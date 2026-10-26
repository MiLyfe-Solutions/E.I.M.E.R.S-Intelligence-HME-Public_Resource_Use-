import V185TrunkScan21Chunk118

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1447155 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 3]
def baseStart_1447155 : Nat := 118140960795 + 1447155 * 2 ^ 59
def prefixEnd_1447155 : Nat := 4983230072969 + 3 ^ 40 * 1447155 * 2
def baseEnd_1447155 : Nat := 330260487358840325825405

theorem tailTrace_1447155 : CollatzResearch.WordTrace tailWord_1447155 prefixEnd_1447155 330260487358840325825405 := by
  unfold tailWord_1447155
  simp only [CollatzResearch.WordTrace]
  refine ⟨52782079072212064242142919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35188052714808042828095279 52782079072212064242142919)
  ·
    refine ⟨79173118608318096363214379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52782079072212064242142919 79173118608318096363214379)
    ·
      refine ⟨118759677912477144544821569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79173118608318096363214379 118759677912477144544821569)
      ·
        refine ⟨89069758434357858408616177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118759677912477144544821569 89069758434357858408616177)
        ·
          refine ⟨66802318825768393806462133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89069758434357858408616177 66802318825768393806462133)
          ·
            refine ⟨6262717389915786919355825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66802318825768393806462133 6262717389915786919355825)
            ·
              refine ⟨4697038042436840189516869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6262717389915786919355825 4697038042436840189516869)
              ·
                refine ⟨880694632956907535534413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4697038042436840189516869 880694632956907535534413)
                ·
                  refine ⟨330260487358840325825405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880694632956907535534413 330260487358840325825405)
                  ·
                    rfl

theorem cell21_1447155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 3].length) (baseStart_1447155 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447155 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447155 prefixEnd_1447155 := by exact prefixLift 1447155
  have htrace : WordTrace (prefixWord ++ tailWord_1447155) baseStart_1447155 baseEnd_1447155 := by
    simpa [prefixWord, tailWord_1447155, baseEnd_1447155] using wordTrace_append hprefix tailTrace_1447155
  have hstable : (prefixWord ++ tailWord_1447155).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447155).length < 2 ^ (prefixWord ++ tailWord_1447155).sum := by decide
  have hdescent : baseEnd_1447155 < baseStart_1447155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447200 : List Nat := [2, 1, 1, 5, 3, 2, 7]
def baseStart_1447200 : Nat := 118140960795 + 1447200 * 2 ^ 59
def prefixEnd_1447200 : Nat := 4983230072969 + 3 ^ 40 * 1447200 * 2
def baseEnd_1447200 : Nat := 36696750774658916397257

theorem tailTrace_1447200 : CollatzResearch.WordTrace tailWord_1447200 prefixEnd_1447200 36696750774658916397257 := by
  unfold tailWord_1447200
  simp only [CollatzResearch.WordTrace]
  refine ⟨26391860178524518463765527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35189146904699357951687369 26391860178524518463765527)
  ·
    refine ⟨39587790267786777695648291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26391860178524518463765527 39587790267786777695648291)
    ·
      refine ⟨59381685401680166543472437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39587790267786777695648291 59381685401680166543472437)
      ·
        refine ⟨5567033006407515613450541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59381685401680166543472437 5567033006407515613450541)
        ·
          refine ⟨2087637377402818355043953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5567033006407515613450541 2087637377402818355043953)
          ·
            refine ⟨1565728033052113766282965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2087637377402818355043953 1565728033052113766282965)
            ·
              refine ⟨36696750774658916397257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1565728033052113766282965 36696750774658916397257)
              ·
                rfl

theorem cell21_1447200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 7].length) (baseStart_1447200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447200 prefixEnd_1447200 := by exact prefixLift 1447200
  have htrace : WordTrace (prefixWord ++ tailWord_1447200) baseStart_1447200 baseEnd_1447200 := by
    simpa [prefixWord, tailWord_1447200, baseEnd_1447200] using wordTrace_append hprefix tailTrace_1447200
  have hstable : (prefixWord ++ tailWord_1447200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447200).length < 2 ^ (prefixWord ++ tailWord_1447200).sum := by decide
  have hdescent : baseEnd_1447200 < baseStart_1447200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447276 : List Nat := [2, 2, 1, 1, 5, 3, 1, 6]
def baseStart_1447276 : Nat := 118140960795 + 1447276 * 2 ^ 59
def prefixEnd_1447276 : Nat := 4983230072969 + 3 ^ 40 * 1447276 * 2
def baseEnd_1447276 : Nat := 110096033735790334769497

theorem tailTrace_1447276 : CollatzResearch.WordTrace tailWord_1447276 prefixEnd_1447276 110096033735790334769497 := by
  unfold tailWord_1447276
  simp only [CollatzResearch.WordTrace]
  refine ⟨26393246152386850953648841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35190994869849134604865121 26393246152386850953648841)
  ·
    refine ⟨19794934614290138215236631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26393246152386850953648841 19794934614290138215236631)
    ·
      refine ⟨29692401921435207322854947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19794934614290138215236631 29692401921435207322854947)
      ·
        refine ⟨44538602882152810984282421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29692401921435207322854947 44538602882152810984282421)
        ·
          refine ⟨4175494020201826029776477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44538602882152810984282421 4175494020201826029776477)
          ·
            refine ⟨1565810257575684761166179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4175494020201826029776477 1565810257575684761166179)
            ·
              refine ⟨2348715386363527141749269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1565810257575684761166179 2348715386363527141749269)
              ·
                refine ⟨110096033735790334769497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2348715386363527141749269 110096033735790334769497)
                ·
                  rfl

theorem cell21_1447276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_1447276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447276 prefixEnd_1447276 := by exact prefixLift 1447276
  have htrace : WordTrace (prefixWord ++ tailWord_1447276) baseStart_1447276 baseEnd_1447276 := by
    simpa [prefixWord, tailWord_1447276, baseEnd_1447276] using wordTrace_append hprefix tailTrace_1447276
  have hstable : (prefixWord ++ tailWord_1447276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447276).length < 2 ^ (prefixWord ++ tailWord_1447276).sum := by decide
  have hdescent : baseEnd_1447276 < baseStart_1447276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447307 : List Nat := [1, 1, 1, 1, 4, 3, 4, 3, 3]
def baseStart_1447307 : Nat := 118140960795 + 1447307 * 2 ^ 59
def prefixEnd_1447307 : Nat := 4983230072969 + 3 ^ 40 * 1447307 * 2
def baseEnd_1447307 : Nat := 330295175829721839291761

theorem tailTrace_1447307 : CollatzResearch.WordTrace tailWord_1447307 prefixEnd_1447307 330295175829721839291761 := by
  unfold tailWord_1447307
  simp only [CollatzResearch.WordTrace]
  refine ⟨52787622967661394201676175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35191748645107596134450783 52787622967661394201676175)
  ·
    refine ⟨79181434451492091302514263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52787622967661394201676175 79181434451492091302514263)
    ·
      refine ⟨118772151677238136953771395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79181434451492091302514263 118772151677238136953771395)
      ·
        refine ⟨178158227515857205430657093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118772151677238136953771395 178158227515857205430657093)
        ·
          refine ⟨33404667659223226018248205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178158227515857205430657093 33404667659223226018248205)
          ·
            refine ⟨12526750372208709756843077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33404667659223226018248205 12526750372208709756843077)
            ·
              refine ⟨2348765694789133079408077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12526750372208709756843077 2348765694789133079408077)
              ·
                refine ⟨880787135545924904778029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2348765694789133079408077 880787135545924904778029)
                ·
                  refine ⟨330295175829721839291761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880787135545924904778029 330295175829721839291761)
                  ·
                    rfl

theorem cell21_1447307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 4, 3, 3].length) (baseStart_1447307 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447307 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447307 prefixEnd_1447307 := by exact prefixLift 1447307
  have htrace : WordTrace (prefixWord ++ tailWord_1447307) baseStart_1447307 baseEnd_1447307 := by
    simpa [prefixWord, tailWord_1447307, baseEnd_1447307] using wordTrace_append hprefix tailTrace_1447307
  have hstable : (prefixWord ++ tailWord_1447307).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447307).length < 2 ^ (prefixWord ++ tailWord_1447307).sum := by decide
  have hdescent : baseEnd_1447307 < baseStart_1447307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447321 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 4]
def baseStart_1447321 : Nat := 118140960795 + 1447321 * 2 ^ 59
def prefixEnd_1447321 : Nat := 4983230072969 + 3 ^ 40 * 1447321 * 2
def baseEnd_1447321 : Nat := 330298370820460926058399

theorem tailTrace_1447321 : CollatzResearch.WordTrace tailWord_1447321 prefixEnd_1447321 330298370820460926058399 := by
  unfold tailWord_1447321
  simp only [CollatzResearch.WordTrace]
  refine ⟨52788133589610674592685817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35192089059740449728457211 52788133589610674592685817)
  ·
    refine ⟨39591100192208005944514363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52788133589610674592685817 39591100192208005944514363)
    ·
      refine ⟨59386650288312008916771545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39591100192208005944514363 59386650288312008916771545)
      ·
        refine ⟨44539987716234006687578659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59386650288312008916771545 44539987716234006687578659)
        ·
          refine ⟨66809981574351010031367989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44539987716234006687578659 66809981574351010031367989)
          ·
            refine ⟨6263435772595407190440749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66809981574351010031367989 6263435772595407190440749)
            ·
              refine ⟨2348788414723277696415281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6263435772595407190440749 2348788414723277696415281)
              ·
                refine ⟨1761591311042458272311461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2348788414723277696415281 1761591311042458272311461)
                ·
                  refine ⟨330298370820460926058399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761591311042458272311461 330298370820460926058399)
                  ·
                    rfl

theorem cell21_1447321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_1447321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447321 prefixEnd_1447321 := by exact prefixLift 1447321
  have htrace : WordTrace (prefixWord ++ tailWord_1447321) baseStart_1447321 baseEnd_1447321 := by
    simpa [prefixWord, tailWord_1447321, baseEnd_1447321] using wordTrace_append hprefix tailTrace_1447321
  have hstable : (prefixWord ++ tailWord_1447321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447321).length < 2 ^ (prefixWord ++ tailWord_1447321).sum := by decide
  have hdescent : baseEnd_1447321 < baseStart_1447321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447324 : List Nat := [2, 2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_1447324 : Nat := 118140960795 + 1447324 * 2 ^ 59
def prefixEnd_1447324 : Nat := 4983230072969 + 3 ^ 40 * 1447324 * 2
def baseEnd_1447324 : Nat := 330299055461333587508393

theorem tailTrace_1447324 : CollatzResearch.WordTrace tailWord_1447324 prefixEnd_1447324 330299055461333587508393 := by
  unfold tailWord_1447324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26394121504299903052522513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35192162005733204070030017 26394121504299903052522513)
  ·
    refine ⟨19795591128224927289391885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26394121504299903052522513 19795591128224927289391885)
    ·
      refine ⟨7423346673084347733521957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19795591128224927289391885 7423346673084347733521957)
      ·
        refine ⟨1391877501203315200035367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7423346673084347733521957 1391877501203315200035367)
        ·
          refine ⟨2087816251804972800053051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1391877501203315200035367 2087816251804972800053051)
          ·
            refine ⟨3131724377707459200079577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2087816251804972800053051 3131724377707459200079577)
            ·
              refine ⟨2348793283280594400059683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3131724377707459200079577 2348793283280594400059683)
              ·
                refine ⟨3523189924920891600089525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2348793283280594400059683 3523189924920891600089525)
                ·
                  refine ⟨330299055461333587508393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3523189924920891600089525 330299055461333587508393)
                  ·
                    rfl

theorem cell21_1447324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_1447324 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447324 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447324 prefixEnd_1447324 := by exact prefixLift 1447324
  have htrace : WordTrace (prefixWord ++ tailWord_1447324) baseStart_1447324 baseEnd_1447324 := by
    simpa [prefixWord, tailWord_1447324, baseEnd_1447324] using wordTrace_append hprefix tailTrace_1447324
  have hstable : (prefixWord ++ tailWord_1447324).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447324).length < 2 ^ (prefixWord ++ tailWord_1447324).sum := by decide
  have hdescent : baseEnd_1447324 < baseStart_1447324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447335 : List Nat := [1, 1, 6, 1, 1, 1, 2, 8]
def baseStart_1447335 : Nat := 118140960795 + 1447335 * 2 ^ 59
def prefixEnd_1447335 : Nat := 4983230072969 + 3 ^ 40 * 1447335 * 2
def baseEnd_1447335 : Nat := 110100521937066670941679

theorem tailTrace_1447335 : CollatzResearch.WordTrace tailWord_1447335 prefixEnd_1447335 110100521937066670941679 := by
  unfold tailWord_1447335
  simp only [CollatzResearch.WordTrace]
  refine ⟨52788644211559954983695459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35192429474373303322463639 52788644211559954983695459)
  ·
    refine ⟨79182966317339932475543189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52788644211559954983695459 79182966317339932475543189)
    ·
      refine ⟨3711701546125309334791087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79182966317339932475543189 3711701546125309334791087)
      ·
        refine ⟨5567552319187964002186631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3711701546125309334791087 5567552319187964002186631)
        ·
          refine ⟨8351328478781946003279947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5567552319187964002186631 8351328478781946003279947)
          ·
            refine ⟨12526992718172919004919921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8351328478781946003279947 12526992718172919004919921)
            ·
              refine ⟨9395244538629689253689941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12526992718172919004919921 9395244538629689253689941)
              ·
                refine ⟨110100521937066670941679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9395244538629689253689941 110100521937066670941679)
                ·
                  rfl

theorem cell21_1447335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 8].length) (baseStart_1447335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447335 prefixEnd_1447335 := by exact prefixLift 1447335
  have htrace : WordTrace (prefixWord ++ tailWord_1447335) baseStart_1447335 baseEnd_1447335 := by
    simpa [prefixWord, tailWord_1447335, baseEnd_1447335] using wordTrace_append hprefix tailTrace_1447335
  have hstable : (prefixWord ++ tailWord_1447335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447335).length < 2 ^ (prefixWord ++ tailWord_1447335).sum := by decide
  have hdescent : baseEnd_1447335 < baseStart_1447335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447428 : List Nat := [2, 3, 2, 3, 3, 8]
def baseStart_1447428 : Nat := 118140960795 + 1447428 * 2 ^ 59
def prefixEnd_1447428 : Nat := 4983230072969 + 3 ^ 40 * 1447428 * 2
def baseEnd_1447428 : Nat := 12234177395490833991661

theorem tailTrace_1447428 : CollatzResearch.WordTrace tailWord_1447428 prefixEnd_1447428 12234177395490833991661 := by
  unfold tailWord_1447428
  simp only [CollatzResearch.WordTrace]
  refine ⟨26396018100111515933415469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35194690800148687911220625 26396018100111515933415469)
  ·
    refine ⟨9898506787541818475030801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26396018100111515933415469 9898506787541818475030801)
    ·
      refine ⟨7423880090656363856273101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9898506787541818475030801 7423880090656363856273101)
      ·
        refine ⟨2783955033996136446102413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7423880090656363856273101 2783955033996136446102413)
        ·
          refine ⟨1043983137748551167288405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2783955033996136446102413 1043983137748551167288405)
          ·
            refine ⟨12234177395490833991661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1043983137748551167288405 12234177395490833991661)
            ·
              rfl

theorem cell21_1447428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 8].length) (baseStart_1447428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447428 prefixEnd_1447428 := by exact prefixLift 1447428
  have htrace : WordTrace (prefixWord ++ tailWord_1447428) baseStart_1447428 baseEnd_1447428 := by
    simpa [prefixWord, tailWord_1447428, baseEnd_1447428] using wordTrace_append hprefix tailTrace_1447428
  have hstable : (prefixWord ++ tailWord_1447428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447428).length < 2 ^ (prefixWord ++ tailWord_1447428).sum := by decide
  have hdescent : baseEnd_1447428 < baseStart_1447428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447566 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1447566 : Nat := 118140960795 + 1447566 * 2 ^ 59
def prefixEnd_1447566 : Nat := 4983230072969 + 3 ^ 40 * 1447566 * 2
def baseEnd_1447566 : Nat := 330354283158394944474565

theorem tailTrace_1447566 : CollatzResearch.WordTrace tailWord_1447566 prefixEnd_1447566 330354283158394944474565 := by
  unfold tailWord_1447566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6599633684215385179419319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35198046315815387623569701 6599633684215385179419319)
  ·
    refine ⟨9899450526323077769128979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6599633684215385179419319 9899450526323077769128979)
    ·
      refine ⟨14849175789484616653693469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9899450526323077769128979 14849175789484616653693469)
      ·
        refine ⟨5568440921056731245135051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14849175789484616653693469 5568440921056731245135051)
        ·
          refine ⟨8352661381585096867702577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568440921056731245135051 8352661381585096867702577)
          ·
            refine ⟨6264496036188822650776933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8352661381585096867702577 6264496036188822650776933)
            ·
              refine ⟨1174593006785404247020675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6264496036188822650776933 1174593006785404247020675)
              ·
                refine ⟨1761889510178106370531013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174593006785404247020675 1761889510178106370531013)
                ·
                  refine ⟨330354283158394944474565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1761889510178106370531013 330354283158394944474565)
                  ·
                    rfl

theorem cell21_1447566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1447566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447566 prefixEnd_1447566 := by exact prefixLift 1447566
  have htrace : WordTrace (prefixWord ++ tailWord_1447566) baseStart_1447566 baseEnd_1447566 := by
    simpa [prefixWord, tailWord_1447566, baseEnd_1447566] using wordTrace_append hprefix tailTrace_1447566
  have hstable : (prefixWord ++ tailWord_1447566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447566).length < 2 ^ (prefixWord ++ tailWord_1447566).sum := by decide
  have hdescent : baseEnd_1447566 < baseStart_1447566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447639 : List Nat := [1, 1, 3, 2, 1, 3, 5, 5]
def baseStart_1447639 : Nat := 118140960795 + 1447639 * 2 ^ 59
def prefixEnd_1447639 : Nat := 4983230072969 + 3 ^ 40 * 1447639 * 2
def baseEnd_1447639 : Nat := 110123647584321013252583

theorem tailTrace_1447639 : CollatzResearch.WordTrace tailWord_1447639 prefixEnd_1447639 110123647584321013252583 := by
  unfold tailWord_1447639
  simp only [CollatzResearch.WordTrace]
  refine ⟨52799732002458614902761971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35199821334972409935174647 52799732002458614902761971)
  ·
    refine ⟨79199598003687922354142957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52799732002458614902761971 79199598003687922354142957)
    ·
      refine ⟨29699849251382970882803609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79199598003687922354142957 29699849251382970882803609)
      ·
        refine ⟨22274886938537228162102707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29699849251382970882803609 22274886938537228162102707)
        ·
          refine ⟨33412330407805842243154061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22274886938537228162102707 33412330407805842243154061)
          ·
            refine ⟨12529623902927190841182773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33412330407805842243154061 12529623902927190841182773)
            ·
              refine ⟨1174652240899424141360885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12529623902927190841182773 1174652240899424141360885)
              ·
                refine ⟨110123647584321013252583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1174652240899424141360885 110123647584321013252583)
                ·
                  rfl

theorem cell21_1447639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 5].length) (baseStart_1447639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447639 prefixEnd_1447639 := by exact prefixLift 1447639
  have htrace : WordTrace (prefixWord ++ tailWord_1447639) baseStart_1447639 baseEnd_1447639 := by
    simpa [prefixWord, tailWord_1447639, baseEnd_1447639] using wordTrace_append hprefix tailTrace_1447639
  have hstable : (prefixWord ++ tailWord_1447639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447639).length < 2 ^ (prefixWord ++ tailWord_1447639).sum := by decide
  have hdescent : baseEnd_1447639 < baseStart_1447639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447645 : List Nat := [1, 4, 3, 3, 1, 1, 2, 3, 3]
def baseStart_1447645 : Nat := 118140960795 + 1447645 * 2 ^ 59
def prefixEnd_1447645 : Nat := 4983230072969 + 3 ^ 40 * 1447645 * 2
def baseEnd_1447645 : Nat := 330372312034708362657737

theorem tailTrace_1447645 : CollatzResearch.WordTrace tailWord_1447645 prefixEnd_1447645 330372312034708362657737 := by
  unfold tailWord_1447645
  simp only [CollatzResearch.WordTrace]
  refine ⟨52799950840436877927480389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35199967226957918618320259 52799950840436877927480389)
  ·
    refine ⟨9899990782581914611402573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52799950840436877927480389 9899990782581914611402573)
    ·
      refine ⟨3712496543468217979275965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9899990782581914611402573 3712496543468217979275965)
      ·
        refine ⟨1392186203800581742228487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3712496543468217979275965 1392186203800581742228487)
        ·
          refine ⟨2088279305700872613342731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392186203800581742228487 2088279305700872613342731)
          ·
            refine ⟨3132418958551308920014097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088279305700872613342731 3132418958551308920014097)
            ·
              refine ⟨2349314218913481690010573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132418958551308920014097 2349314218913481690010573)
              ·
                refine ⟨880992832092555633753965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2349314218913481690010573 880992832092555633753965)
                ·
                  refine ⟨330372312034708362657737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880992832092555633753965 330372312034708362657737)
                  ·
                    rfl

theorem cell21_1447645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 2, 3, 3].length) (baseStart_1447645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447645 prefixEnd_1447645 := by exact prefixLift 1447645
  have htrace : WordTrace (prefixWord ++ tailWord_1447645) baseStart_1447645 baseEnd_1447645 := by
    simpa [prefixWord, tailWord_1447645, baseEnd_1447645] using wordTrace_append hprefix tailTrace_1447645
  have hstable : (prefixWord ++ tailWord_1447645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447645).length < 2 ^ (prefixWord ++ tailWord_1447645).sum := by decide
  have hdescent : baseEnd_1447645 < baseStart_1447645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447653 : List Nat := [1, 3, 1, 4, 1, 1, 1, 2, 7]
def baseStart_1447653 : Nat := 118140960795 + 1447653 * 2 ^ 59
def prefixEnd_1447653 : Nat := 4983230072969 + 3 ^ 40 * 1447653 * 2
def baseEnd_1447653 : Nat := 330374137743702126524387

theorem tailTrace_1447653 : CollatzResearch.WordTrace tailWord_1447653 prefixEnd_1447653 330374137743702126524387 := by
  unfold tailWord_1447653
  simp only [CollatzResearch.WordTrace]
  refine ⟨52800242624407895293771613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35200161749605263529181075 52800242624407895293771613)
  ·
    refine ⟨19800090984152960735164355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52800242624407895293771613 19800090984152960735164355)
    ·
      refine ⟨29700136476229441102746533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19800090984152960735164355 29700136476229441102746533)
      ·
        refine ⟨5568775589293020206764975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29700136476229441102746533 5568775589293020206764975)
        ·
          refine ⟨8353163383939530310147463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5568775589293020206764975 8353163383939530310147463)
          ·
            refine ⟨12529745075909295465221195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8353163383939530310147463 12529745075909295465221195)
            ·
              refine ⟨18794617613863943197831793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12529745075909295465221195 18794617613863943197831793)
              ·
                refine ⟨14095963210397957398373845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18794617613863943197831793 14095963210397957398373845)
                ·
                  refine ⟨330374137743702126524387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14095963210397957398373845 330374137743702126524387)
                  ·
                    rfl

theorem cell21_1447653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_1447653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447653 prefixEnd_1447653 := by exact prefixLift 1447653
  have htrace : WordTrace (prefixWord ++ tailWord_1447653) baseStart_1447653 baseEnd_1447653 := by
    simpa [prefixWord, tailWord_1447653, baseEnd_1447653] using wordTrace_append hprefix tailTrace_1447653
  have hstable : (prefixWord ++ tailWord_1447653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447653).length < 2 ^ (prefixWord ++ tailWord_1447653).sum := by decide
  have hdescent : baseEnd_1447653 < baseStart_1447653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447670 : List Nat := [5, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1447670 : Nat := 118140960795 + 1447670 * 2 ^ 59
def prefixEnd_1447670 : Nat := 4983230072969 + 3 ^ 40 * 1447670 * 2
def baseEnd_1447670 : Nat := 330378017375313874741019

theorem tailTrace_1447670 : CollatzResearch.WordTrace tailWord_1447670 prefixEnd_1447670 330378017375313874741019 := by
  unfold tailWord_1447670
  simp only [CollatzResearch.WordTrace]
  refine ⟨3300053916584144199821279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35200575110230871464760309 3300053916584144199821279)
  ·
    refine ⟨4950080874876216299731919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3300053916584144199821279 4950080874876216299731919)
    ·
      refine ⟨7425121312314324449597879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4950080874876216299731919 7425121312314324449597879)
      ·
        refine ⟨11137681968471486674396819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7425121312314324449597879 11137681968471486674396819)
        ·
          refine ⟨16706522952707230011595229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11137681968471486674396819 16706522952707230011595229)
          ·
            refine ⟨6264946107265211254348211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16706522952707230011595229 6264946107265211254348211)
            ·
              refine ⟨9397419160897816881522317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6264946107265211254348211 9397419160897816881522317)
              ·
                refine ⟨3524032185336681330570869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9397419160897816881522317 3524032185336681330570869)
                ·
                  refine ⟨330378017375313874741019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3524032185336681330570869 330378017375313874741019)
                  ·
                    rfl

theorem cell21_1447670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1447670 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447670 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447670 prefixEnd_1447670 := by exact prefixLift 1447670
  have htrace : WordTrace (prefixWord ++ tailWord_1447670) baseStart_1447670 baseEnd_1447670 := by
    simpa [prefixWord, tailWord_1447670, baseEnd_1447670] using wordTrace_append hprefix tailTrace_1447670
  have hstable : (prefixWord ++ tailWord_1447670).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447670).length < 2 ^ (prefixWord ++ tailWord_1447670).sum := by decide
  have hdescent : baseEnd_1447670 < baseStart_1447670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447732 : List Nat := [2, 5, 1, 1, 2, 2, 2, 6]
def baseStart_1447732 : Nat := 118140960795 + 1447732 * 2 ^ 59
def prefixEnd_1447732 : Nat := 4983230072969 + 3 ^ 40 * 1447732 * 2
def baseEnd_1447732 : Nat := 110130722206671848235853

theorem tailTrace_1447732 : CollatzResearch.WordTrace tailWord_1447732 prefixEnd_1447732 110130722206671848235853 := by
  unfold tailWord_1447732
  simp only [CollatzResearch.WordTrace]
  refine ⟨26401561995560845892948725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35202082660747794523931633 26401561995560845892948725)
  ·
    refine ⟨2475146437083829302463943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26401561995560845892948725 2475146437083829302463943)
    ·
      refine ⟨3712719655625743953695915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2475146437083829302463943 3712719655625743953695915)
      ·
        refine ⟨5569079483438615930543873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3712719655625743953695915 5569079483438615930543873)
        ·
          refine ⟨4176809612578961947907905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5569079483438615930543873 4176809612578961947907905)
          ·
            refine ⟨3132607209434221460930929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4176809612578961947907905 3132607209434221460930929)
            ·
              refine ⟨2349455407075666095698197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132607209434221460930929 2349455407075666095698197)
              ·
                refine ⟨110130722206671848235853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2349455407075666095698197 110130722206671848235853)
                ·
                  rfl

theorem cell21_1447732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_1447732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447732 prefixEnd_1447732 := by exact prefixLift 1447732
  have htrace : WordTrace (prefixWord ++ tailWord_1447732) baseStart_1447732 baseEnd_1447732 := by
    simpa [prefixWord, tailWord_1447732, baseEnd_1447732] using wordTrace_append hprefix tailTrace_1447732
  have hstable : (prefixWord ++ tailWord_1447732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447732).length < 2 ^ (prefixWord ++ tailWord_1447732).sum := by decide
  have hdescent : baseEnd_1447732 < baseStart_1447732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447819 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 6]
def baseStart_1447819 : Nat := 118140960795 + 1447819 * 2 ^ 59
def prefixEnd_1447819 : Nat := 4983230072969 + 3 ^ 40 * 1447819 * 2
def baseEnd_1447819 : Nat := 330412021205322726757381

theorem tailTrace_1447819 : CollatzResearch.WordTrace tailWord_1447819 prefixEnd_1447819 330412021205322726757381 := by
  unfold tailWord_1447819
  simp only [CollatzResearch.WordTrace]
  refine ⟨52806297141806505644314511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35204198094537670429543007 52806297141806505644314511)
  ·
    refine ⟨79209445712709758466471767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52806297141806505644314511 79209445712709758466471767)
    ·
      refine ⟨118814168569064637699707651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79209445712709758466471767 118814168569064637699707651)
      ·
        refine ⟨178221252853596956549561477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118814168569064637699707651 178221252853596956549561477)
        ·
          refine ⟨33416484910049429353042777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 178221252853596956549561477 33416484910049429353042777)
          ·
            refine ⟨25062363682537072014782083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33416484910049429353042777 25062363682537072014782083)
            ·
              refine ⟨37593545523805608022173125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25062363682537072014782083 37593545523805608022173125)
              ·
                refine ⟨7048789785713551504157461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37593545523805608022173125 7048789785713551504157461)
                ·
                  refine ⟨330412021205322726757381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7048789785713551504157461 330412021205322726757381)
                  ·
                    rfl

theorem cell21_1447819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_1447819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447819 prefixEnd_1447819 := by exact prefixLift 1447819
  have htrace : WordTrace (prefixWord ++ tailWord_1447819) baseStart_1447819 baseEnd_1447819 := by
    simpa [prefixWord, tailWord_1447819, baseEnd_1447819] using wordTrace_append hprefix tailTrace_1447819
  have hstable : (prefixWord ++ tailWord_1447819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447819).length < 2 ^ (prefixWord ++ tailWord_1447819).sum := by decide
  have hdescent : baseEnd_1447819 < baseStart_1447819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1447895 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 6]
def baseStart_1447895 : Nat := 118140960795 + 1447895 * 2 ^ 59
def prefixEnd_1447895 : Nat := 4983230072969 + 3 ^ 40 * 1447895 * 2
def baseEnd_1447895 : Nat := 330429365440763483490559

theorem tailTrace_1447895 : CollatzResearch.WordTrace tailWord_1447895 prefixEnd_1447895 330429365440763483490559 := by
  unfold tailWord_1447895
  simp only [CollatzResearch.WordTrace]
  refine ⟨52809069089531170624081139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35206046059687447082720759 52809069089531170624081139)
  ·
    refine ⟨79213603634296755936121709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52809069089531170624081139 79213603634296755936121709)
    ·
      refine ⟨29705101362861283476045641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79213603634296755936121709 29705101362861283476045641)
      ·
        refine ⟨22278826022145962607034231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29705101362861283476045641 22278826022145962607034231)
        ·
          refine ⟨33418239033218943910551347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22278826022145962607034231 33418239033218943910551347)
          ·
            refine ⟨50127358549828415865827021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33418239033218943910551347 50127358549828415865827021)
            ·
              refine ⟨18797759456185655949685133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50127358549828415865827021 18797759456185655949685133)
              ·
                refine ⟨7049159796069620981131925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18797759456185655949685133 7049159796069620981131925)
                ·
                  refine ⟨330429365440763483490559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7049159796069620981131925 330429365440763483490559)
                  ·
                    rfl

theorem cell21_1447895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_1447895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1447895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1447895 prefixEnd_1447895 := by exact prefixLift 1447895
  have htrace : WordTrace (prefixWord ++ tailWord_1447895) baseStart_1447895 baseEnd_1447895 := by
    simpa [prefixWord, tailWord_1447895, baseEnd_1447895] using wordTrace_append hprefix tailTrace_1447895
  have hstable : (prefixWord ++ tailWord_1447895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1447895).length < 2 ^ (prefixWord ++ tailWord_1447895).sum := by decide
  have hdescent : baseEnd_1447895 < baseStart_1447895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1447895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448047 : List Nat := [1, 1, 2, 1, 3, 4, 1, 2, 6]
def baseStart_1448047 : Nat := 118140960795 + 1448047 * 2 ^ 59
def prefixEnd_1448047 : Nat := 4983230072969 + 3 ^ 40 * 1448047 * 2
def baseEnd_1448047 : Nat := 330464053911644996956915

theorem tailTrace_1448047 : CollatzResearch.WordTrace tailWord_1448047 prefixEnd_1448047 330464053911644996956915 := by
  unfold tailWord_1448047
  simp only [CollatzResearch.WordTrace]
  refine ⟨52814612984980500583614395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35209741989987000389076263 52814612984980500583614395)
  ·
    refine ⟨79221919477470750875421593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52814612984980500583614395 79221919477470750875421593)
    ·
      refine ⟨59416439608103063156566195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79221919477470750875421593 59416439608103063156566195)
      ·
        refine ⟨89124659412154594734849293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59416439608103063156566195 89124659412154594734849293)
        ·
          refine ⟨33421747279557973025568485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89124659412154594734849293 33421747279557973025568485)
          ·
            refine ⟨6266577614917119942294091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33421747279557973025568485 6266577614917119942294091)
            ·
              refine ⟨9399866422375679913441137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6266577614917119942294091 9399866422375679913441137)
              ·
                refine ⟨7049899816781759935080853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9399866422375679913441137 7049899816781759935080853)
                ·
                  refine ⟨330464053911644996956915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7049899816781759935080853 330464053911644996956915)
                  ·
                    rfl

theorem cell21_1448047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_1448047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448047 prefixEnd_1448047 := by exact prefixLift 1448047
  have htrace : WordTrace (prefixWord ++ tailWord_1448047) baseStart_1448047 baseEnd_1448047 := by
    simpa [prefixWord, tailWord_1448047, baseEnd_1448047] using wordTrace_append hprefix tailTrace_1448047
  have hstable : (prefixWord ++ tailWord_1448047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448047).length < 2 ^ (prefixWord ++ tailWord_1448047).sum := by decide
  have hdescent : baseEnd_1448047 < baseStart_1448047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448067 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 3]
def baseStart_1448067 : Nat := 118140960795 + 1448067 * 2 ^ 59
def prefixEnd_1448067 : Nat := 4983230072969 + 3 ^ 40 * 1448067 * 2
def baseEnd_1448067 : Nat := 330468618184129406623541

theorem tailTrace_1448067 : CollatzResearch.WordTrace tailWord_1448067 prefixEnd_1448067 330468618184129406623541 := by
  unfold tailWord_1448067
  simp only [CollatzResearch.WordTrace]
  refine ⟨52815342444908043999342455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35210228296605362666228303 52815342444908043999342455)
  ·
    refine ⟨79223013667362065999013683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52815342444908043999342455 79223013667362065999013683)
    ·
      refine ⟨118834520501043098998520525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79223013667362065999013683 118834520501043098998520525)
      ·
        refine ⟨44562945187891162124445197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118834520501043098998520525 44562945187891162124445197)
        ·
          refine ⟨16711104445459185796666949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44562945187891162124445197 16711104445459185796666949)
          ·
            refine ⟨3133332083523597336875053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16711104445459185796666949 3133332083523597336875053)
            ·
              refine ⟨1174999531321349001328145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3133332083523597336875053 1174999531321349001328145)
              ·
                refine ⟨881249648491011750996109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1174999531321349001328145 881249648491011750996109)
                ·
                  refine ⟨330468618184129406623541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881249648491011750996109 330468618184129406623541)
                  ·
                    rfl

theorem cell21_1448067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 3].length) (baseStart_1448067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448067 prefixEnd_1448067 := by exact prefixLift 1448067
  have htrace : WordTrace (prefixWord ++ tailWord_1448067) baseStart_1448067 baseEnd_1448067 := by
    simpa [prefixWord, tailWord_1448067, baseEnd_1448067] using wordTrace_append hprefix tailTrace_1448067
  have hstable : (prefixWord ++ tailWord_1448067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448067).length < 2 ^ (prefixWord ++ tailWord_1448067).sum := by decide
  have hdescent : baseEnd_1448067 < baseStart_1448067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448129 : List Nat := [1, 2, 6, 1, 3, 1, 1, 6]
def baseStart_1448129 : Nat := 118140960795 + 1448129 * 2 ^ 59
def prefixEnd_1448129 : Nat := 4983230072969 + 3 ^ 40 * 1448129 * 2
def baseEnd_1448129 : Nat := 110160922476277025530027

theorem tailTrace_1448129 : CollatzResearch.WordTrace tailWord_1448129 prefixEnd_1448129 110160922476277025530027 := by
  unfold tailWord_1448129
  simp only [CollatzResearch.WordTrace]
  refine ⟨52817603770683428588099441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35211735847122285725399627 52817603770683428588099441)
  ·
    refine ⟨39613202828012571441074581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52817603770683428588099441 39613202828012571441074581)
    ·
      refine ⟨1856868882563089286300371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 39613202828012571441074581 1856868882563089286300371)
      ·
        refine ⟨2785303323844633929450557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1856868882563089286300371 2785303323844633929450557)
        ·
          refine ⟨1044488746441737723543959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2785303323844633929450557 1044488746441737723543959)
          ·
            refine ⟨1566733119662606585315939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1044488746441737723543959 1566733119662606585315939)
            ·
              refine ⟨2350099679493909877973909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1566733119662606585315939 2350099679493909877973909)
              ·
                refine ⟨110160922476277025530027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2350099679493909877973909 110160922476277025530027)
                ·
                  rfl

theorem cell21_1448129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 6].length) (baseStart_1448129 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448129 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448129 prefixEnd_1448129 := by exact prefixLift 1448129
  have htrace : WordTrace (prefixWord ++ tailWord_1448129) baseStart_1448129 baseEnd_1448129 := by
    simpa [prefixWord, tailWord_1448129, baseEnd_1448129] using wordTrace_append hprefix tailTrace_1448129
  have hstable : (prefixWord ++ tailWord_1448129).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448129).length < 2 ^ (prefixWord ++ tailWord_1448129).sum := by decide
  have hdescent : baseEnd_1448129 < baseStart_1448129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448137 : List Nat := [1, 2, 1, 1, 2, 1, 1, 12]
def baseStart_1448137 : Nat := 118140960795 + 1448137 * 2 ^ 59
def prefixEnd_1448137 : Nat := 4983230072969 + 3 ^ 40 * 1448137 * 2
def baseEnd_1448137 : Nat := 110161531045941613485577

theorem tailTrace_1448137 : CollatzResearch.WordTrace tailWord_1448137 prefixEnd_1448137 110161531045941613485577 := by
  unfold tailWord_1448137
  simp only [CollatzResearch.WordTrace]
  refine ⟨52817895554654445954390665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35211930369769630636260443 52817895554654445954390665)
  ·
    refine ⟨39613421665990834465792999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52817895554654445954390665 39613421665990834465792999)
    ·
      refine ⟨59420132498986251698689499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39613421665990834465792999 59420132498986251698689499)
      ·
        refine ⟨89130198748479377548034249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59420132498986251698689499 89130198748479377548034249)
        ·
          refine ⟨66847649061359533161025687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89130198748479377548034249 66847649061359533161025687)
          ·
            refine ⟨100271473592039299741538531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66847649061359533161025687 100271473592039299741538531)
            ·
              refine ⟨150407210388058949612307797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100271473592039299741538531 150407210388058949612307797)
              ·
                refine ⟨110161531045941613485577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 150407210388058949612307797 110161531045941613485577)
                ·
                  rfl

theorem cell21_1448137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 12].length) (baseStart_1448137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448137 prefixEnd_1448137 := by exact prefixLift 1448137
  have htrace : WordTrace (prefixWord ++ tailWord_1448137) baseStart_1448137 baseEnd_1448137 := by
    simpa [prefixWord, tailWord_1448137, baseEnd_1448137] using wordTrace_append hprefix tailTrace_1448137
  have hstable : (prefixWord ++ tailWord_1448137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448137).length < 2 ^ (prefixWord ++ tailWord_1448137).sum := by decide
  have hdescent : baseEnd_1448137 < baseStart_1448137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448292 : List Nat := [2, 3, 1, 1, 3, 1, 4, 2, 4]
def baseStart_1448292 : Nat := 118140960795 + 1448292 * 2 ^ 59
def prefixEnd_1448292 : Nat := 4983230072969 + 3 ^ 40 * 1448292 * 2
def baseEnd_1448292 : Nat := 330519966249579015373081

theorem tailTrace_1448292 : CollatzResearch.WordTrace tailWord_1448292 prefixEnd_1448292 330519966249579015373081 := by
  unfold tailWord_1448292
  simp only [CollatzResearch.WordTrace]
  refine ⟨26411774434546453713141565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35215699246061938284188753 26411774434546453713141565)
  ·
    refine ⟨9904415412954920142428087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26411774434546453713141565 9904415412954920142428087)
    ·
      refine ⟨14856623119432380213642131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9904415412954920142428087 14856623119432380213642131)
      ·
        refine ⟨22284934679148570320463197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14856623119432380213642131 22284934679148570320463197)
        ·
          refine ⟨8356850504680713870173699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22284934679148570320463197 8356850504680713870173699)
          ·
            refine ⟨12535275757021070805260549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8356850504680713870173699 12535275757021070805260549)
            ·
              refine ⟨2350364204441450775986353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12535275757021070805260549 2350364204441450775986353)
              ·
                refine ⟨1762773153331088081989765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350364204441450775986353 1762773153331088081989765)
                ·
                  refine ⟨330519966249579015373081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1762773153331088081989765 330519966249579015373081)
                  ·
                    rfl

theorem cell21_1448292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_1448292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448292 prefixEnd_1448292 := by exact prefixLift 1448292
  have htrace : WordTrace (prefixWord ++ tailWord_1448292) baseStart_1448292 baseEnd_1448292 := by
    simpa [prefixWord, tailWord_1448292, baseEnd_1448292] using wordTrace_append hprefix tailTrace_1448292
  have hstable : (prefixWord ++ tailWord_1448292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448292).length < 2 ^ (prefixWord ++ tailWord_1448292).sum := by decide
  have hdescent : baseEnd_1448292 < baseStart_1448292 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448295 : List Nat := [1, 1, 5, 1, 3, 1, 4, 2, 3]
def baseStart_1448295 : Nat := 118140960795 + 1448295 * 2 ^ 59
def prefixEnd_1448295 : Nat := 4983230072969 + 3 ^ 40 * 1448295 * 2
def baseEnd_1448295 : Nat := 330520650890451676823075

theorem tailTrace_1448295 : CollatzResearch.WordTrace tailWord_1448295 prefixEnd_1448295 330520650890451676823075 := by
  unfold tailWord_1448295
  simp only [CollatzResearch.WordTrace]
  refine ⟨52823658288082038938642339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35215772192054692625761559 52823658288082038938642339)
  ·
    refine ⟨79235487432123058407963509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52823658288082038938642339 79235487432123058407963509)
    ·
      refine ⟨7428326946761536725746579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79235487432123058407963509 7428326946761536725746579)
      ·
        refine ⟨11142490420142305088619869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7428326946761536725746579 11142490420142305088619869)
        ·
          refine ⟨4178433907553364408232451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11142490420142305088619869 4178433907553364408232451)
          ·
            refine ⟨6267650861330046612348677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4178433907553364408232451 6267650861330046612348677)
            ·
              refine ⟨1175184536499383739815377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6267650861330046612348677 1175184536499383739815377)
              ·
                refine ⟨881388402374537804861533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175184536499383739815377 881388402374537804861533)
                ·
                  refine ⟨330520650890451676823075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881388402374537804861533 330520650890451676823075)
                  ·
                    rfl

theorem cell21_1448295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 4, 2, 3].length) (baseStart_1448295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448295 prefixEnd_1448295 := by exact prefixLift 1448295
  have htrace : WordTrace (prefixWord ++ tailWord_1448295) baseStart_1448295 baseEnd_1448295 := by
    simpa [prefixWord, tailWord_1448295, baseEnd_1448295] using wordTrace_append hprefix tailTrace_1448295
  have hstable : (prefixWord ++ tailWord_1448295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448295).length < 2 ^ (prefixWord ++ tailWord_1448295).sum := by decide
  have hdescent : baseEnd_1448295 < baseStart_1448295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448306 : List Nat := [3, 2, 1, 2, 1, 3, 3, 6]
def baseStart_1448306 : Nat := 118140960795 + 1448306 * 2 ^ 59
def prefixEnd_1448306 : Nat := 4983230072969 + 3 ^ 40 * 1448306 * 2
def baseEnd_1448306 : Nat := 110174387080106034046573

theorem tailTrace_1448306 : CollatzResearch.WordTrace tailWord_1448306 prefixEnd_1448306 110174387080106034046573 := by
  unfold tailWord_1448306
  simp only [CollatzResearch.WordTrace]
  refine ⟨13206014872760546954323193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35216039660694791878195181 13206014872760546954323193)
  ·
    refine ⟨9904511154570410215742395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13206014872760546954323193 9904511154570410215742395)
    ·
      refine ⟨14856766731855615323613593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9904511154570410215742395 14856766731855615323613593)
      ·
        refine ⟨11142575048891711492710195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14856766731855615323613593 11142575048891711492710195)
        ·
          refine ⟨16713862573337567239065293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11142575048891711492710195 16713862573337567239065293)
          ·
            refine ⟨6267698465001587714649485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16713862573337567239065293 6267698465001587714649485)
            ·
              refine ⟨2350386924375595392993557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6267698465001587714649485 2350386924375595392993557)
              ·
                refine ⟨110174387080106034046573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2350386924375595392993557 110174387080106034046573)
                ·
                  rfl

theorem cell21_1448306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 6].length) (baseStart_1448306 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448306 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448306 prefixEnd_1448306 := by exact prefixLift 1448306
  have htrace : WordTrace (prefixWord ++ tailWord_1448306) baseStart_1448306 baseEnd_1448306 := by
    simpa [prefixWord, tailWord_1448306, baseEnd_1448306] using wordTrace_append hprefix tailTrace_1448306
  have hstable : (prefixWord ++ tailWord_1448306).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448306).length < 2 ^ (prefixWord ++ tailWord_1448306).sum := by decide
  have hdescent : baseEnd_1448306 < baseStart_1448306 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448323 : List Nat := [1, 1, 1, 3, 6, 1, 3, 5]
def baseStart_1448323 : Nat := 118140960795 + 1448323 * 2 ^ 59
def prefixEnd_1448323 : Nat := 4983230072969 + 3 ^ 40 * 1448323 * 2
def baseEnd_1448323 : Nat := 110175680290643283452117

theorem tailTrace_1448323 : CollatzResearch.WordTrace tailWord_1448323 prefixEnd_1448323 110175680290643283452117 := by
  unfold tailWord_1448323
  simp only [CollatzResearch.WordTrace]
  refine ⟨52824679531980599720661623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35216453021320399813774415 52824679531980599720661623)
  ·
    refine ⟨79237019297970899580992435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52824679531980599720661623 79237019297970899580992435)
    ·
      refine ⟨118855528946956349371488653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79237019297970899580992435 118855528946956349371488653)
      ·
        refine ⟨44570823355108631014308245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118855528946956349371488653 44570823355108631014308245)
        ·
          refine ⟨2089257344770717078795699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44570823355108631014308245 2089257344770717078795699)
          ·
            refine ⟨3133886017156075618193549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089257344770717078795699 3133886017156075618193549)
            ·
              refine ⟨1175207256433528356822581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3133886017156075618193549 1175207256433528356822581)
              ·
                refine ⟨110175680290643283452117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1175207256433528356822581 110175680290643283452117)
                ·
                  rfl

theorem cell21_1448323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 5].length) (baseStart_1448323 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448323 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448323 prefixEnd_1448323 := by exact prefixLift 1448323
  have htrace : WordTrace (prefixWord ++ tailWord_1448323) baseStart_1448323 baseEnd_1448323 := by
    simpa [prefixWord, tailWord_1448323, baseEnd_1448323] using wordTrace_append hprefix tailTrace_1448323
  have hstable : (prefixWord ++ tailWord_1448323).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448323).length < 2 ^ (prefixWord ++ tailWord_1448323).sum := by decide
  have hdescent : baseEnd_1448323 < baseStart_1448323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448351 : List Nat := [1, 1, 2, 5, 1, 1, 3, 1, 6]
def baseStart_1448351 : Nat := 118140960795 + 1448351 * 2 ^ 59
def prefixEnd_1448351 : Nat := 4983230072969 + 3 ^ 40 * 1448351 * 2
def baseEnd_1448351 : Nat := 330533430853408023889627

theorem tailTrace_1448351 : CollatzResearch.WordTrace tailWord_1448351 prefixEnd_1448351 330533430853408023889627 := by
  unfold tailWord_1448351
  simp only [CollatzResearch.WordTrace]
  refine ⟨52825700775879160502680907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35217133850586107001787271 52825700775879160502680907)
  ·
    refine ⟨79238551163818740754021361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52825700775879160502680907 79238551163818740754021361)
    ·
      refine ⟨59428913372864055565516021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79238551163818740754021361 59428913372864055565516021)
      ·
        refine ⟨5571460628706005209267127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59428913372864055565516021 5571460628706005209267127)
        ·
          refine ⟨8357190943059007813900691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571460628706005209267127 8357190943059007813900691)
          ·
            refine ⟨12535786414588511720851037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357190943059007813900691 12535786414588511720851037)
            ·
              refine ⟨4700919905470691895319139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12535786414588511720851037 4700919905470691895319139)
              ·
                refine ⟨7051379858206037842978709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4700919905470691895319139 7051379858206037842978709)
                ·
                  refine ⟨330533430853408023889627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7051379858206037842978709 330533430853408023889627)
                  ·
                    rfl

theorem cell21_1448351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_1448351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448351 prefixEnd_1448351 := by exact prefixLift 1448351
  have htrace : WordTrace (prefixWord ++ tailWord_1448351) baseStart_1448351 baseEnd_1448351 := by
    simpa [prefixWord, tailWord_1448351, baseEnd_1448351] using wordTrace_append hprefix tailTrace_1448351
  have hstable : (prefixWord ++ tailWord_1448351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448351).length < 2 ^ (prefixWord ++ tailWord_1448351).sum := by decide
  have hdescent : baseEnd_1448351 < baseStart_1448351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448354 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 3]
def baseStart_1448354 : Nat := 118140960795 + 1448354 * 2 ^ 59
def prefixEnd_1448354 : Nat := 4983230072969 + 3 ^ 40 * 1448354 * 2
def baseEnd_1448354 : Nat := 330534115494280685339621

theorem tailTrace_1448354 : CollatzResearch.WordTrace tailWord_1448354 prefixEnd_1448354 330534115494280685339621 := by
  unfold tailWord_1448354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13206452548717073003760029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35217206796578861343360077 13206452548717073003760029)
  ·
    refine ⟨4952419705768902376410011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13206452548717073003760029 4952419705768902376410011)
    ·
      refine ⟨7428629558653353564615017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4952419705768902376410011 7428629558653353564615017)
      ·
        refine ⟨5571472168990015173461263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7428629558653353564615017 5571472168990015173461263)
        ·
          refine ⟨8357208253485022760191895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5571472168990015173461263 8357208253485022760191895)
          ·
            refine ⟨12535812380227534140287843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8357208253485022760191895 12535812380227534140287843)
            ·
              refine ⟨18803718570341301210431765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12535812380227534140287843 18803718570341301210431765)
              ·
                refine ⟨881424307984748494238989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18803718570341301210431765 881424307984748494238989)
                ·
                  refine ⟨330534115494280685339621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881424307984748494238989 330534115494280685339621)
                  ·
                    rfl

theorem cell21_1448354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_1448354 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448354 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448354 prefixEnd_1448354 := by exact prefixLift 1448354
  have htrace : WordTrace (prefixWord ++ tailWord_1448354) baseStart_1448354 baseEnd_1448354 := by
    simpa [prefixWord, tailWord_1448354, baseEnd_1448354] using wordTrace_append hprefix tailTrace_1448354
  have hstable : (prefixWord ++ tailWord_1448354).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448354).length < 2 ^ (prefixWord ++ tailWord_1448354).sum := by decide
  have hdescent : baseEnd_1448354 < baseStart_1448354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448388 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 3]
def baseStart_1448388 : Nat := 118140960795 + 1448388 * 2 ^ 59
def prefixEnd_1448388 : Nat := 4983230072969 + 3 ^ 40 * 1448388 * 2
def baseEnd_1448388 : Nat := 330541874757504181772885

theorem tailTrace_1448388 : CollatzResearch.WordTrace tailWord_1448388 prefixEnd_1448388 330541874757504181772885 := by
  unfold tailWord_1448388
  simp only [CollatzResearch.WordTrace]
  refine ⟨26413525138372557910888909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35218033517830077214518545 26413525138372557910888909)
  ·
    refine ⟨9905071926889709216583341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26413525138372557910888909 9905071926889709216583341)
    ·
      refine ⟨3714401972583640956218753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9905071926889709216583341 3714401972583640956218753)
      ·
        refine ⟨2785801479437730717164065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3714401972583640956218753 2785801479437730717164065)
        ·
          refine ⟨2089351109578298037873049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2785801479437730717164065 2089351109578298037873049)
          ·
            refine ⟨1567013332183723528404787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2089351109578298037873049 1567013332183723528404787)
            ·
              refine ⟨2350519998275585292607181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567013332183723528404787 2350519998275585292607181)
              ·
                refine ⟨881444999353344484727693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2350519998275585292607181 881444999353344484727693)
                ·
                  refine ⟨330541874757504181772885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881444999353344484727693 330541874757504181772885)
                  ·
                    rfl

theorem cell21_1448388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_1448388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448388 prefixEnd_1448388 := by exact prefixLift 1448388
  have htrace : WordTrace (prefixWord ++ tailWord_1448388) baseStart_1448388 baseEnd_1448388 := by
    simpa [prefixWord, tailWord_1448388, baseEnd_1448388] using wordTrace_append hprefix tailTrace_1448388
  have hstable : (prefixWord ++ tailWord_1448388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448388).length < 2 ^ (prefixWord ++ tailWord_1448388).sum := by decide
  have hdescent : baseEnd_1448388 < baseStart_1448388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448427 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 4]
def baseStart_1448427 : Nat := 118140960795 + 1448427 * 2 ^ 59
def prefixEnd_1448427 : Nat := 4983230072969 + 3 ^ 40 * 1448427 * 2
def baseEnd_1448427 : Nat := 330550775088848780622805

theorem tailTrace_1448427 : CollatzResearch.WordTrace tailWord_1448427 prefixEnd_1448427 330550775088848780622805 := by
  unfold tailWord_1448427
  simp only [CollatzResearch.WordTrace]
  refine ⟨52828472723603825482447535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35218981815735883654965023 52828472723603825482447535)
  ·
    refine ⟨79242709085405738223671303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52828472723603825482447535 79242709085405738223671303)
    ·
      refine ⟨118864063628108607335506955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79242709085405738223671303 118864063628108607335506955)
      ·
        refine ⟨178296095442162911003260433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118864063628108607335506955 178296095442162911003260433)
        ·
          refine ⟨133722071581622183252445325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178296095442162911003260433 133722071581622183252445325)
          ·
            refine ⟨50145776843108318719666997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133722071581622183252445325 50145776843108318719666997)
            ·
              refine ⟨4701166579041404879968781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50145776843108318719666997 4701166579041404879968781)
              ·
                refine ⟨1762937467140526829988293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4701166579041404879968781 1762937467140526829988293)
                ·
                  refine ⟨330550775088848780622805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1762937467140526829988293 330550775088848780622805)
                  ·
                    rfl

theorem cell21_1448427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_1448427 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448427 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448427 prefixEnd_1448427 := by exact prefixLift 1448427
  have htrace : WordTrace (prefixWord ++ tailWord_1448427) baseStart_1448427 baseEnd_1448427 := by
    simpa [prefixWord, tailWord_1448427, baseEnd_1448427] using wordTrace_append hprefix tailTrace_1448427
  have hstable : (prefixWord ++ tailWord_1448427).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448427).length < 2 ^ (prefixWord ++ tailWord_1448427).sum := by decide
  have hdescent : baseEnd_1448427 < baseStart_1448427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448441 : List Nat := [1, 2, 1, 3, 1, 2, 4, 7]
def baseStart_1448441 : Nat := 118140960795 + 1448441 * 2 ^ 59
def prefixEnd_1448441 : Nat := 4983230072969 + 3 ^ 40 * 1448441 * 2
def baseEnd_1448441 : Nat := 110184656693195955796481

theorem tailTrace_1448441 : CollatzResearch.WordTrace tailWord_1448441 prefixEnd_1448441 110184656693195955796481 := by
  unfold tailWord_1448441
  simp only [CollatzResearch.WordTrace]
  refine ⟨52828983345553105873457177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35219322230368737248971451 52828983345553105873457177)
  ·
    refine ⟨39621737509164829405092883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52828983345553105873457177 39621737509164829405092883)
    ·
      refine ⟨59432606263747244107639325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39621737509164829405092883 59432606263747244107639325)
      ·
        refine ⟨22287227348905216540364747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59432606263747244107639325 22287227348905216540364747)
        ·
          refine ⟨33430841023357824810547121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22287227348905216540364747 33430841023357824810547121)
          ·
            refine ⟨25073130767518368607910341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33430841023357824810547121 25073130767518368607910341)
            ·
              refine ⟨4701212018909694113983189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25073130767518368607910341 4701212018909694113983189)
              ·
                refine ⟨110184656693195955796481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4701212018909694113983189 110184656693195955796481)
                ·
                  rfl

theorem cell21_1448441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 7].length) (baseStart_1448441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448441 prefixEnd_1448441 := by exact prefixLift 1448441
  have htrace : WordTrace (prefixWord ++ tailWord_1448441) baseStart_1448441 baseEnd_1448441 := by
    simpa [prefixWord, tailWord_1448441, baseEnd_1448441] using wordTrace_append hprefix tailTrace_1448441
  have hstable : (prefixWord ++ tailWord_1448441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448441).length < 2 ^ (prefixWord ++ tailWord_1448441).sum := by decide
  have hdescent : baseEnd_1448441 < baseStart_1448441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448506 : List Nat := [3, 1, 1, 1, 3, 4, 2, 3, 3]
def baseStart_1448506 : Nat := 118140960795 + 1448506 * 2 ^ 59
def prefixEnd_1448506 : Nat := 4983230072969 + 3 ^ 40 * 1448506 * 2
def baseEnd_1448506 : Nat := 330568803965162198805977

theorem tailTrace_1448506 : CollatzResearch.WordTrace tailWord_1448506 prefixEnd_1448506 330568803965162198805977 := by
  unfold tailWord_1448506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13207838522579405493643343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35220902726878414649715581 13207838522579405493643343)
  ·
    refine ⟨19811757783869108240465015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13207838522579405493643343 19811757783869108240465015)
    ·
      refine ⟨29717636675803662360697523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19811757783869108240465015 29717636675803662360697523)
      ·
        refine ⟨44576455013705493541046285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29717636675803662360697523 44576455013705493541046285)
        ·
          refine ⟨16716170630139560077892357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44576455013705493541046285 16716170630139560077892357)
          ·
            refine ⟨3134281993151167514604817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16716170630139560077892357 3134281993151167514604817)
            ·
              refine ⟨2350711494863375635953613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134281993151167514604817 2350711494863375635953613)
              ·
                refine ⟨881516810573765863482605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2350711494863375635953613 881516810573765863482605)
                ·
                  refine ⟨330568803965162198805977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881516810573765863482605 330568803965162198805977)
                  ·
                    rfl

theorem cell21_1448506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 2, 3, 3].length) (baseStart_1448506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448506 prefixEnd_1448506 := by exact prefixLift 1448506
  have htrace : WordTrace (prefixWord ++ tailWord_1448506) baseStart_1448506 baseEnd_1448506 := by
    simpa [prefixWord, tailWord_1448506, baseEnd_1448506] using wordTrace_append hprefix tailTrace_1448506
  have hstable : (prefixWord ++ tailWord_1448506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448506).length < 2 ^ (prefixWord ++ tailWord_1448506).sum := by decide
  have hdescent : baseEnd_1448506 < baseStart_1448506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448517 : List Nat := [1, 3, 1, 1, 1, 6, 8]
def baseStart_1448517 : Nat := 118140960795 + 1448517 * 2 ^ 59
def prefixEnd_1448517 : Nat := 4983230072969 + 3 ^ 40 * 1448517 * 2
def baseEnd_1448517 : Nat := 36730146035003180458069

theorem tailTrace_1448517 : CollatzResearch.WordTrace tailWord_1448517 prefixEnd_1448517 36730146035003180458069 := by
  unfold tailWord_1448517
  simp only [CollatzResearch.WordTrace]
  refine ⟨52831755293277770853223805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35221170195518513902149203 52831755293277770853223805)
  ·
    refine ⟨19811908234979164069958927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52831755293277770853223805 19811908234979164069958927)
    ·
      refine ⟨29717862352468746104938391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19811908234979164069958927 29717862352468746104938391)
      ·
        refine ⟨44576793528703119157407587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29717862352468746104938391 44576793528703119157407587)
        ·
          refine ⟨66865190293054678736111381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44576793528703119157407587 66865190293054678736111381)
          ·
            refine ⟨3134305794986938065755221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66865190293054678736111381 3134305794986938065755221)
            ·
              refine ⟨36730146035003180458069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3134305794986938065755221 36730146035003180458069)
              ·
                rfl

theorem cell21_1448517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 8].length) (baseStart_1448517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448517 prefixEnd_1448517 := by exact prefixLift 1448517
  have htrace : WordTrace (prefixWord ++ tailWord_1448517) baseStart_1448517 baseEnd_1448517 := by
    simpa [prefixWord, tailWord_1448517, baseEnd_1448517] using wordTrace_append hprefix tailTrace_1448517
  have hstable : (prefixWord ++ tailWord_1448517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448517).length < 2 ^ (prefixWord ++ tailWord_1448517).sum := by decide
  have hdescent : baseEnd_1448517 < baseStart_1448517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448548 : List Nat := [2, 3, 1, 1, 2, 2, 1, 4, 5]
def baseStart_1448548 : Nat := 118140960795 + 1448548 * 2 ^ 59
def prefixEnd_1448548 : Nat := 4983230072969 + 3 ^ 40 * 1448548 * 2
def baseEnd_1448548 : Nat := 330578388937379459105891

theorem tailTrace_1448548 : CollatzResearch.WordTrace tailWord_1448548 prefixEnd_1448548 330578388937379459105891 := by
  unfold tailWord_1448548
  simp only [CollatzResearch.WordTrace]
  refine ⟨26416442978082731573801149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35221923970776975431734865 26416442978082731573801149)
  ·
    refine ⟨9906166116781024340175431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26416442978082731573801149 9906166116781024340175431)
    ·
      refine ⟨14859249175171536510263147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9906166116781024340175431 14859249175171536510263147)
      ·
        refine ⟨22288873762757304765394721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14859249175171536510263147 22288873762757304765394721)
        ·
          refine ⟨16716655322067978574046041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22288873762757304765394721 16716655322067978574046041)
          ·
            refine ⟨12537491491550983930534531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16716655322067978574046041 12537491491550983930534531)
            ·
              refine ⟨18806237237326475895801797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12537491491550983930534531 18806237237326475895801797)
              ·
                refine ⟨3526169481998714230462837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18806237237326475895801797 3526169481998714230462837)
                ·
                  refine ⟨330578388937379459105891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3526169481998714230462837 330578388937379459105891)
                  ·
                    rfl

theorem cell21_1448548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_1448548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448548 prefixEnd_1448548 := by exact prefixLift 1448548
  have htrace : WordTrace (prefixWord ++ tailWord_1448548) baseStart_1448548 baseEnd_1448548 := by
    simpa [prefixWord, tailWord_1448548, baseEnd_1448548] using wordTrace_append hprefix tailTrace_1448548
  have hstable : (prefixWord ++ tailWord_1448548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448548).length < 2 ^ (prefixWord ++ tailWord_1448548).sum := by decide
  have hdescent : baseEnd_1448548 < baseStart_1448548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448630 : List Nat := [5, 1, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1448630 : Nat := 118140960795 + 1448630 * 2 ^ 59
def prefixEnd_1448630 : Nat := 4983230072969 + 3 ^ 40 * 1448630 * 2
def baseEnd_1448630 : Nat := 330597102454565538739057

theorem tailTrace_1448630 : CollatzResearch.WordTrace tailWord_1448630 prefixEnd_1448630 330597102454565538739057 := by
  unfold tailWord_1448630
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302242296366774447005459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35223917827912260768058229 3302242296366774447005459)
  ·
    refine ⟨4953363444550161670508189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3302242296366774447005459 4953363444550161670508189)
    ·
      refine ⟨1857511291706310626440571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4953363444550161670508189 1857511291706310626440571)
      ·
        refine ⟨2786266937559465939660857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1857511291706310626440571 2786266937559465939660857)
        ·
          refine ⟨2089700203169599454745643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2786266937559465939660857 2089700203169599454745643)
          ·
            refine ⟨3134550304754399182118465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089700203169599454745643 3134550304754399182118465)
            ·
              refine ⟨2350912728565799386588849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134550304754399182118465 2350912728565799386588849)
              ·
                refine ⟨1763184546424349539941637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2350912728565799386588849 1763184546424349539941637)
                ·
                  refine ⟨330597102454565538739057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763184546424349539941637 330597102454565538739057)
                  ·
                    rfl

theorem cell21_1448630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1448630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448630 prefixEnd_1448630 := by exact prefixLift 1448630
  have htrace : WordTrace (prefixWord ++ tailWord_1448630) baseStart_1448630 baseEnd_1448630 := by
    simpa [prefixWord, tailWord_1448630, baseEnd_1448630] using wordTrace_append hprefix tailTrace_1448630
  have hstable : (prefixWord ++ tailWord_1448630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448630).length < 2 ^ (prefixWord ++ tailWord_1448630).sum := by decide
  have hdescent : baseEnd_1448630 < baseStart_1448630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448683 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 9]
def baseStart_1448683 : Nat := 118140960795 + 1448683 * 2 ^ 59
def prefixEnd_1448683 : Nat := 4983230072969 + 3 ^ 40 * 1448683 * 2
def baseEnd_1448683 : Nat := 330609197776649224355615

theorem tailTrace_1448683 : CollatzResearch.WordTrace tailWord_1448683 prefixEnd_1448683 330609197776649224355615 := by
  unfold tailWord_1448683
  simp only [CollatzResearch.WordTrace]
  refine ⟨52837809810676381203766703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35225206540450920802511135 52837809810676381203766703)
  ·
    refine ⟨79256714716014571805650055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52837809810676381203766703 79256714716014571805650055)
    ·
      refine ⟨118885072074021857708475083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79256714716014571805650055 118885072074021857708475083)
      ·
        refine ⟨178327608111032786562712625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118885072074021857708475083 178327608111032786562712625)
        ·
          refine ⟨133745706083274589922034469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178327608111032786562712625 133745706083274589922034469)
          ·
            refine ⟨25077319890613985610381463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133745706083274589922034469 25077319890613985610381463)
            ·
              refine ⟨37615979835920978415572195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25077319890613985610381463 37615979835920978415572195)
              ·
                refine ⟨56423969753881467623358293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37615979835920978415572195 56423969753881467623358293)
                ·
                  refine ⟨330609197776649224355615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56423969753881467623358293 330609197776649224355615)
                  ·
                    rfl

theorem cell21_1448683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 9].length) (baseStart_1448683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448683 prefixEnd_1448683 := by exact prefixLift 1448683
  have htrace : WordTrace (prefixWord ++ tailWord_1448683) baseStart_1448683 baseEnd_1448683 := by
    simpa [prefixWord, tailWord_1448683, baseEnd_1448683] using wordTrace_append hprefix tailTrace_1448683
  have hstable : (prefixWord ++ tailWord_1448683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448683).length < 2 ^ (prefixWord ++ tailWord_1448683).sum := by decide
  have hdescent : baseEnd_1448683 < baseStart_1448683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448700 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 5]
def baseStart_1448700 : Nat := 118140960795 + 1448700 * 2 ^ 59
def prefixEnd_1448700 : Nat := 4983230072969 + 3 ^ 40 * 1448700 * 2
def baseEnd_1448700 : Nat := 330613077408260972572247

theorem tailTrace_1448700 : CollatzResearch.WordTrace tailWord_1448700 prefixEnd_1448700 330613077408260972572247 := by
  unfold tailWord_1448700
  simp only [CollatzResearch.WordTrace]
  refine ⟨26419214925807396553567777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35225619901076528738090369 26419214925807396553567777)
  ·
    refine ⟨19814411194355547415175833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26419214925807396553567777 19814411194355547415175833)
    ·
      refine ⟨14860808395766660561381875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19814411194355547415175833 14860808395766660561381875)
      ·
        refine ⟨22291212593649990842072813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14860808395766660561381875 22291212593649990842072813)
        ·
          refine ⟨8359204722618746565777305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22291212593649990842072813 8359204722618746565777305)
          ·
            refine ⟨6269403541964059924332979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8359204722618746565777305 6269403541964059924332979)
            ·
              refine ⟨9404105312946089886499469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6269403541964059924332979 9404105312946089886499469)
              ·
                refine ⟨3526539492354783707437301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9404105312946089886499469 3526539492354783707437301)
                ·
                  refine ⟨330613077408260972572247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3526539492354783707437301 330613077408260972572247)
                  ·
                    rfl

theorem cell21_1448700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 5].length) (baseStart_1448700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448700 prefixEnd_1448700 := by exact prefixLift 1448700
  have htrace : WordTrace (prefixWord ++ tailWord_1448700) baseStart_1448700 baseEnd_1448700 := by
    simpa [prefixWord, tailWord_1448700, baseEnd_1448700] using wordTrace_append hprefix tailTrace_1448700
  have hstable : (prefixWord ++ tailWord_1448700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448700).length < 2 ^ (prefixWord ++ tailWord_1448700).sum := by decide
  have hdescent : baseEnd_1448700 < baseStart_1448700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448762 : List Nat := [3, 1, 1, 1, 6, 1, 2, 6]
def baseStart_1448762 : Nat := 118140960795 + 1448762 * 2 ^ 59
def prefixEnd_1448762 : Nat := 4983230072969 + 3 ^ 40 * 1448762 * 2
def baseEnd_1448762 : Nat := 110209075550987547512929

theorem tailTrace_1448762 : CollatzResearch.WordTrace tailWord_1448762 prefixEnd_1448762 110209075550987547512929 := by
  unfold tailWord_1448762
  simp only [CollatzResearch.WordTrace]
  refine ⟨13210172794347544423973135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35227127451593451797261693 13210172794347544423973135)
  ·
    refine ⟨19815259191521316635959703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13210172794347544423973135 19815259191521316635959703)
    ·
      refine ⟨29722888787281974953939555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19815259191521316635959703 29722888787281974953939555)
      ·
        refine ⟨44584333180922962430909333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29722888787281974953939555 44584333180922962430909333)
        ·
          refine ⟨2089890617855763863948875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44584333180922962430909333 2089890617855763863948875)
          ·
            refine ⟨3134835926783645795923313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089890617855763863948875 3134835926783645795923313)
            ·
              refine ⟨2351126945087734346942485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3134835926783645795923313 2351126945087734346942485)
              ·
                refine ⟨110209075550987547512929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2351126945087734346942485 110209075550987547512929)
                ·
                  rfl

theorem cell21_1448762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 6].length) (baseStart_1448762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448762 prefixEnd_1448762 := by exact prefixLift 1448762
  have htrace : WordTrace (prefixWord ++ tailWord_1448762) baseStart_1448762 baseEnd_1448762 := by
    simpa [prefixWord, tailWord_1448762, baseEnd_1448762] using wordTrace_append hprefix tailTrace_1448762
  have hstable : (prefixWord ++ tailWord_1448762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448762).length < 2 ^ (prefixWord ++ tailWord_1448762).sum := by decide
  have hdescent : baseEnd_1448762 < baseStart_1448762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448807 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 4]
def baseStart_1448807 : Nat := 118140960795 + 1448807 * 2 ^ 59
def prefixEnd_1448807 : Nat := 4983230072969 + 3 ^ 40 * 1448807 * 2
def baseEnd_1448807 : Nat := 330637496266052564288695

theorem tailTrace_1448807 : CollatzResearch.WordTrace tailWord_1448807 prefixEnd_1448807 330637496266052564288695 := by
  unfold tailWord_1448807
  simp only [CollatzResearch.WordTrace]
  refine ⟨52842332462227150381280675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35228221641484766920853783 52842332462227150381280675)
  ·
    refine ⟨79263498693340725571921013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52842332462227150381280675 79263498693340725571921013)
    ·
      refine ⟨7430953002500693022367595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79263498693340725571921013 7430953002500693022367595)
      ·
        refine ⟨11146429503751039533551393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430953002500693022367595 11146429503751039533551393)
        ·
          refine ⟨8359822127813279650163545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11146429503751039533551393 8359822127813279650163545)
          ·
            refine ⟨6269866595859959737622659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8359822127813279650163545 6269866595859959737622659)
            ·
              refine ⟨9404799893789939606433989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6269866595859959737622659 9404799893789939606433989)
              ·
                refine ⟨1763399980085613676206373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9404799893789939606433989 1763399980085613676206373)
                ·
                  refine ⟨330637496266052564288695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763399980085613676206373 330637496266052564288695)
                  ·
                    rfl

theorem cell21_1448807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 4].length) (baseStart_1448807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448807 prefixEnd_1448807 := by exact prefixLift 1448807
  have htrace : WordTrace (prefixWord ++ tailWord_1448807) baseStart_1448807 baseEnd_1448807 := by
    simpa [prefixWord, tailWord_1448807, baseEnd_1448807] using wordTrace_append hprefix tailTrace_1448807
  have hstable : (prefixWord ++ tailWord_1448807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448807).length < 2 ^ (prefixWord ++ tailWord_1448807).sum := by decide
  have hdescent : baseEnd_1448807 < baseStart_1448807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448852 : List Nat := [2, 4, 2, 1, 1, 1, 1, 2, 7]
def baseStart_1448852 : Nat := 118140960795 + 1448852 * 2 ^ 59
def prefixEnd_1448852 : Nat := 4983230072969 + 3 ^ 40 * 1448852 * 2
def baseEnd_1448852 : Nat := 330647765879142486038603

theorem tailTrace_1448852 : CollatzResearch.WordTrace tailWord_1448852 prefixEnd_1448852 330647765879142486038603 := by
  unfold tailWord_1448852
  simp only [CollatzResearch.WordTrace]
  refine ⟨26421986873532061533334405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35229315831376082044445873 26421986873532061533334405)
  ·
    refine ⟨4954122538787261537500201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26421986873532061533334405 4954122538787261537500201)
    ·
      refine ⟨3715591904090446153125151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4954122538787261537500201 3715591904090446153125151)
      ·
        refine ⟨5573387856135669229687727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3715591904090446153125151 5573387856135669229687727)
        ·
          refine ⟨8360081784203503844531591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5573387856135669229687727 8360081784203503844531591)
          ·
            refine ⟨12540122676305255766797387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8360081784203503844531591 12540122676305255766797387)
            ·
              refine ⟨18810184014457883650196081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12540122676305255766797387 18810184014457883650196081)
              ·
                refine ⟨14107638010843412737647061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18810184014457883650196081 14107638010843412737647061)
                ·
                  refine ⟨330647765879142486038603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14107638010843412737647061 330647765879142486038603)
                  ·
                    rfl

theorem cell21_1448852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_1448852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448852 prefixEnd_1448852 := by exact prefixLift 1448852
  have htrace : WordTrace (prefixWord ++ tailWord_1448852) baseStart_1448852 baseEnd_1448852 := by
    simpa [prefixWord, tailWord_1448852, baseEnd_1448852] using wordTrace_append hprefix tailTrace_1448852
  have hstable : (prefixWord ++ tailWord_1448852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448852).length < 2 ^ (prefixWord ++ tailWord_1448852).sum := by decide
  have hdescent : baseEnd_1448852 < baseStart_1448852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1448914 : List Nat := [3, 2, 2, 3, 1, 3, 7]
def baseStart_1448914 : Nat := 118140960795 + 1448914 * 2 ^ 59
def prefixEnd_1448914 : Nat := 4983230072969 + 3 ^ 40 * 1448914 * 2
def baseEnd_1448914 : Nat := 36740212791538239556127

theorem tailTrace_1448914 : CollatzResearch.WordTrace tailWord_1448914 prefixEnd_1448914 36740212791538239556127 := by
  unfold tailWord_1448914
  simp only [CollatzResearch.WordTrace]
  refine ⟨13211558768209876913856449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35230823381893005103617197 13211558768209876913856449)
  ·
    refine ⟨9908669076157407685392337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13211558768209876913856449 9908669076157407685392337)
    ·
      refine ⟨7431501807118055764044253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9908669076157407685392337 7431501807118055764044253)
      ·
        refine ⟨2786813177669270911516595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7431501807118055764044253 2786813177669270911516595)
        ·
          refine ⟨4180219766503906367274893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2786813177669270911516595 4180219766503906367274893)
          ·
            refine ⟨1567582412438964887728085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4180219766503906367274893 1567582412438964887728085)
            ·
              refine ⟨36740212791538239556127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1567582412438964887728085 36740212791538239556127)
              ·
                rfl

theorem cell21_1448914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 7].length) (baseStart_1448914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1448914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1448914 prefixEnd_1448914 := by exact prefixLift 1448914
  have htrace : WordTrace (prefixWord ++ tailWord_1448914) baseStart_1448914 baseEnd_1448914 := by
    simpa [prefixWord, tailWord_1448914, baseEnd_1448914] using wordTrace_append hprefix tailTrace_1448914
  have hstable : (prefixWord ++ tailWord_1448914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1448914).length < 2 ^ (prefixWord ++ tailWord_1448914).sum := by decide
  have hdescent : baseEnd_1448914 < baseStart_1448914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1448914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449021 : List Nat := [1, 4, 1, 3, 1, 2, 1, 5, 3]
def baseStart_1449021 : Nat := 118140960795 + 1449021 * 2 ^ 59
def prefixEnd_1449021 : Nat := 4983230072969 + 3 ^ 40 * 1449021 * 2
def baseEnd_1449021 : Nat := 330686333981635747721591

theorem tailTrace_1449021 : CollatzResearch.WordTrace tailWord_1449021 prefixEnd_1449021 330686333981635747721591 := by
  unfold tailWord_1449021
  simp only [CollatzResearch.WordTrace]
  refine ⟨52850137683451864929570917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35233425122301243286380611 52850137683451864929570917)
  ·
    refine ⟨9909400815647224674294547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52850137683451864929570917 9909400815647224674294547)
    ·
      refine ⟨14864101223470837011441821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9909400815647224674294547 14864101223470837011441821)
      ·
        refine ⟨5574037958801563879290683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14864101223470837011441821 5574037958801563879290683)
        ·
          refine ⟨8361056938202345818936025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574037958801563879290683 8361056938202345818936025)
          ·
            refine ⟨6270792703651759364202019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8361056938202345818936025 6270792703651759364202019)
            ·
              refine ⟨9406189055477639046303029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6270792703651759364202019 9406189055477639046303029)
              ·
                refine ⟨881830223951028660590909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9406189055477639046303029 881830223951028660590909)
                ·
                  refine ⟨330686333981635747721591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881830223951028660590909 330686333981635747721591)
                  ·
                    rfl

theorem cell21_1449021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_1449021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449021 prefixEnd_1449021 := by exact prefixLift 1449021
  have htrace : WordTrace (prefixWord ++ tailWord_1449021) baseStart_1449021 baseEnd_1449021 := by
    simpa [prefixWord, tailWord_1449021, baseEnd_1449021] using wordTrace_append hprefix tailTrace_1449021
  have hstable : (prefixWord ++ tailWord_1449021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449021).length < 2 ^ (prefixWord ++ tailWord_1449021).sum := by decide
  have hdescent : baseEnd_1449021 < baseStart_1449021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449032 : List Nat := [2, 1, 3, 1, 1, 1, 12]
def baseStart_1449032 : Nat := 118140960795 + 1449032 * 2 ^ 59
def prefixEnd_1449032 : Nat := 4983230072969 + 3 ^ 40 * 1449032 * 2
def baseEnd_1449032 : Nat := 36743204925722463670915

theorem tailTrace_1449032 : CollatzResearch.WordTrace tailWord_1449032 prefixEnd_1449032 36743204925722463670915 := by
  unfold tailWord_1449032
  simp only [CollatzResearch.WordTrace]
  refine ⟨26425269443206006904110675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35233692590941342538814233 26425269443206006904110675)
  ·
    refine ⟨39637904164809010356166013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26425269443206006904110675 39637904164809010356166013)
    ·
      refine ⟨14864214061803378883562255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39637904164809010356166013 14864214061803378883562255)
      ·
        refine ⟨22296321092705068325343383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14864214061803378883562255 22296321092705068325343383)
        ·
          refine ⟨33444481639057602488015075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22296321092705068325343383 33444481639057602488015075)
          ·
            refine ⟨50166722458586403732022613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33444481639057602488015075 50166722458586403732022613)
            ·
              refine ⟨36743204925722463670915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 50166722458586403732022613 36743204925722463670915)
              ·
                rfl

theorem cell21_1449032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 12].length) (baseStart_1449032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449032 prefixEnd_1449032 := by exact prefixLift 1449032
  have htrace : WordTrace (prefixWord ++ tailWord_1449032) baseStart_1449032 baseEnd_1449032 := by
    simpa [prefixWord, tailWord_1449032, baseEnd_1449032] using wordTrace_append hprefix tailTrace_1449032
  have hstable : (prefixWord ++ tailWord_1449032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449032).length < 2 ^ (prefixWord ++ tailWord_1449032).sum := by decide
  have hdescent : baseEnd_1449032 < baseStart_1449032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449052 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 4]
def baseStart_1449052 : Nat := 118140960795 + 1449052 * 2 ^ 59
def prefixEnd_1449052 : Nat := 4983230072969 + 3 ^ 40 * 1449052 * 2
def baseEnd_1449052 : Nat := 330693408603986582704861

theorem tailTrace_1449052 : CollatzResearch.WordTrace tailWord_1449052 prefixEnd_1449052 330693408603986582704861 := by
  unfold tailWord_1449052
  simp only [CollatzResearch.WordTrace]
  refine ⟨26425634173169778611974705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35234178897559704815966273 26425634173169778611974705)
  ·
    refine ⟨19819225629877333958981029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26425634173169778611974705 19819225629877333958981029)
    ·
      refine ⟨3716104805602000117308943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19819225629877333958981029 3716104805602000117308943)
      ·
        refine ⟨5574157208403000175963415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3716104805602000117308943 5574157208403000175963415)
        ·
          refine ⟨8361235812604500263945123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5574157208403000175963415 8361235812604500263945123)
          ·
            refine ⟨12541853718906750395917685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8361235812604500263945123 12541853718906750395917685)
            ·
              refine ⟨1175798786147507849617283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12541853718906750395917685 1175798786147507849617283)
              ·
                refine ⟨1763698179221261774425925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175798786147507849617283 1763698179221261774425925)
                ·
                  refine ⟨330693408603986582704861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763698179221261774425925 330693408603986582704861)
                  ·
                    rfl

theorem cell21_1449052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 4].length) (baseStart_1449052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449052 prefixEnd_1449052 := by exact prefixLift 1449052
  have htrace : WordTrace (prefixWord ++ tailWord_1449052) baseStart_1449052 baseEnd_1449052 := by
    simpa [prefixWord, tailWord_1449052, baseEnd_1449052] using wordTrace_append hprefix tailTrace_1449052
  have hstable : (prefixWord ++ tailWord_1449052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449052).length < 2 ^ (prefixWord ++ tailWord_1449052).sum := by decide
  have hdescent : baseEnd_1449052 < baseStart_1449052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449066 : List Nat := [3, 1, 3, 2, 2, 1, 4, 5]
def baseStart_1449066 : Nat := 118140960795 + 1449066 * 2 ^ 59
def prefixEnd_1449066 : Nat := 4983230072969 + 3 ^ 40 * 1449066 * 2
def baseEnd_1449066 : Nat := 110232201198241889823833

theorem tailTrace_1449066 : CollatzResearch.WordTrace tailWord_1449066 prefixEnd_1449066 110232201198241889823833 := by
  unfold tailWord_1449066
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212944742072209403739763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35234519312192558409972701 13212944742072209403739763)
  ·
    refine ⟨19819417113108314105609645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13212944742072209403739763 19819417113108314105609645)
    ·
      refine ⟨7432281417415617789603617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19819417113108314105609645 7432281417415617789603617)
      ·
        refine ⟨5574211063061713342202713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7432281417415617789603617 5574211063061713342202713)
        ·
          refine ⟨4180658297296285006652035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5574211063061713342202713 4180658297296285006652035)
          ·
            refine ⟨6270987445944427509978053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180658297296285006652035 6270987445944427509978053)
            ·
              refine ⟨1175810146114580158120885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6270987445944427509978053 1175810146114580158120885)
              ·
                refine ⟨110232201198241889823833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1175810146114580158120885 110232201198241889823833)
                ·
                  rfl

theorem cell21_1449066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_1449066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449066 prefixEnd_1449066 := by exact prefixLift 1449066
  have htrace : WordTrace (prefixWord ++ tailWord_1449066) baseStart_1449066 baseEnd_1449066 := by
    simpa [prefixWord, tailWord_1449066, baseEnd_1449066] using wordTrace_append hprefix tailTrace_1449066
  have hstable : (prefixWord ++ tailWord_1449066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449066).length < 2 ^ (prefixWord ++ tailWord_1449066).sum := by decide
  have hdescent : baseEnd_1449066 < baseStart_1449066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449111 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 4]
def baseStart_1449111 : Nat := 118140960795 + 1449111 * 2 ^ 59
def prefixEnd_1449111 : Nat := 4983230072969 + 3 ^ 40 * 1449111 * 2
def baseEnd_1449111 : Nat := 330706873207815591221407

theorem tailTrace_1449111 : CollatzResearch.WordTrace tailWord_1449111 prefixEnd_1449111 330706873207815591221407 := by
  unfold tailWord_1449111
  simp only [CollatzResearch.WordTrace]
  refine ⟨52853420253125810300347187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35235613502083873533564791 52853420253125810300347187)
  ·
    refine ⟨79280130379688715450520781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52853420253125810300347187 79280130379688715450520781)
    ·
      refine ⟨29730048892383268293945293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79280130379688715450520781 29730048892383268293945293)
      ·
        refine ⟨11148768334643725610229485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29730048892383268293945293 11148768334643725610229485)
        ·
          refine ⟨4180788125491397103836057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11148768334643725610229485 4180788125491397103836057)
          ·
            refine ⟨3135591094118547827877043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4180788125491397103836057 3135591094118547827877043)
            ·
              refine ⟨4703386641177821741815565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3135591094118547827877043 4703386641177821741815565)
              ·
                refine ⟨1763769990441683153180837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4703386641177821741815565 1763769990441683153180837)
                ·
                  refine ⟨330706873207815591221407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1763769990441683153180837 330706873207815591221407)
                  ·
                    rfl

theorem cell21_1449111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 4].length) (baseStart_1449111 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449111 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449111 prefixEnd_1449111 := by exact prefixLift 1449111
  have htrace : WordTrace (prefixWord ++ tailWord_1449111) baseStart_1449111 baseEnd_1449111 := by
    simpa [prefixWord, tailWord_1449111, baseEnd_1449111] using wordTrace_append hprefix tailTrace_1449111
  have hstable : (prefixWord ++ tailWord_1449111).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449111).length < 2 ^ (prefixWord ++ tailWord_1449111).sum := by decide
  have hdescent : baseEnd_1449111 < baseStart_1449111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449142 : List Nat := [5, 1, 3, 2, 10]
def baseStart_1449142 : Nat := 118140960795 + 1449142 * 2 ^ 59
def prefixEnd_1449142 : Nat := 4983230072969 + 3 ^ 40 * 1449142 * 2
def baseEnd_1449142 : Nat := 4082888244816869459317

theorem tailTrace_1449142 : CollatzResearch.WordTrace tailWord_1449142 prefixEnd_1449142 4082888244816869459317 := by
  unfold tailWord_1449142
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303409432250843912170355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35236367277342335063150453 3303409432250843912170355)
  ·
    refine ⟨4955114148376265868255533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3303409432250843912170355 4955114148376265868255533)
    ·
      refine ⟨1858167805641099700595825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4955114148376265868255533 1858167805641099700595825)
      ·
        refine ⟨1393625854230824775446869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1858167805641099700595825 1393625854230824775446869)
        ·
          refine ⟨4082888244816869459317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1393625854230824775446869 4082888244816869459317)
          ·
            rfl

theorem cell21_1449142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 10].length) (baseStart_1449142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449142 prefixEnd_1449142 := by exact prefixLift 1449142
  have htrace : WordTrace (prefixWord ++ tailWord_1449142) baseStart_1449142 baseEnd_1449142 := by
    simpa [prefixWord, tailWord_1449142, baseEnd_1449142] using wordTrace_append hprefix tailTrace_1449142
  have hstable : (prefixWord ++ tailWord_1449142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449142).length < 2 ^ (prefixWord ++ tailWord_1449142).sum := by decide
  have hdescent : baseEnd_1449142 < baseStart_1449142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449215 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 5]
def baseStart_1449215 : Nat := 118140960795 + 1449215 * 2 ^ 59
def prefixEnd_1449215 : Nat := 4983230072969 + 3 ^ 40 * 1449215 * 2
def baseEnd_1449215 : Nat := 330730607424734521487861

theorem tailTrace_1449215 : CollatzResearch.WordTrace tailWord_1449215 prefixEnd_1449215 330730607424734521487861 := by
  unfold tailWord_1449215
  simp only [CollatzResearch.WordTrace]
  refine ⟨52857213444749036062133099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35238142296499357374755399 52857213444749036062133099)
  ·
    refine ⟨79285820167123554093199649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52857213444749036062133099 79285820167123554093199649)
    ·
      refine ⟨59464365125342665569899737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79285820167123554093199649 59464365125342665569899737)
      ·
        refine ⟨44598273844006999177424803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59464365125342665569899737 44598273844006999177424803)
        ·
          refine ⟨66897410766010498766137205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44598273844006999177424803 66897410766010498766137205)
          ·
            refine ⟨6271632259313484259325363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66897410766010498766137205 6271632259313484259325363)
            ·
              refine ⟨9407448388970226388988045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6271632259313484259325363 9407448388970226388988045)
              ·
                refine ⟨3527793145863834895870517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9407448388970226388988045 3527793145863834895870517)
                ·
                  refine ⟨330730607424734521487861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3527793145863834895870517 330730607424734521487861)
                  ·
                    rfl

theorem cell21_1449215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 5].length) (baseStart_1449215 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449215 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449215 prefixEnd_1449215 := by exact prefixLift 1449215
  have htrace : WordTrace (prefixWord ++ tailWord_1449215) baseStart_1449215 baseEnd_1449215 := by
    simpa [prefixWord, tailWord_1449215, baseEnd_1449215] using wordTrace_append hprefix tailTrace_1449215
  have hstable : (prefixWord ++ tailWord_1449215).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449215).length < 2 ^ (prefixWord ++ tailWord_1449215).sum := by decide
  have hdescent : baseEnd_1449215 < baseStart_1449215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449266 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 3]
def baseStart_1449266 : Nat := 118140960795 + 1449266 * 2 ^ 59
def prefixEnd_1449266 : Nat := 4983230072969 + 3 ^ 40 * 1449266 * 2
def baseEnd_1449266 : Nat := 330742246319569766137757

theorem tailTrace_1449266 : CollatzResearch.WordTrace tailWord_1449266 prefixEnd_1449266 330742246319569766137757 := by
  unfold tailWord_1449266
  simp only [CollatzResearch.WordTrace]
  refine ⟨13214768391891067943059913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35239382378376181181493101 13214768391891067943059913)
  ·
    refine ⟨9911076293918300957294935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13214768391891067943059913 9911076293918300957294935)
    ·
      refine ⟨14866614440877451435942403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9911076293918300957294935 14866614440877451435942403)
      ·
        refine ⟨22299921661316177153913605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14866614440877451435942403 22299921661316177153913605)
        ·
          refine ⟨4181235311496783216358801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22299921661316177153913605 4181235311496783216358801)
          ·
            refine ⟨3135926483622587412269101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4181235311496783216358801 3135926483622587412269101)
            ·
              refine ⟨1175972431358470279600913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3135926483622587412269101 1175972431358470279600913)
              ·
                refine ⟨881979323518852709700685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1175972431358470279600913 881979323518852709700685)
                ·
                  refine ⟨330742246319569766137757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 881979323518852709700685 330742246319569766137757)
                  ·
                    rfl

theorem cell21_1449266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 3].length) (baseStart_1449266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449266 prefixEnd_1449266 := by exact prefixLift 1449266
  have htrace : WordTrace (prefixWord ++ tailWord_1449266) baseStart_1449266 baseEnd_1449266 := by
    simpa [prefixWord, tailWord_1449266, baseEnd_1449266] using wordTrace_append hprefix tailTrace_1449266
  have hstable : (prefixWord ++ tailWord_1449266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449266).length < 2 ^ (prefixWord ++ tailWord_1449266).sum := by decide
  have hdescent : baseEnd_1449266 < baseStart_1449266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449305 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 8]
def baseStart_1449305 : Nat := 118140960795 + 1449305 * 2 ^ 59
def prefixEnd_1449305 : Nat := 4983230072969 + 3 ^ 40 * 1449305 * 2
def baseEnd_1449305 : Nat := 330751146650914364987677

theorem tailTrace_1449305 : CollatzResearch.WordTrace tailWord_1449305 prefixEnd_1449305 330751146650914364987677 := by
  unfold tailWord_1449305
  simp only [CollatzResearch.WordTrace]
  refine ⟨52860496014422981432909369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35240330676281987621939579 52860496014422981432909369)
  ·
    refine ⟨39645372010817236074682027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52860496014422981432909369 39645372010817236074682027)
    ·
      refine ⟨59468058016225854112023041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39645372010817236074682027 59468058016225854112023041)
      ·
        refine ⟨44601043512169390584017281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59468058016225854112023041 44601043512169390584017281)
        ·
          refine ⟨33450782634127042938012961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44601043512169390584017281 33450782634127042938012961)
          ·
            refine ⟨25088086975595282203509721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33450782634127042938012961 25088086975595282203509721)
            ·
              refine ⟨18816065231696461652632291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25088086975595282203509721 18816065231696461652632291)
              ·
                refine ⟨28224097847544692478948437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18816065231696461652632291 28224097847544692478948437)
                ·
                  refine ⟨330751146650914364987677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28224097847544692478948437 330751146650914364987677)
                  ·
                    rfl

theorem cell21_1449305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 8].length) (baseStart_1449305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449305 prefixEnd_1449305 := by exact prefixLift 1449305
  have htrace : WordTrace (prefixWord ++ tailWord_1449305) baseStart_1449305 baseEnd_1449305 := by
    simpa [prefixWord, tailWord_1449305, baseEnd_1449305] using wordTrace_append hprefix tailTrace_1449305
  have hstable : (prefixWord ++ tailWord_1449305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449305).length < 2 ^ (prefixWord ++ tailWord_1449305).sum := by decide
  have hdescent : baseEnd_1449305 < baseStart_1449305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449325 : List Nat := [1, 5, 1, 1, 1, 4, 1, 4, 3]
def baseStart_1449325 : Nat := 118140960795 + 1449325 * 2 ^ 59
def prefixEnd_1449325 : Nat := 4983230072969 + 3 ^ 40 * 1449325 * 2
def baseEnd_1449325 : Nat := 330755710923398774654303

theorem tailTrace_1449325 : CollatzResearch.WordTrace tailWord_1449325 prefixEnd_1449325 330755710923398774654303 := by
  unfold tailWord_1449325
  simp only [CollatzResearch.WordTrace]
  refine ⟨52861225474350524848637429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35240816982900349899091619 52861225474350524848637429)
  ·
    refine ⟨4955739888220361704559759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52861225474350524848637429 4955739888220361704559759)
    ·
      refine ⟨7433609832330542556839639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4955739888220361704559759 7433609832330542556839639)
      ·
        refine ⟨11150414748495813835259459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7433609832330542556839639 11150414748495813835259459)
        ·
          refine ⟨16725622122743720752889189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11150414748495813835259459 16725622122743720752889189)
          ·
            refine ⟨3136054148014447641166723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16725622122743720752889189 3136054148014447641166723)
            ·
              refine ⟨4704081222021671461750085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136054148014447641166723 4704081222021671461750085)
              ·
                refine ⟨882015229129063399078141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4704081222021671461750085 882015229129063399078141)
                ·
                  refine ⟨330755710923398774654303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882015229129063399078141 330755710923398774654303)
                  ·
                    rfl

theorem cell21_1449325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_1449325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449325 prefixEnd_1449325 := by exact prefixLift 1449325
  have htrace : WordTrace (prefixWord ++ tailWord_1449325) baseStart_1449325 baseEnd_1449325 := by
    simpa [prefixWord, tailWord_1449325, baseEnd_1449325] using wordTrace_append hprefix tailTrace_1449325
  have hstable : (prefixWord ++ tailWord_1449325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449325).length < 2 ^ (prefixWord ++ tailWord_1449325).sum := by decide
  have hdescent : baseEnd_1449325 < baseStart_1449325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449342 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1449342 : Nat := 118140960795 + 1449342 * 2 ^ 59
def prefixEnd_1449342 : Nat := 4983230072969 + 3 ^ 40 * 1449342 * 2
def baseEnd_1449342 : Nat := 330759590555010522870935

theorem tailTrace_1449342 : CollatzResearch.WordTrace tailWord_1449342 prefixEnd_1449342 330759590555010522870935 := by
  unfold tailWord_1449342
  simp only [CollatzResearch.WordTrace]
  refine ⟨6607730689411117094000785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35241230343525957834670853 6607730689411117094000785)
  ·
    refine ⟨4955798017058337820500589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6607730689411117094000785 4955798017058337820500589)
    ·
      refine ⟨1858424256396876682687721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4955798017058337820500589 1858424256396876682687721)
      ·
        refine ⟨1393818192297657512015791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1858424256396876682687721 1393818192297657512015791)
        ·
          refine ⟨2090727288446486268023687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393818192297657512015791 2090727288446486268023687)
          ·
            refine ⟨3136090932669729402035531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2090727288446486268023687 3136090932669729402035531)
            ·
              refine ⟨4704136399004594103053297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136090932669729402035531 4704136399004594103053297)
              ·
                refine ⟨3528102299253445577289973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4704136399004594103053297 3528102299253445577289973)
                ·
                  refine ⟨330759590555010522870935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3528102299253445577289973 330759590555010522870935)
                  ·
                    rfl

theorem cell21_1449342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1449342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449342 prefixEnd_1449342 := by exact prefixLift 1449342
  have htrace : WordTrace (prefixWord ++ tailWord_1449342) baseStart_1449342 baseEnd_1449342 := by
    simpa [prefixWord, tailWord_1449342, baseEnd_1449342] using wordTrace_append hprefix tailTrace_1449342
  have hstable : (prefixWord ++ tailWord_1449342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449342).length < 2 ^ (prefixWord ++ tailWord_1449342).sum := by decide
  have hdescent : baseEnd_1449342 < baseStart_1449342 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449410 : List Nat := [3, 5, 2, 1, 2, 1, 1, 3, 3]
def baseStart_1449410 : Nat := 118140960795 + 1449410 * 2 ^ 59
def prefixEnd_1449410 : Nat := 4983230072969 + 3 ^ 40 * 1449410 * 2
def baseEnd_1449410 : Nat := 330775109081457515737463

theorem tailTrace_1449410 : CollatzResearch.WordTrace tailWord_1449410 prefixEnd_1449410 330775109081457515737463 := by
  unfold tailWord_1449410
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216081419760646091370421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35242883786028389576987789 13216081419760646091370421)
  ·
    refine ⟨1239007633102560571065977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13216081419760646091370421 1239007633102560571065977)
    ·
      refine ⟨929255724826920428299483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1239007633102560571065977 929255724826920428299483)
      ·
        refine ⟨1393883587240380642449225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929255724826920428299483 1393883587240380642449225)
        ·
          refine ⟨1045412690430285481836919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1393883587240380642449225 1045412690430285481836919)
          ·
            refine ⟨1568119035645428222755379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045412690430285481836919 1568119035645428222755379)
            ·
              refine ⟨2352178553468142334133069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568119035645428222755379 2352178553468142334133069)
              ·
                refine ⟨882066957550553375299901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2352178553468142334133069 882066957550553375299901)
                ·
                  refine ⟨330775109081457515737463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882066957550553375299901 330775109081457515737463)
                  ·
                    rfl

theorem cell21_1449410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_1449410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449410 prefixEnd_1449410 := by exact prefixLift 1449410
  have htrace : WordTrace (prefixWord ++ tailWord_1449410) baseStart_1449410 baseEnd_1449410 := by
    simpa [prefixWord, tailWord_1449410, baseEnd_1449410] using wordTrace_append hprefix tailTrace_1449410
  have hstable : (prefixWord ++ tailWord_1449410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449410).length < 2 ^ (prefixWord ++ tailWord_1449410).sum := by decide
  have hdescent : baseEnd_1449410 < baseStart_1449410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449505 : List Nat := [1, 2, 3, 2, 2, 4, 1, 6]
def baseStart_1449505 : Nat := 118140960795 + 1449505 * 2 ^ 59
def prefixEnd_1449505 : Nat := 4983230072969 + 3 ^ 40 * 1449505 * 2
def baseEnd_1449505 : Nat := 110265596458586153884645

theorem tailTrace_1449505 : CollatzResearch.WordTrace tailWord_1449505 prefixEnd_1449505 110265596458586153884645 := by
  unfold tailWord_1449505
  simp only [CollatzResearch.WordTrace]
  refine ⟨52867790613698415590189969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35245193742465610393459979 52867790613698415590189969)
  ·
    refine ⟨39650842960273811692642477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52867790613698415590189969 39650842960273811692642477)
    ·
      refine ⟨14869066110102679384740929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39650842960273811692642477 14869066110102679384740929)
      ·
        refine ⟨11151799582577009538555697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14869066110102679384740929 11151799582577009538555697)
        ·
          refine ⟨8363849686932757153916773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11151799582577009538555697 8363849686932757153916773)
          ·
            refine ⟨1568221816299891966359395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8363849686932757153916773 1568221816299891966359395)
            ·
              refine ⟨2352332724449837949539093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568221816299891966359395 2352332724449837949539093)
              ·
                refine ⟨110265596458586153884645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2352332724449837949539093 110265596458586153884645)
                ·
                  rfl

theorem cell21_1449505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 6].length) (baseStart_1449505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449505 prefixEnd_1449505 := by exact prefixLift 1449505
  have htrace : WordTrace (prefixWord ++ tailWord_1449505) baseStart_1449505 baseEnd_1449505 := by
    simpa [prefixWord, tailWord_1449505, baseEnd_1449505] using wordTrace_append hprefix tailTrace_1449505
  have hstable : (prefixWord ++ tailWord_1449505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449505).length < 2 ^ (prefixWord ++ tailWord_1449505).sum := by decide
  have hdescent : baseEnd_1449505 < baseStart_1449505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449542 : List Nat := [6, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1449542 : Nat := 118140960795 + 1449542 * 2 ^ 59
def prefixEnd_1449542 : Nat := 4983230072969 + 3 ^ 40 * 1449542 * 2
def baseEnd_1449542 : Nat := 330805233279854619537193

theorem tailTrace_1449542 : CollatzResearch.WordTrace tailWord_1449542 prefixEnd_1449542 330805233279854619537193 := by
  unfold tailWord_1449542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1652160628580136590915215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35246093409709580606191253 1652160628580136590915215)
  ·
    refine ⟨2478240942870204886372823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1652160628580136590915215 2478240942870204886372823)
    ·
      refine ⟨3717361414305307329559235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2478240942870204886372823 3717361414305307329559235)
      ·
        refine ⟨5576042121457960994338853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3717361414305307329559235 5576042121457960994338853)
        ·
          refine ⟨1045507897773367686438535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5576042121457960994338853 1045507897773367686438535)
          ·
            refine ⟨1568261846660051529657803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045507897773367686438535 1568261846660051529657803)
            ·
              refine ⟨2352392769990077294486705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568261846660051529657803 2352392769990077294486705)
              ·
                refine ⟨1764294577492557970865029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2352392769990077294486705 1764294577492557970865029)
                ·
                  refine ⟨330805233279854619537193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1764294577492557970865029 330805233279854619537193)
                  ·
                    rfl

theorem cell21_1449542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1449542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449542 prefixEnd_1449542 := by exact prefixLift 1449542
  have htrace : WordTrace (prefixWord ++ tailWord_1449542) baseStart_1449542 baseEnd_1449542 := by
    simpa [prefixWord, tailWord_1449542, baseEnd_1449542] using wordTrace_append hprefix tailTrace_1449542
  have hstable : (prefixWord ++ tailWord_1449542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449542).length < 2 ^ (prefixWord ++ tailWord_1449542).sum := by decide
  have hdescent : baseEnd_1449542 < baseStart_1449542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449581 : List Nat := [1, 5, 1, 1, 4, 1, 1, 7]
def baseStart_1449581 : Nat := 118140960795 + 1449581 * 2 ^ 59
def prefixEnd_1449581 : Nat := 4983230072969 + 3 ^ 40 * 1449581 * 2
def baseEnd_1449581 : Nat := 110271377870399739462371

theorem tailTrace_1449581 : CollatzResearch.WordTrace tailWord_1449581 prefixEnd_1449581 110271377870399739462371 := by
  unfold tailWord_1449581
  simp only [CollatzResearch.WordTrace]
  refine ⟨52870562561423080569956597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35247041707615387046637731 52870562561423080569956597)
  ·
    refine ⟨4956615240133413803433431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52870562561423080569956597 4956615240133413803433431)
    ·
      refine ⟨7434922860200120705150147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4956615240133413803433431 7434922860200120705150147)
      ·
        refine ⟨11152384290300181057725221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7434922860200120705150147 11152384290300181057725221)
        ·
          refine ⟨2091072054431283948323479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11152384290300181057725221 2091072054431283948323479)
          ·
            refine ⟨3136608081646925922485219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091072054431283948323479 3136608081646925922485219)
            ·
              refine ⟨4704912122470388883727829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136608081646925922485219 4704912122470388883727829)
              ·
                refine ⟨110271377870399739462371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4704912122470388883727829 110271377870399739462371)
                ·
                  rfl

theorem cell21_1449581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 7].length) (baseStart_1449581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449581 prefixEnd_1449581 := by exact prefixLift 1449581
  have htrace : WordTrace (prefixWord ++ tailWord_1449581) baseStart_1449581 baseEnd_1449581 := by
    simpa [prefixWord, tailWord_1449581, baseEnd_1449581] using wordTrace_append hprefix tailTrace_1449581
  have hstable : (prefixWord ++ tailWord_1449581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449581).length < 2 ^ (prefixWord ++ tailWord_1449581).sum := by decide
  have hdescent : baseEnd_1449581 < baseStart_1449581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449609 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 6]
def baseStart_1449609 : Nat := 118140960795 + 1449609 * 2 ^ 59
def prefixEnd_1449609 : Nat := 4983230072969 + 3 ^ 40 * 1449609 * 2
def baseEnd_1449609 : Nat := 330820523592677391920389

theorem tailTrace_1449609 : CollatzResearch.WordTrace tailWord_1449609 prefixEnd_1449609 330820523592677391920389 := by
  unfold tailWord_1449609
  simp only [CollatzResearch.WordTrace]
  refine ⟨52871583805321641351975881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35247722536881094234650587 52871583805321641351975881)
  ·
    refine ⟨39653687853991231013981911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52871583805321641351975881 39653687853991231013981911)
    ·
      refine ⟨59480531780986846520972867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39653687853991231013981911 59480531780986846520972867)
      ·
        refine ⟨89220797671480269781459301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59480531780986846520972867 89220797671480269781459301)
        ·
          refine ⟨16728899563402550584023619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89220797671480269781459301 16728899563402550584023619)
          ·
            refine ⟨25093349345103825876035429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16728899563402550584023619 25093349345103825876035429)
            ·
              refine ⟨4705003002206967351756643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25093349345103825876035429 4705003002206967351756643)
              ·
                refine ⟨7057504503310451027634965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4705003002206967351756643 7057504503310451027634965)
                ·
                  refine ⟨330820523592677391920389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7057504503310451027634965 330820523592677391920389)
                  ·
                    rfl

theorem cell21_1449609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 6].length) (baseStart_1449609 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449609 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449609 prefixEnd_1449609 := by exact prefixLift 1449609
  have htrace : WordTrace (prefixWord ++ tailWord_1449609) baseStart_1449609 baseEnd_1449609 := by
    simpa [prefixWord, tailWord_1449609, baseEnd_1449609] using wordTrace_append hprefix tailTrace_1449609
  have hstable : (prefixWord ++ tailWord_1449609).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449609).length < 2 ^ (prefixWord ++ tailWord_1449609).sum := by decide
  have hdescent : baseEnd_1449609 < baseStart_1449609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449674 : List Nat := [3, 1, 2, 1, 6, 1, 1, 6]
def baseStart_1449674 : Nat := 118140960795 + 1449674 * 2 ^ 59
def prefixEnd_1449674 : Nat := 4983230072969 + 3 ^ 40 * 1449674 * 2
def baseEnd_1449674 : Nat := 110278452492750574445641

theorem tailTrace_1449674 : CollatzResearch.WordTrace tailWord_1449674 prefixEnd_1449674 110278452492750574445641 := by
  unfold tailWord_1449674
  simp only [CollatzResearch.WordTrace]
  refine ⟨13218488637521539363273019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35249303033390771635394717 13218488637521539363273019)
  ·
    refine ⟨19827732956282309044909529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13218488637521539363273019 19827732956282309044909529)
    ·
      refine ⟨14870799717211731783682147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19827732956282309044909529 14870799717211731783682147)
      ·
        refine ⟨22306199575817597675523221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14870799717211731783682147 22306199575817597675523221)
        ·
          refine ⟨1045603105116449891040151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22306199575817597675523221 1045603105116449891040151)
          ·
            refine ⟨1568404657674674836560227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045603105116449891040151 1568404657674674836560227)
            ·
              refine ⟨2352606986512012254840341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568404657674674836560227 2352606986512012254840341)
              ·
                refine ⟨110278452492750574445641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2352606986512012254840341 110278452492750574445641)
                ·
                  rfl

theorem cell21_1449674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 6].length) (baseStart_1449674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449674 prefixEnd_1449674 := by exact prefixLift 1449674
  have htrace : WordTrace (prefixWord ++ tailWord_1449674) baseStart_1449674 baseEnd_1449674 := by
    simpa [prefixWord, tailWord_1449674, baseEnd_1449674] using wordTrace_append hprefix tailTrace_1449674
  have hstable : (prefixWord ++ tailWord_1449674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449674).length < 2 ^ (prefixWord ++ tailWord_1449674).sum := by decide
  have hdescent : baseEnd_1449674 < baseStart_1449674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449761 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 6]
def baseStart_1449761 : Nat := 118140960795 + 1449761 * 2 ^ 59
def prefixEnd_1449761 : Nat := 4983230072969 + 3 ^ 40 * 1449761 * 2
def baseEnd_1449761 : Nat := 330855212063558905386745

theorem tailTrace_1449761 : CollatzResearch.WordTrace tailWord_1449761 prefixEnd_1449761 330855212063558905386745 := by
  unfold tailWord_1449761
  simp only [CollatzResearch.WordTrace]
  refine ⟨52877127700770971311509137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35251418467180647541006091 52877127700770971311509137)
  ·
    refine ⟨39657845775578228483631853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52877127700770971311509137 39657845775578228483631853)
    ·
      refine ⟨14871692165841835681361945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39657845775578228483631853 14871692165841835681361945)
      ·
        refine ⟨11153769124381376761021459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14871692165841835681361945 11153769124381376761021459)
        ·
          refine ⟨16730653686572065141532189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11153769124381376761021459 16730653686572065141532189)
          ·
            refine ⟨6273995132464524428074571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16730653686572065141532189 6273995132464524428074571)
            ·
              refine ⟨9410992698696786642111857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6273995132464524428074571 9410992698696786642111857)
              ·
                refine ⟨7058244524022589981583893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9410992698696786642111857 7058244524022589981583893)
                ·
                  refine ⟨330855212063558905386745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7058244524022589981583893 330855212063558905386745)
                  ·
                    rfl

theorem cell21_1449761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 6].length) (baseStart_1449761 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449761 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449761 prefixEnd_1449761 := by exact prefixLift 1449761
  have htrace : WordTrace (prefixWord ++ tailWord_1449761) baseStart_1449761 baseEnd_1449761 := by
    simpa [prefixWord, tailWord_1449761, baseEnd_1449761] using wordTrace_append hprefix tailTrace_1449761
  have hstable : (prefixWord ++ tailWord_1449761).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449761).length < 2 ^ (prefixWord ++ tailWord_1449761).sum := by decide
  have hdescent : baseEnd_1449761 < baseStart_1449761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449781 : List Nat := [1, 3, 3, 1, 5, 1, 1, 1, 5]
def baseStart_1449781 : Nat := 118140960795 + 1449781 * 2 ^ 59
def prefixEnd_1449781 : Nat := 4983230072969 + 3 ^ 40 * 1449781 * 2
def baseEnd_1449781 : Nat := 330859776336043315053371

theorem tailTrace_1449781 : CollatzResearch.WordTrace tailWord_1449781 prefixEnd_1449781 330859776336043315053371 := by
  unfold tailWord_1449781
  simp only [CollatzResearch.WordTrace]
  refine ⟨52877857160698514727237197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35251904773799009818158131 52877857160698514727237197)
  ·
    refine ⟨19829196435261943022713949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52877857160698514727237197 19829196435261943022713949)
    ·
      refine ⟨7435948663223228633517731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19829196435261943022713949 7435948663223228633517731)
      ·
        refine ⟨11153922994834842950276597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7435948663223228633517731 11153922994834842950276597)
        ·
          refine ⟨1045680280765766526588431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11153922994834842950276597 1045680280765766526588431)
          ·
            refine ⟨1568520421148649789882647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045680280765766526588431 1568520421148649789882647)
            ·
              refine ⟨2352780631722974684823971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1568520421148649789882647 2352780631722974684823971)
              ·
                refine ⟨3529170947584462027235957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2352780631722974684823971 3529170947584462027235957)
                ·
                  refine ⟨330859776336043315053371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3529170947584462027235957 330859776336043315053371)
                  ·
                    rfl

theorem cell21_1449781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 1, 5].length) (baseStart_1449781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449781 prefixEnd_1449781 := by exact prefixLift 1449781
  have htrace : WordTrace (prefixWord ++ tailWord_1449781) baseStart_1449781 baseEnd_1449781 := by
    simpa [prefixWord, tailWord_1449781, baseEnd_1449781] using wordTrace_append hprefix tailTrace_1449781
  have hstable : (prefixWord ++ tailWord_1449781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449781).length < 2 ^ (prefixWord ++ tailWord_1449781).sum := by decide
  have hdescent : baseEnd_1449781 < baseStart_1449781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449795 : List Nat := [1, 1, 1, 3, 1, 7, 2, 1, 4]
def baseStart_1449795 : Nat := 118140960795 + 1449795 * 2 ^ 59
def prefixEnd_1449795 : Nat := 4983230072969 + 3 ^ 40 * 1449795 * 2
def baseEnd_1449795 : Nat := 330862971326782401820009

theorem tailTrace_1449795 : CollatzResearch.WordTrace tailWord_1449795 prefixEnd_1449795 330862971326782401820009 := by
  unfold tailWord_1449795
  simp only [CollatzResearch.WordTrace]
  refine ⟨52878367782647795118246839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35252245188431863412164559 52878367782647795118246839)
  ·
    refine ⟨79317551673971692677370259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52878367782647795118246839 79317551673971692677370259)
    ·
      refine ⟨118976327510957539016055389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79317551673971692677370259 118976327510957539016055389)
      ·
        refine ⟨44616122816609077131020771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118976327510957539016055389 44616122816609077131020771)
        ·
          refine ⟨66924184224913615696531157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44616122816609077131020771 66924184224913615696531157)
          ·
            refine ⟨1568535567771412867887449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66924184224913615696531157 1568535567771412867887449)
            ·
              refine ⟨1176401675828559650915587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1568535567771412867887449 1176401675828559650915587)
              ·
                refine ⟨1764602513742839476373381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176401675828559650915587 1764602513742839476373381)
                ·
                  refine ⟨330862971326782401820009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1764602513742839476373381 330862971326782401820009)
                  ·
                    rfl

theorem cell21_1449795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 2, 1, 4].length) (baseStart_1449795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449795 prefixEnd_1449795 := by exact prefixLift 1449795
  have htrace : WordTrace (prefixWord ++ tailWord_1449795) baseStart_1449795 baseEnd_1449795 := by
    simpa [prefixWord, tailWord_1449795, baseEnd_1449795] using wordTrace_append hprefix tailTrace_1449795
  have hstable : (prefixWord ++ tailWord_1449795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449795).length < 2 ^ (prefixWord ++ tailWord_1449795).sum := by decide
  have hdescent : baseEnd_1449795 < baseStart_1449795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1449837 : List Nat := [1, 5, 1, 1, 1, 1, 2, 3, 6]
def baseStart_1449837 : Nat := 118140960795 + 1449837 * 2 ^ 59
def prefixEnd_1449837 : Nat := 4983230072969 + 3 ^ 40 * 1449837 * 2
def baseEnd_1449837 : Nat := 330872556298999662119923

theorem tailTrace_1449837 : CollatzResearch.WordTrace tailWord_1449837 prefixEnd_1449837 330872556298999662119923 := by
  unfold tailWord_1449837
  simp only [CollatzResearch.WordTrace]
  refine ⟨52879899648495636291275765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35253266432330424194183843 52879899648495636291275765)
  ·
    refine ⟨4957490592046465902307103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52879899648495636291275765 4957490592046465902307103)
    ·
      refine ⟨7436235888069698853460655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4957490592046465902307103 7436235888069698853460655)
      ·
        refine ⟨11154353832104548280190983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7436235888069698853460655 11154353832104548280190983)
        ·
          refine ⟨16731530748156822420286475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11154353832104548280190983 16731530748156822420286475)
          ·
            refine ⟨25097296122235233630429713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16731530748156822420286475 25097296122235233630429713)
            ·
              refine ⟨18822972091676425222822285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25097296122235233630429713 18822972091676425222822285)
              ·
                refine ⟨7058614534378659458558357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18822972091676425222822285 7058614534378659458558357)
                ·
                  refine ⟨330872556298999662119923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7058614534378659458558357 330872556298999662119923)
                  ·
                    rfl

theorem cell21_1449837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_1449837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1449837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1449837 prefixEnd_1449837 := by exact prefixLift 1449837
  have htrace : WordTrace (prefixWord ++ tailWord_1449837) baseStart_1449837 baseEnd_1449837 := by
    simpa [prefixWord, tailWord_1449837, baseEnd_1449837] using wordTrace_append hprefix tailTrace_1449837
  have hstable : (prefixWord ++ tailWord_1449837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1449837).length < 2 ^ (prefixWord ++ tailWord_1449837).sum := by decide
  have hdescent : baseEnd_1449837 < baseStart_1449837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1449837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450034 : List Nat := [3, 2, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1450034 : Nat := 118140960795 + 1450034 * 2 ^ 59
def prefixEnd_1450034 : Nat := 4983230072969 + 3 ^ 40 * 1450034 * 2
def baseEnd_1450034 : Nat := 330917514382971097336187

theorem tailTrace_1450034 : CollatzResearch.WordTrace tailWord_1450034 prefixEnd_1450034 330917514382971097336187 := by
  unfold tailWord_1450034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13221771207195484734049289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35258056552521292624131437 13221771207195484734049289)
  ·
    refine ⟨9916328405396613550536967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13221771207195484734049289 9916328405396613550536967)
    ·
      refine ⟨14874492608094920325805451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9916328405396613550536967 14874492608094920325805451)
      ·
        refine ⟨22311738912142380488708177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14874492608094920325805451 22311738912142380488708177)
        ·
          refine ⟨16733804184106785366531133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22311738912142380488708177 16733804184106785366531133)
          ·
            refine ⟨6275176569040044512449175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16733804184106785366531133 6275176569040044512449175)
            ·
              refine ⟨9412764853560066768673763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6275176569040044512449175 9412764853560066768673763)
              ·
                refine ⟨14119147280340100153010645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9412764853560066768673763 14119147280340100153010645)
                ·
                  refine ⟨330917514382971097336187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14119147280340100153010645 330917514382971097336187)
                  ·
                    rfl

theorem cell21_1450034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1450034 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450034 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450034 prefixEnd_1450034 := by exact prefixLift 1450034
  have htrace : WordTrace (prefixWord ++ tailWord_1450034) baseStart_1450034 baseEnd_1450034 := by
    simpa [prefixWord, tailWord_1450034, baseEnd_1450034] using wordTrace_append hprefix tailTrace_1450034
  have hstable : (prefixWord ++ tailWord_1450034).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450034).length < 2 ^ (prefixWord ++ tailWord_1450034).sum := by decide
  have hdescent : baseEnd_1450034 < baseStart_1450034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450096 : List Nat := [2, 1, 1, 1, 5, 2, 4, 5]
def baseStart_1450096 : Nat := 118140960795 + 1450096 * 2 ^ 59
def prefixEnd_1450096 : Nat := 4983230072969 + 3 ^ 40 * 1450096 * 2
def baseEnd_1450096 : Nat := 110310554542557589100909

theorem tailTrace_1450096 : CollatzResearch.WordTrace tailWord_1450096 prefixEnd_1450096 110310554542557589100909 := by
  unfold tailWord_1450096
  simp only [CollatzResearch.WordTrace]
  refine ⟨26444673077278661762477071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35259564103038215683302761 26444673077278661762477071)
  ·
    refine ⟨39667009615917992643715607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26444673077278661762477071 39667009615917992643715607)
    ·
      refine ⟨59500514423876988965573411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39667009615917992643715607 59500514423876988965573411)
      ·
        refine ⟨89250771635815483448360117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59500514423876988965573411 89250771635815483448360117)
        ·
          refine ⟨8367259840857701573283761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89250771635815483448360117 8367259840857701573283761)
          ·
            refine ⟨6275444880643276179962821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8367259840857701573283761 6275444880643276179962821)
            ·
              refine ⟨1176645915120614283743029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6275444880643276179962821 1176645915120614283743029)
              ·
                refine ⟨110310554542557589100909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1176645915120614283743029 110310554542557589100909)
                ·
                  rfl

theorem cell21_1450096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 5].length) (baseStart_1450096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450096 prefixEnd_1450096 := by exact prefixLift 1450096
  have htrace : WordTrace (prefixWord ++ tailWord_1450096) baseStart_1450096 baseEnd_1450096 := by
    simpa [prefixWord, tailWord_1450096, baseEnd_1450096] using wordTrace_append hprefix tailTrace_1450096
  have hstable : (prefixWord ++ tailWord_1450096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450096).length < 2 ^ (prefixWord ++ tailWord_1450096).sum := by decide
  have hdescent : baseEnd_1450096 < baseStart_1450096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450113 : List Nat := [1, 2, 4, 2, 4, 1, 7]
def baseStart_1450113 : Nat := 118140960795 + 1450113 * 2 ^ 59
def prefixEnd_1450113 : Nat := 4983230072969 + 3 ^ 40 * 1450113 * 2
def baseEnd_1450113 : Nat := 36770615917698279502151

theorem tailTrace_1450113 : CollatzResearch.WordTrace tailWord_1450113 prefixEnd_1450113 36770615917698279502151 := by
  unfold tailWord_1450113
  simp only [CollatzResearch.WordTrace]
  refine ⟨52889966195495735428322993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35259977463663823618881995 52889966195495735428322993)
  ·
    refine ⟨39667474646621801571242245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52889966195495735428322993 39667474646621801571242245)
    ·
      refine ⟨7437651496241587794607921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39667474646621801571242245 7437651496241587794607921)
      ·
        refine ⟨5578238622181190845955941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7437651496241587794607921 5578238622181190845955941)
        ·
          refine ⟨1045919741658973283616739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5578238622181190845955941 1045919741658973283616739)
          ·
            refine ⟨1568879612488459925425109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1045919741658973283616739 1568879612488459925425109)
            ·
              refine ⟨36770615917698279502151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1568879612488459925425109 36770615917698279502151)
              ·
                rfl

theorem cell21_1450113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 7].length) (baseStart_1450113 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450113 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450113 prefixEnd_1450113 := by exact prefixLift 1450113
  have htrace : WordTrace (prefixWord ++ tailWord_1450113) baseStart_1450113 baseEnd_1450113 := by
    simpa [prefixWord, tailWord_1450113, baseEnd_1450113] using wordTrace_append hprefix tailTrace_1450113
  have hstable : (prefixWord ++ tailWord_1450113).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450113).length < 2 ^ (prefixWord ++ tailWord_1450113).sum := by decide
  have hdescent : baseEnd_1450113 < baseStart_1450113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450172 : List Nat := [2, 2, 2, 3, 4, 8]
def baseStart_1450172 : Nat := 118140960795 + 1450172 * 2 ^ 59
def prefixEnd_1450172 : Nat := 4983230072969 + 3 ^ 40 * 1450172 * 2
def baseEnd_1450172 : Nat := 12257370661596797186515

theorem tailTrace_1450172 : CollatzResearch.WordTrace tailWord_1450172 prefixEnd_1450172 12257370661596797186515 := by
  unfold tailWord_1450172
  simp only [CollatzResearch.WordTrace]
  refine ⟨26446059051140994252360385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35261412068187992336480513 26446059051140994252360385)
  ·
    refine ⟨19834544288355745689270289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26446059051140994252360385 19834544288355745689270289)
    ·
      refine ⟨14875908216266809266952717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19834544288355745689270289 14875908216266809266952717)
      ·
        refine ⟨5578465581100053475107269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14875908216266809266952717 5578465581100053475107269)
        ·
          refine ⟨1045962296456260026582613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5578465581100053475107269 1045962296456260026582613)
          ·
            refine ⟨12257370661596797186515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1045962296456260026582613 12257370661596797186515)
            ·
              rfl

theorem cell21_1450172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 8].length) (baseStart_1450172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450172 prefixEnd_1450172 := by exact prefixLift 1450172
  have htrace : WordTrace (prefixWord ++ tailWord_1450172) baseStart_1450172 baseEnd_1450172 := by
    simpa [prefixWord, tailWord_1450172, baseEnd_1450172] using wordTrace_append hprefix tailTrace_1450172
  have hstable : (prefixWord ++ tailWord_1450172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450172).length < 2 ^ (prefixWord ++ tailWord_1450172).sum := by decide
  have hdescent : baseEnd_1450172 < baseStart_1450172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450178 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1450178 : Nat := 118140960795 + 1450178 * 2 ^ 59
def prefixEnd_1450178 : Nat := 4983230072969 + 3 ^ 40 * 1450178 * 2
def baseEnd_1450178 : Nat := 330950377144858846935893

theorem tailTrace_1450178 : CollatzResearch.WordTrace tailWord_1450178 prefixEnd_1450178 330950377144858846935893 := by
  unfold tailWord_1450178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223084235065062882359797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35261557960173501019626125 13223084235065062882359797)
  ·
    refine ⟨1239664147037349645221231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13223084235065062882359797 1239664147037349645221231)
    ·
      refine ⟨1859496220556024467831847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1239664147037349645221231 1859496220556024467831847)
      ·
        refine ⟨2789244330834036701747771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859496220556024467831847 2789244330834036701747771)
        ·
          refine ⟨4183866496251055052621657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2789244330834036701747771 4183866496251055052621657)
          ·
            refine ⟨3137899872188291289466243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4183866496251055052621657 3137899872188291289466243)
            ·
              refine ⟨4706849808282436934199365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3137899872188291289466243 4706849808282436934199365)
              ·
                refine ⟨882534339052956925162381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4706849808282436934199365 882534339052956925162381)
                ·
                  refine ⟨330950377144858846935893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882534339052956925162381 330950377144858846935893)
                  ·
                    rfl

theorem cell21_1450178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1450178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450178 prefixEnd_1450178 := by exact prefixLift 1450178
  have htrace : WordTrace (prefixWord ++ tailWord_1450178) baseStart_1450178 baseEnd_1450178 := by
    simpa [prefixWord, tailWord_1450178, baseEnd_1450178] using wordTrace_append hprefix tailTrace_1450178
  have hstable : (prefixWord ++ tailWord_1450178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450178).length < 2 ^ (prefixWord ++ tailWord_1450178).sum := by decide
  have hdescent : baseEnd_1450178 < baseStart_1450178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450186 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 5]
def baseStart_1450186 : Nat := 118140960795 + 1450186 * 2 ^ 59
def prefixEnd_1450186 : Nat := 4983230072969 + 3 ^ 40 * 1450186 * 2
def baseEnd_1450186 : Nat := 330952202853852610802543

theorem tailTrace_1450186 : CollatzResearch.WordTrace tailWord_1450186 prefixEnd_1450186 330952202853852610802543 := by
  unfold tailWord_1450186
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223157181057817223932603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35261752482820845930486941 13223157181057817223932603)
  ·
    refine ⟨19834735771586725835898905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13223157181057817223932603 19834735771586725835898905)
    ·
      refine ⟨14876051828690044376924179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19834735771586725835898905 14876051828690044376924179)
      ·
        refine ⟨22314077743035066565386269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14876051828690044376924179 22314077743035066565386269)
        ·
          refine ⟨8367779153638149962019851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22314077743035066565386269 8367779153638149962019851)
          ·
            refine ⟨12551668730457224943029777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8367779153638149962019851 12551668730457224943029777)
            ·
              refine ⟨9413751547842918707272333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12551668730457224943029777 9413751547842918707272333)
              ·
                refine ⟨3530156830441094515227125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9413751547842918707272333 3530156830441094515227125)
                ·
                  refine ⟨330952202853852610802543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3530156830441094515227125 330952202853852610802543)
                  ·
                    rfl

theorem cell21_1450186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_1450186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450186 prefixEnd_1450186 := by exact prefixLift 1450186
  have htrace : WordTrace (prefixWord ++ tailWord_1450186) baseStart_1450186 baseEnd_1450186 := by
    simpa [prefixWord, tailWord_1450186, baseEnd_1450186] using wordTrace_append hprefix tailTrace_1450186
  have hstable : (prefixWord ++ tailWord_1450186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450186).length < 2 ^ (prefixWord ++ tailWord_1450186).sum := by decide
  have hdescent : baseEnd_1450186 < baseStart_1450186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450234 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 4]
def baseStart_1450234 : Nat := 118140960795 + 1450234 * 2 ^ 59
def prefixEnd_1450234 : Nat := 4983230072969 + 3 ^ 40 * 1450234 * 2
def baseEnd_1450234 : Nat := 330963157107815194002445

theorem tailTrace_1450234 : CollatzResearch.WordTrace tailWord_1450234 prefixEnd_1450234 330963157107815194002445 := by
  unfold tailWord_1450234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223594857014343273369439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35262919618704915395651837 13223594857014343273369439)
  ·
    refine ⟨19835392285521514910054159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13223594857014343273369439 19835392285521514910054159)
    ·
      refine ⟨29753088428282272365081239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19835392285521514910054159 29753088428282272365081239)
      ·
        refine ⟨44629632642423408547621859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29753088428282272365081239 44629632642423408547621859)
        ·
          refine ⟨66944448963635112821432789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44629632642423408547621859 66944448963635112821432789)
          ·
            refine ⟨1569010522585197956752331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 66944448963635112821432789 1569010522585197956752331)
            ·
              refine ⟨2353515783877796935128497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569010522585197956752331 2353515783877796935128497)
              ·
                refine ⟨1765136837908347701346373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2353515783877796935128497 1765136837908347701346373)
                ·
                  refine ⟨330963157107815194002445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765136837908347701346373 330963157107815194002445)
                  ·
                    rfl

theorem cell21_1450234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 4].length) (baseStart_1450234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450234 prefixEnd_1450234 := by exact prefixLift 1450234
  have htrace : WordTrace (prefixWord ++ tailWord_1450234) baseStart_1450234 baseEnd_1450234 := by
    simpa [prefixWord, tailWord_1450234, baseEnd_1450234] using wordTrace_append hprefix tailTrace_1450234
  have hstable : (prefixWord ++ tailWord_1450234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450234).length < 2 ^ (prefixWord ++ tailWord_1450234).sum := by decide
  have hdescent : baseEnd_1450234 < baseStart_1450234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450293 : List Nat := [1, 3, 3, 1, 2, 1, 2, 4, 4]
def baseStart_1450293 : Nat := 118140960795 + 1450293 * 2 ^ 59
def prefixEnd_1450293 : Nat := 4983230072969 + 3 ^ 40 * 1450293 * 2
def baseEnd_1450293 : Nat := 330976621711644202518991

theorem tailTrace_1450293 : CollatzResearch.WordTrace tailWord_1450293 prefixEnd_1450293 330976621711644202518991 := by
  unfold tailWord_1450293
  simp only [CollatzResearch.WordTrace]
  refine ⟨52896531334843626169875533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35264354223229084113250355 52896531334843626169875533)
  ·
    refine ⟨19836199250566359813703325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52896531334843626169875533 19836199250566359813703325)
    ·
      refine ⟨7438574718962384930138747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19836199250566359813703325 7438574718962384930138747)
      ·
        refine ⟨11157862078443577395208121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7438574718962384930138747 11157862078443577395208121)
        ·
          refine ⟨8368396558832683046406091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11157862078443577395208121 8368396558832683046406091)
          ·
            refine ⟨12552594838249024569609137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8368396558832683046406091 12552594838249024569609137)
            ·
              refine ⟨9414446128686768427206853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12552594838249024569609137 9414446128686768427206853)
              ·
                refine ⟨1765208649128769080101285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9414446128686768427206853 1765208649128769080101285)
                ·
                  refine ⟨330976621711644202518991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765208649128769080101285 330976621711644202518991)
                  ·
                    rfl

theorem cell21_1450293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 4, 4].length) (baseStart_1450293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450293 prefixEnd_1450293 := by exact prefixLift 1450293
  have htrace : WordTrace (prefixWord ++ tailWord_1450293) baseStart_1450293 baseEnd_1450293 := by
    simpa [prefixWord, tailWord_1450293, baseEnd_1450293] using wordTrace_append hprefix tailTrace_1450293
  have hstable : (prefixWord ++ tailWord_1450293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450293).length < 2 ^ (prefixWord ++ tailWord_1450293).sum := by decide
  have hdescent : baseEnd_1450293 < baseStart_1450293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450358 : List Nat := [5, 1, 1, 4, 1, 2, 1, 6]
def baseStart_1450358 : Nat := 118140960795 + 1450358 * 2 ^ 59
def prefixEnd_1450358 : Nat := 4983230072969 + 3 ^ 40 * 1450358 * 2
def baseEnd_1450358 : Nat := 110330485199072844645175

theorem tailTrace_1450358 : CollatzResearch.WordTrace tailWord_1450358 prefixEnd_1450358 110330485199072844645175 := by
  unfold tailWord_1450358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3306181379975508891936983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35265934719738761513994485 3306181379975508891936983)
  ·
    refine ⟨4959272069963263337905475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3306181379975508891936983 4959272069963263337905475)
    ·
      refine ⟨7438908104944895006858213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4959272069963263337905475 7438908104944895006858213)
      ·
        refine ⟨1394795269677167813785915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7438908104944895006858213 1394795269677167813785915)
        ·
          refine ⟨2092192904515751720678873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394795269677167813785915 2092192904515751720678873)
          ·
            refine ⟨1569144678386813790509155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092192904515751720678873 1569144678386813790509155)
            ·
              refine ⟨2353717017580220685763733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569144678386813790509155 2353717017580220685763733)
              ·
                refine ⟨110330485199072844645175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2353717017580220685763733 110330485199072844645175)
                ·
                  rfl

theorem cell21_1450358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_1450358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450358 prefixEnd_1450358 := by exact prefixLift 1450358
  have htrace : WordTrace (prefixWord ++ tailWord_1450358) baseStart_1450358 baseEnd_1450358 := by
    simpa [prefixWord, tailWord_1450358, baseEnd_1450358] using wordTrace_append hprefix tailTrace_1450358
  have hstable : (prefixWord ++ tailWord_1450358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450358).length < 2 ^ (prefixWord ++ tailWord_1450358).sum := by decide
  have hdescent : baseEnd_1450358 < baseStart_1450358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450473 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 5]
def baseStart_1450473 : Nat := 118140960795 + 1450473 * 2 ^ 59
def prefixEnd_1450473 : Nat := 4983230072969 + 3 ^ 40 * 1450473 * 2
def baseEnd_1450473 : Nat := 331017700164003889518623

theorem tailTrace_1450473 : CollatzResearch.WordTrace tailWord_1450473 prefixEnd_1450473 331017700164003889518623 := by
  unfold tailWord_1450473
  simp only [CollatzResearch.WordTrace]
  refine ⟨52903096474191516911428073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35268730982794344607618715 52903096474191516911428073)
  ·
    refine ⟨39677322355643637683571055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52903096474191516911428073 39677322355643637683571055)
    ·
      refine ⟨59515983533465456525356583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39677322355643637683571055 59515983533465456525356583)
      ·
        refine ⟨89273975300198184788034875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59515983533465456525356583 89273975300198184788034875)
        ·
          refine ⟨133910962950297277182052313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89273975300198184788034875 133910962950297277182052313)
          ·
            refine ⟨100433222212722957886539235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133910962950297277182052313 100433222212722957886539235)
            ·
              refine ⟨150649833319084436829808853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100433222212722957886539235 150649833319084436829808853)
              ·
                refine ⟨3530855468416041488198645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150649833319084436829808853 3530855468416041488198645)
                ·
                  refine ⟨331017700164003889518623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3530855468416041488198645 331017700164003889518623)
                  ·
                    rfl

theorem cell21_1450473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 5].length) (baseStart_1450473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450473 prefixEnd_1450473 := by exact prefixLift 1450473
  have htrace : WordTrace (prefixWord ++ tailWord_1450473) baseStart_1450473 baseEnd_1450473 := by
    simpa [prefixWord, tailWord_1450473, baseEnd_1450473] using wordTrace_append hprefix tailTrace_1450473
  have hstable : (prefixWord ++ tailWord_1450473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450473).length < 2 ^ (prefixWord ++ tailWord_1450473).sum := by decide
  have hdescent : baseEnd_1450473 < baseStart_1450473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450524 : List Nat := [2, 2, 3, 1, 2, 2, 4, 2, 3]
def baseStart_1450524 : Nat := 118140960795 + 1450524 * 2 ^ 59
def prefixEnd_1450524 : Nat := 4983230072969 + 3 ^ 40 * 1450524 * 2
def baseEnd_1450524 : Nat := 331029339058839134168519

theorem tailTrace_1450524 : CollatzResearch.WordTrace tailWord_1450524 prefixEnd_1450524 331029339058839134168519 := by
  unfold tailWord_1450524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26452478298503376310767313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35269971064671168414356417 26452478298503376310767313)
  ·
    refine ⟨19839358723877532233075485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26452478298503376310767313 19839358723877532233075485)
    ·
      refine ⟨7439759521454074587403307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19839358723877532233075485 7439759521454074587403307)
      ·
        refine ⟨11159639282181111881104961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7439759521454074587403307 11159639282181111881104961)
        ·
          refine ⟨8369729461635833910828721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11159639282181111881104961 8369729461635833910828721)
          ·
            refine ⟨6277297096226875433121541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8369729461635833910828721 6277297096226875433121541)
            ·
              refine ⟨1176993205542539143710289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6277297096226875433121541 1176993205542539143710289)
              ·
                refine ⟨882744904156904357782717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1176993205542539143710289 882744904156904357782717)
                ·
                  refine ⟨331029339058839134168519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882744904156904357782717 331029339058839134168519)
                  ·
                    rfl

theorem cell21_1450524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_1450524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450524 prefixEnd_1450524 := by exact prefixLift 1450524
  have htrace : WordTrace (prefixWord ++ tailWord_1450524) baseStart_1450524 baseEnd_1450524 := by
    simpa [prefixWord, tailWord_1450524, baseEnd_1450524] using wordTrace_append hprefix tailTrace_1450524
  have hstable : (prefixWord ++ tailWord_1450524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450524).length < 2 ^ (prefixWord ++ tailWord_1450524).sum := by decide
  have hdescent : baseEnd_1450524 < baseStart_1450524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450541 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 5]
def baseStart_1450541 : Nat := 118140960795 + 1450541 * 2 ^ 59
def prefixEnd_1450541 : Nat := 4983230072969 + 3 ^ 40 * 1450541 * 2
def baseEnd_1450541 : Nat := 331033218690450882385151

theorem tailTrace_1450541 : CollatzResearch.WordTrace tailWord_1450541 prefixEnd_1450541 331033218690450882385151 := by
  unfold tailWord_1450541
  simp only [CollatzResearch.WordTrace]
  refine ⟨52905576637945164524903477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35270384425296776349935651 52905576637945164524903477)
  ·
    refine ⟨4959897809807359174209701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52905576637945164524903477 4959897809807359174209701)
    ·
      refine ⟨929980839338879845164319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4959897809807359174209701 929980839338879845164319)
      ·
        refine ⟨1394971259008319767746479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 929980839338879845164319 1394971259008319767746479)
        ·
          refine ⟨2092456888512479651619719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1394971259008319767746479 2092456888512479651619719)
          ·
            refine ⟨3138685332768719477429579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2092456888512479651619719 3138685332768719477429579)
            ·
              refine ⟨4708027999153079216144369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3138685332768719477429579 4708027999153079216144369)
              ·
                refine ⟨3531020999364809412108277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4708027999153079216144369 3531020999364809412108277)
                ·
                  refine ⟨331033218690450882385151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3531020999364809412108277 331033218690450882385151)
                  ·
                    rfl

theorem cell21_1450541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_1450541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450541 prefixEnd_1450541 := by exact prefixLift 1450541
  have htrace : WordTrace (prefixWord ++ tailWord_1450541) baseStart_1450541 baseEnd_1450541 := by
    simpa [prefixWord, tailWord_1450541, baseEnd_1450541] using wordTrace_append hprefix tailTrace_1450541
  have hstable : (prefixWord ++ tailWord_1450541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450541).length < 2 ^ (prefixWord ++ tailWord_1450541).sum := by decide
  have hdescent : baseEnd_1450541 < baseStart_1450541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450735 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 3]
def baseStart_1450735 : Nat := 118140960795 + 1450735 * 2 ^ 59
def prefixEnd_1450735 : Nat := 4983230072969 + 3 ^ 40 * 1450735 * 2
def baseEnd_1450735 : Nat := 331077492133549656151421

theorem tailTrace_1450735 : CollatzResearch.WordTrace tailWord_1450735 prefixEnd_1450735 331077492133549656151421 := by
  unfold tailWord_1450735
  simp only [CollatzResearch.WordTrace]
  refine ⟨52912652399242335657465659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35275101599494890438310439 52912652399242335657465659)
  ·
    refine ⟨79368978598863503486198489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52912652399242335657465659 79368978598863503486198489)
    ·
      refine ⟨59526733949147627614648867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79368978598863503486198489 59526733949147627614648867)
      ·
        refine ⟨89290100923721441421973301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59526733949147627614648867 89290100923721441421973301)
        ·
          refine ⟨8370946961598885133309997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89290100923721441421973301 8370946961598885133309997)
          ·
            refine ⟨3139105110599581924991249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8370946961598885133309997 3139105110599581924991249)
            ·
              refine ⟨2354328832949686443743437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3139105110599581924991249 2354328832949686443743437)
              ·
                refine ⟨882873312356132416403789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2354328832949686443743437 882873312356132416403789)
                ·
                  refine ⟨331077492133549656151421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882873312356132416403789 331077492133549656151421)
                  ·
                    rfl

theorem cell21_1450735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 3].length) (baseStart_1450735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450735 prefixEnd_1450735 := by exact prefixLift 1450735
  have htrace : WordTrace (prefixWord ++ tailWord_1450735) baseStart_1450735 baseEnd_1450735 := by
    simpa [prefixWord, tailWord_1450735, baseEnd_1450735] using wordTrace_append hprefix tailTrace_1450735
  have hstable : (prefixWord ++ tailWord_1450735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450735).length < 2 ^ (prefixWord ++ tailWord_1450735).sum := by decide
  have hdescent : baseEnd_1450735 < baseStart_1450735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450741 : List Nat := [1, 3, 6, 1, 2, 1, 1, 2, 4]
def baseStart_1450741 : Nat := 118140960795 + 1450741 * 2 ^ 59
def prefixEnd_1450741 : Nat := 4983230072969 + 3 ^ 40 * 1450741 * 2
def baseEnd_1450741 : Nat := 331078861415294979051409

theorem tailTrace_1450741 : CollatzResearch.WordTrace tailWord_1450741 prefixEnd_1450741 331078861415294979051409 := by
  unfold tailWord_1450741
  simp only [CollatzResearch.WordTrace]
  refine ⟨52912871237220598682184077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35275247491480399121456051 52912871237220598682184077)
  ·
    refine ⟨19842326713957724505819029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52912871237220598682184077 19842326713957724505819029)
    ·
      refine ⟨930109064716768336210267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19842326713957724505819029 930109064716768336210267)
      ·
        refine ⟨1395163597075152504315401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930109064716768336210267 1395163597075152504315401)
        ·
          refine ⟨1046372697806364378236551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1395163597075152504315401 1046372697806364378236551)
          ·
            refine ⟨1569559046709546567354827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046372697806364378236551 1569559046709546567354827)
            ·
              refine ⟨2354338570064319851032241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1569559046709546567354827 2354338570064319851032241)
              ·
                refine ⟨1765753927548239888274181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2354338570064319851032241 1765753927548239888274181)
                ·
                  refine ⟨331078861415294979051409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765753927548239888274181 331078861415294979051409)
                  ·
                    rfl

theorem cell21_1450741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 2, 4].length) (baseStart_1450741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450741 prefixEnd_1450741 := by exact prefixLift 1450741
  have htrace : WordTrace (prefixWord ++ tailWord_1450741) baseStart_1450741 baseEnd_1450741 := by
    simpa [prefixWord, tailWord_1450741, baseEnd_1450741] using wordTrace_append hprefix tailTrace_1450741
  have hstable : (prefixWord ++ tailWord_1450741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450741).length < 2 ^ (prefixWord ++ tailWord_1450741).sum := by decide
  have hdescent : baseEnd_1450741 < baseStart_1450741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450780 : List Nat := [2, 2, 3, 1, 1, 5, 2, 5]
def baseStart_1450780 : Nat := 118140960795 + 1450780 * 2 ^ 59
def prefixEnd_1450780 : Nat := 4983230072969 + 3 ^ 40 * 1450780 * 2
def baseEnd_1450780 : Nat := 110362587248879859300443

theorem tailTrace_1450780 : CollatzResearch.WordTrace tailWord_1450780 prefixEnd_1450780 110362587248879859300443 := by
  unfold tailWord_1450780
  simp only [CollatzResearch.WordTrace]
  refine ⟨26457146842039654171426897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35276195789386205561902529 26457146842039654171426897)
  ·
    refine ⟨19842860131529740628570173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26457146842039654171426897 19842860131529740628570173)
    ·
      refine ⟨7441072549323652735713815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19842860131529740628570173 7441072549323652735713815)
      ·
        refine ⟨11161608823985479103570723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7441072549323652735713815 11161608823985479103570723)
        ·
          refine ⟨16742413235978218655356085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11161608823985479103570723 16742413235978218655356085)
          ·
            refine ⟨1569601240872957998939633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16742413235978218655356085 1569601240872957998939633)
            ·
              refine ⟨1177200930654718499204725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569601240872957998939633 1177200930654718499204725)
              ·
                refine ⟨110362587248879859300443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1177200930654718499204725 110362587248879859300443)
                ·
                  rfl

theorem cell21_1450780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 2, 5].length) (baseStart_1450780 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450780 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450780 prefixEnd_1450780 := by exact prefixLift 1450780
  have htrace : WordTrace (prefixWord ++ tailWord_1450780) baseStart_1450780 baseEnd_1450780 := by
    simpa [prefixWord, tailWord_1450780, baseEnd_1450780] using wordTrace_append hprefix tailTrace_1450780
  have hstable : (prefixWord ++ tailWord_1450780).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450780).length < 2 ^ (prefixWord ++ tailWord_1450780).sum := by decide
  have hdescent : baseEnd_1450780 < baseStart_1450780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450797 : List Nat := [1, 5, 3, 2, 1, 2, 7]
def baseStart_1450797 : Nat := 118140960795 + 1450797 * 2 ^ 59
def prefixEnd_1450797 : Nat := 4983230072969 + 3 ^ 40 * 1450797 * 2
def baseEnd_1450797 : Nat := 36787960153139036235329

theorem tailTrace_1450797 : CollatzResearch.WordTrace tailWord_1450797 prefixEnd_1450797 36787960153139036235329 := by
  unfold tailWord_1450797
  simp only [CollatzResearch.WordTrace]
  refine ⟨52914913725017720246222645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35276609150011813497481763 52914913725017720246222645)
  ·
    refine ⟨4960773161720411273083373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52914913725017720246222645 4960773161720411273083373)
    ·
      refine ⟨1860289935645154227406265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4960773161720411273083373 1860289935645154227406265)
      ·
        refine ⟨1395217451733865670554699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1860289935645154227406265 1395217451733865670554699)
        ·
          refine ⟨2092826177600798505832049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395217451733865670554699 2092826177600798505832049)
          ·
            refine ⟨1569619633200598879374037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2092826177600798505832049 1569619633200598879374037)
            ·
              refine ⟨36787960153139036235329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1569619633200598879374037 36787960153139036235329)
              ·
                rfl

theorem cell21_1450797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 2, 7].length) (baseStart_1450797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450797 prefixEnd_1450797 := by exact prefixLift 1450797
  have htrace : WordTrace (prefixWord ++ tailWord_1450797) baseStart_1450797 baseEnd_1450797 := by
    simpa [prefixWord, tailWord_1450797, baseEnd_1450797] using wordTrace_append hprefix tailTrace_1450797
  have hstable : (prefixWord ++ tailWord_1450797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450797).length < 2 ^ (prefixWord ++ tailWord_1450797).sum := by decide
  have hdescent : baseEnd_1450797 < baseStart_1450797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450808 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 4]
def baseStart_1450808 : Nat := 118140960795 + 1450808 * 2 ^ 59
def prefixEnd_1450808 : Nat := 4983230072969 + 3 ^ 40 * 1450808 * 2
def baseEnd_1450808 : Nat := 331094151728117751434605

theorem tailTrace_1450808 : CollatzResearch.WordTrace tailWord_1450808 prefixEnd_1450808 331094151728117751434605 := by
  unfold tailWord_1450808
  simp only [CollatzResearch.WordTrace]
  refine ⟨26457657463988934562436539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35276876618651912749915385 26457657463988934562436539)
  ·
    refine ⟨39686486195983401843654809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26457657463988934562436539 39686486195983401843654809)
    ·
      refine ⟨29764864646987551382741107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39686486195983401843654809 29764864646987551382741107)
      ·
        refine ⟨44647296970481327074111661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29764864646987551382741107 44647296970481327074111661)
        ·
          refine ⟨16742736363930497652791873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44647296970481327074111661 16742736363930497652791873)
          ·
            refine ⟨12557052272947873239593905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16742736363930497652791873 12557052272947873239593905)
            ·
              refine ⟨9417789204710904929695429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12557052272947873239593905 9417789204710904929695429)
              ·
                refine ⟨1765835475883294674317893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9417789204710904929695429 1765835475883294674317893)
                ·
                  refine ⟨331094151728117751434605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765835475883294674317893 331094151728117751434605)
                  ·
                    rfl

theorem cell21_1450808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 4].length) (baseStart_1450808 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450808 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450808 prefixEnd_1450808 := by exact prefixLift 1450808
  have htrace : WordTrace (prefixWord ++ tailWord_1450808) baseStart_1450808 baseEnd_1450808 := by
    simpa [prefixWord, tailWord_1450808, baseEnd_1450808] using wordTrace_append hprefix tailTrace_1450808
  have hstable : (prefixWord ++ tailWord_1450808).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450808).length < 2 ^ (prefixWord ++ tailWord_1450808).sum := by decide
  have hdescent : baseEnd_1450808 < baseStart_1450808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450825 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 4]
def baseStart_1450825 : Nat := 118140960795 + 1450825 * 2 ^ 59
def prefixEnd_1450825 : Nat := 4983230072969 + 3 ^ 40 * 1450825 * 2
def baseEnd_1450825 : Nat := 331098031359729499651237

theorem tailTrace_1450825 : CollatzResearch.WordTrace tailWord_1450825 prefixEnd_1450825 331098031359729499651237 := by
  unfold tailWord_1450825
  simp only [CollatzResearch.WordTrace]
  refine ⟨52915934968916281028241929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35277289979277520685494619 52915934968916281028241929)
  ·
    refine ⟨39686951226687210771181447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52915934968916281028241929 39686951226687210771181447)
    ·
      refine ⟨59530426840030816156772171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39686951226687210771181447 59530426840030816156772171)
      ·
        refine ⟨89295640260046224235158257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59530426840030816156772171 89295640260046224235158257)
        ·
          refine ⟨66971730195034668176368693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89295640260046224235158257 66971730195034668176368693)
          ·
            refine ⟨6278599705784500141534565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66971730195034668176368693 6278599705784500141534565)
            ·
              refine ⟨1177237444834593776537731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6278599705784500141534565 1177237444834593776537731)
              ·
                refine ⟨1765856167251890664806597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177237444834593776537731 1765856167251890664806597)
                ·
                  refine ⟨331098031359729499651237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1765856167251890664806597 331098031359729499651237)
                  ·
                    rfl

theorem cell21_1450825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 4].length) (baseStart_1450825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450825 prefixEnd_1450825 := by exact prefixLift 1450825
  have htrace : WordTrace (prefixWord ++ tailWord_1450825) baseStart_1450825 baseEnd_1450825 := by
    simpa [prefixWord, tailWord_1450825, baseEnd_1450825] using wordTrace_append hprefix tailTrace_1450825
  have hstable : (prefixWord ++ tailWord_1450825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450825).length < 2 ^ (prefixWord ++ tailWord_1450825).sum := by decide
  have hdescent : baseEnd_1450825 < baseStart_1450825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450862 : List Nat := [4, 1, 2, 3, 3, 1, 2, 2, 3]
def baseStart_1450862 : Nat := 118140960795 + 1450862 * 2 ^ 59
def prefixEnd_1450862 : Nat := 4983230072969 + 3 ^ 40 * 1450862 * 2
def baseEnd_1450862 : Nat := 331106475263825657534495

theorem tailTrace_1450862 : CollatzResearch.WordTrace tailWord_1450862 prefixEnd_1450862 331106475263825657534495 := by
  unfold tailWord_1450862
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614660558722779543417355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35278189646521490898225893 6614660558722779543417355)
  ·
    refine ⟨9921990838084169315126033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6614660558722779543417355 9921990838084169315126033)
    ·
      refine ⟨7441493128563126986344525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9921990838084169315126033 7441493128563126986344525)
      ·
        refine ⟨2790559923211172619879197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7441493128563126986344525 2790559923211172619879197)
        ·
          refine ⟨1046459971204189732454699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2790559923211172619879197 1046459971204189732454699)
          ·
            refine ⟨1569689956806284598682049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046459971204189732454699 1569689956806284598682049)
            ·
              refine ⟨1177267467604713449011537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569689956806284598682049 1177267467604713449011537)
              ·
                refine ⟨882950600703535086758653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177267467604713449011537 882950600703535086758653)
                ·
                  refine ⟨331106475263825657534495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 882950600703535086758653 331106475263825657534495)
                  ·
                    rfl

theorem cell21_1450862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_1450862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450862 prefixEnd_1450862 := by exact prefixLift 1450862
  have htrace : WordTrace (prefixWord ++ tailWord_1450862) baseStart_1450862 baseEnd_1450862 := by
    simpa [prefixWord, tailWord_1450862, baseEnd_1450862] using wordTrace_append hprefix tailTrace_1450862
  have hstable : (prefixWord ++ tailWord_1450862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450862).length < 2 ^ (prefixWord ++ tailWord_1450862).sum := by decide
  have hdescent : baseEnd_1450862 < baseStart_1450862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450867 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 6]
def baseStart_1450867 : Nat := 118140960795 + 1450867 * 2 ^ 59
def prefixEnd_1450867 : Nat := 4983230072969 + 3 ^ 40 * 1450867 * 2
def baseEnd_1450867 : Nat := 331107616331946759951151

theorem tailTrace_1450867 : CollatzResearch.WordTrace tailWord_1450867 prefixEnd_1450867 331107616331946759951151 := by
  unfold tailWord_1450867
  simp only [CollatzResearch.WordTrace]
  refine ⟨52917466834764122201270855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35278311223176081467513903 52917466834764122201270855)
  ·
    refine ⟨79376200252146183301906283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52917466834764122201270855 79376200252146183301906283)
    ·
      refine ⟨119064300378219274952859425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79376200252146183301906283 119064300378219274952859425)
      ·
        refine ⟨89298225283664456214644569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119064300378219274952859425 89298225283664456214644569)
        ·
          refine ⟨66973668962748342160983427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89298225283664456214644569 66973668962748342160983427)
          ·
            refine ⟨100460503444122513241475141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66973668962748342160983427 100460503444122513241475141)
            ·
              refine ⟨18836344395772971232776589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100460503444122513241475141 18836344395772971232776589)
              ·
                refine ⟨7063629148414864212291221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18836344395772971232776589 7063629148414864212291221)
                ·
                  refine ⟨331107616331946759951151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7063629148414864212291221 331107616331946759951151)
                  ·
                    rfl

theorem cell21_1450867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 6].length) (baseStart_1450867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450867 prefixEnd_1450867 := by exact prefixLift 1450867
  have htrace : WordTrace (prefixWord ++ tailWord_1450867) baseStart_1450867 baseEnd_1450867 := by
    simpa [prefixWord, tailWord_1450867, baseEnd_1450867] using wordTrace_append hprefix tailTrace_1450867
  have hstable : (prefixWord ++ tailWord_1450867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450867).length < 2 ^ (prefixWord ++ tailWord_1450867).sum := by decide
  have hdescent : baseEnd_1450867 < baseStart_1450867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1450994 : List Nat := [3, 2, 1, 5, 1, 1, 1, 3, 4]
def baseStart_1450994 : Nat := 118140960795 + 1450994 * 2 ^ 59
def prefixEnd_1450994 : Nat := 4983230072969 + 3 ^ 40 * 1450994 * 2
def baseEnd_1450994 : Nat := 331136599462222761334225

theorem tailTrace_1450994 : CollatzResearch.WordTrace tailWord_1450994 prefixEnd_1450994 331136599462222761334225 := by
  unfold tailWord_1450994
  simp only [CollatzResearch.WordTrace]
  refine ⟨13230524726326005722786009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35281399270202681927429357 13230524726326005722786009)
  ·
    refine ⟨9922893544744504292089507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13230524726326005722786009 9922893544744504292089507)
    ·
      refine ⟨14884340317116756438134261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9922893544744504292089507 14884340317116756438134261)
      ·
        refine ⟨1395406904729695916075087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14884340317116756438134261 1395406904729695916075087)
        ·
          refine ⟨2093110357094543874112631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395406904729695916075087 2093110357094543874112631)
          ·
            refine ⟨3139665535641815811168947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093110357094543874112631 3139665535641815811168947)
            ·
              refine ⟨4709498303462723716753421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3139665535641815811168947 4709498303462723716753421)
              ·
                refine ⟨1766061863798521393782533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4709498303462723716753421 1766061863798521393782533)
                ·
                  refine ⟨331136599462222761334225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766061863798521393782533 331136599462222761334225)
                  ·
                    rfl

theorem cell21_1450994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_1450994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1450994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1450994 prefixEnd_1450994 := by exact prefixLift 1450994
  have htrace : WordTrace (prefixWord ++ tailWord_1450994) baseStart_1450994 baseEnd_1450994 := by
    simpa [prefixWord, tailWord_1450994, baseEnd_1450994] using wordTrace_append hprefix tailTrace_1450994
  have hstable : (prefixWord ++ tailWord_1450994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1450994).length < 2 ^ (prefixWord ++ tailWord_1450994).sum := by decide
  have hdescent : baseEnd_1450994 < baseStart_1450994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1450994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451039 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 3]
def baseStart_1451039 : Nat := 118140960795 + 1451039 * 2 ^ 59
def prefixEnd_1451039 : Nat := 4983230072969 + 3 ^ 40 * 1451039 * 2
def baseEnd_1451039 : Nat := 331146869075312683084133

theorem tailTrace_1451039 : CollatzResearch.WordTrace tailWord_1451039 prefixEnd_1451039 331146869075312683084133 := by
  unfold tailWord_1451039
  simp only [CollatzResearch.WordTrace]
  refine ⟨52923740190140995576532171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35282493460093997051021447 52923740190140995576532171)
  ·
    refine ⟨79385610285211493364798257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52923740190140995576532171 79385610285211493364798257)
    ·
      refine ⟨59539207713908620023598693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79385610285211493364798257 59539207713908620023598693)
      ·
        refine ⟨11163601446357866254424755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59539207713908620023598693 11163601446357866254424755)
        ·
          refine ⟨16745402169536799381637133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11163601446357866254424755 16745402169536799381637133)
          ·
            refine ⟨6279525813576299768113925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16745402169536799381637133 6279525813576299768113925)
            ·
              refine ⟨1177411090045556206521361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6279525813576299768113925 1177411090045556206521361)
              ·
                refine ⟨883058317534167154891021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177411090045556206521361 883058317534167154891021)
                ·
                  refine ⟨331146869075312683084133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883058317534167154891021 331146869075312683084133)
                  ·
                    rfl

theorem cell21_1451039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 3].length) (baseStart_1451039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451039 prefixEnd_1451039 := by exact prefixLift 1451039
  have htrace : WordTrace (prefixWord ++ tailWord_1451039) baseStart_1451039 baseEnd_1451039 := by
    simpa [prefixWord, tailWord_1451039, baseEnd_1451039] using wordTrace_append hprefix tailTrace_1451039
  have hstable : (prefixWord ++ tailWord_1451039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451039).length < 2 ^ (prefixWord ++ tailWord_1451039).sum := by decide
  have hdescent : baseEnd_1451039 < baseStart_1451039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451233 : List Nat := [1, 2, 3, 1, 3, 3, 1, 2, 5]
def baseStart_1451233 : Nat := 118140960795 + 1451233 * 2 ^ 59
def prefixEnd_1451233 : Nat := 4983230072969 + 3 ^ 40 * 1451233 * 2
def baseEnd_1451233 : Nat := 331191142518411456850403

theorem tailTrace_1451233 : CollatzResearch.WordTrace tailWord_1451233 prefixEnd_1451233 331191142518411456850403 := by
  unfold tailWord_1451233
  simp only [CollatzResearch.WordTrace]
  refine ⟨52930815951438166709094353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35287210634292111139396235 52930815951438166709094353)
  ·
    refine ⟨39698111963578625031820765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52930815951438166709094353 39698111963578625031820765)
    ·
      refine ⟨14886791986341984386932787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39698111963578625031820765 14886791986341984386932787)
      ·
        refine ⟨22330187979512976580399181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14886791986341984386932787 22330187979512976580399181)
        ·
          refine ⟨8373820492317366217649693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22330187979512976580399181 8373820492317366217649693)
          ·
            refine ⟨3140182684619012331618635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8373820492317366217649693 3140182684619012331618635)
            ·
              refine ⟨4710274026928518497427953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140182684619012331618635 4710274026928518497427953)
              ·
                refine ⟨3532705520196388873070965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4710274026928518497427953 3532705520196388873070965)
                ·
                  refine ⟨331191142518411456850403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3532705520196388873070965 331191142518411456850403)
                  ·
                    rfl

theorem cell21_1451233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 2, 5].length) (baseStart_1451233 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451233 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451233 prefixEnd_1451233 := by exact prefixLift 1451233
  have htrace : WordTrace (prefixWord ++ tailWord_1451233) baseStart_1451233 baseEnd_1451233 := by
    simpa [prefixWord, tailWord_1451233, baseEnd_1451233] using wordTrace_append hprefix tailTrace_1451233
  have hstable : (prefixWord ++ tailWord_1451233).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451233).length < 2 ^ (prefixWord ++ tailWord_1451233).sum := by decide
  have hdescent : baseEnd_1451233 < baseStart_1451233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451337 : List Nat := [1, 2, 1, 1, 2, 3, 3, 8]
def baseStart_1451337 : Nat := 118140960795 + 1451337 * 2 ^ 59
def prefixEnd_1451337 : Nat := 4983230072969 + 3 ^ 40 * 1451337 * 2
def baseEnd_1451337 : Nat := 110404958911776795705619

theorem tailTrace_1451337 : CollatzResearch.WordTrace tailWord_1451337 prefixEnd_1451337 110404958911776795705619 := by
  unfold tailWord_1451337
  simp only [CollatzResearch.WordTrace]
  refine ⟨52934609143061392470880265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35289739428707594980586843 52934609143061392470880265)
  ·
    refine ⟨39700956857296044353160199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52934609143061392470880265 39700956857296044353160199)
    ·
      refine ⟨59551435285944066529740299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39700956857296044353160199 59551435285944066529740299)
      ·
        refine ⟨89327152928916099794610449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59551435285944066529740299 89327152928916099794610449)
        ·
          refine ⟨66995364696687074845957837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89327152928916099794610449 66995364696687074845957837)
          ·
            refine ⟨25123261761257653067234189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66995364696687074845957837 25123261761257653067234189)
            ·
              refine ⟨9421223160471619900212821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25123261761257653067234189 9421223160471619900212821)
              ·
                refine ⟨110404958911776795705619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9421223160471619900212821 110404958911776795705619)
                ·
                  rfl

theorem cell21_1451337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 8].length) (baseStart_1451337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451337 prefixEnd_1451337 := by exact prefixLift 1451337
  have htrace : WordTrace (prefixWord ++ tailWord_1451337) baseStart_1451337 baseEnd_1451337 := by
    simpa [prefixWord, tailWord_1451337, baseEnd_1451337] using wordTrace_append hprefix tailTrace_1451337
  have hstable : (prefixWord ++ tailWord_1451337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451337).length < 2 ^ (prefixWord ++ tailWord_1451337).sum := by decide
  have hdescent : baseEnd_1451337 < baseStart_1451337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451340 : List Nat := [2, 2, 1, 3, 2, 3, 1, 3, 4]
def baseStart_1451340 : Nat := 118140960795 + 1451340 * 2 ^ 59
def prefixEnd_1451340 : Nat := 4983230072969 + 3 ^ 40 * 1451340 * 2
def baseEnd_1451340 : Nat := 331215561376203048566851

theorem tailTrace_1451340 : CollatzResearch.WordTrace tailWord_1451340 prefixEnd_1451340 331215561376203048566851 := by
  unfold tailWord_1451340
  simp only [CollatzResearch.WordTrace]
  refine ⟨26467359281025261991619737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35289812374700349322159649 26467359281025261991619737)
  ·
    refine ⟨19850519460768946493714803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26467359281025261991619737 19850519460768946493714803)
    ·
      refine ⟨29775779191153419740572205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19850519460768946493714803 29775779191153419740572205)
      ·
        refine ⟨11165917196682532402714577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29775779191153419740572205 11165917196682532402714577)
        ·
          refine ⟨8374437897511899302035933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11165917196682532402714577 8374437897511899302035933)
          ·
            refine ⟨3140414211566962238263475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8374437897511899302035933 3140414211566962238263475)
            ·
              refine ⟨4710621317350443357395213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140414211566962238263475 4710621317350443357395213)
              ·
                refine ⟨1766482994006416259023205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4710621317350443357395213 1766482994006416259023205)
                ·
                  refine ⟨331215561376203048566851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766482994006416259023205 331215561376203048566851)
                  ·
                    rfl

theorem cell21_1451340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 3, 4].length) (baseStart_1451340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451340 prefixEnd_1451340 := by exact prefixLift 1451340
  have htrace : WordTrace (prefixWord ++ tailWord_1451340) baseStart_1451340 baseEnd_1451340 := by
    simpa [prefixWord, tailWord_1451340, baseEnd_1451340] using wordTrace_append hprefix tailTrace_1451340
  have hstable : (prefixWord ++ tailWord_1451340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451340).length < 2 ^ (prefixWord ++ tailWord_1451340).sum := by decide
  have hdescent : baseEnd_1451340 < baseStart_1451340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451374 : List Nat := [4, 1, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1451374 : Nat := 118140960795 + 1451374 * 2 ^ 59
def prefixEnd_1451374 : Nat := 4983230072969 + 3 ^ 40 * 1451374 * 2
def baseEnd_1451374 : Nat := 331223320639426545000115

theorem tailTrace_1451374 : CollatzResearch.WordTrace tailWord_1451374 prefixEnd_1451374 331223320639426545000115 := by
  unfold tailWord_1451374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6616994830490918473747147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35290639095951565193318117 6616994830490918473747147)
  ·
    refine ⟨9925492245736377710620721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6616994830490918473747147 9925492245736377710620721)
    ·
      refine ⟨7444119184302283282965541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9925492245736377710620721 7444119184302283282965541)
      ·
        refine ⟨1395772347056678115556039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7444119184302283282965541 1395772347056678115556039)
        ·
          refine ⟨2093658520585017173334059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1395772347056678115556039 2093658520585017173334059)
          ·
            refine ⟨3140487780877525760001089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2093658520585017173334059 3140487780877525760001089)
            ·
              refine ⟨2355365835658144320000817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3140487780877525760001089 2355365835658144320000817)
              ·
                refine ⟨1766524376743608240000613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355365835658144320000817 1766524376743608240000613)
                ·
                  refine ⟨331223320639426545000115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766524376743608240000613 331223320639426545000115)
                  ·
                    rfl

theorem cell21_1451374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1451374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451374 prefixEnd_1451374 := by exact prefixLift 1451374
  have htrace : WordTrace (prefixWord ++ tailWord_1451374) baseStart_1451374 baseEnd_1451374 := by
    simpa [prefixWord, tailWord_1451374, baseEnd_1451374] using wordTrace_append hprefix tailTrace_1451374
  have hstable : (prefixWord ++ tailWord_1451374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451374).length < 2 ^ (prefixWord ++ tailWord_1451374).sum := by decide
  have hdescent : baseEnd_1451374 < baseStart_1451374 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451413 : List Nat := [1, 3, 2, 1, 1, 2, 2, 9]
def baseStart_1451413 : Nat := 118140960795 + 1451413 * 2 ^ 59
def prefixEnd_1451413 : Nat := 4983230072969 + 3 ^ 40 * 1451413 * 2
def baseEnd_1451413 : Nat := 110410740323590381283345

theorem tailTrace_1451413 : CollatzResearch.WordTrace tailWord_1451413 prefixEnd_1451413 110410740323590381283345 := by
  unfold tailWord_1451413
  simp only [CollatzResearch.WordTrace]
  refine ⟨52937381090786057450646893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35291587393857371633764595 52937381090786057450646893)
  ·
    refine ⟨19851517909044771543992585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52937381090786057450646893 19851517909044771543992585)
    ·
      refine ⟨14888638431783578657994439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19851517909044771543992585 14888638431783578657994439)
      ·
        refine ⟨22332957647675367986991659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14888638431783578657994439 22332957647675367986991659)
        ·
          refine ⟨33499436471513051980487489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22332957647675367986991659 33499436471513051980487489)
          ·
            refine ⟨25124577353634788985365617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33499436471513051980487489 25124577353634788985365617)
            ·
              refine ⟨18843433015226091739024213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25124577353634788985365617 18843433015226091739024213)
              ·
                refine ⟨110410740323590381283345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18843433015226091739024213 110410740323590381283345)
                ·
                  rfl

theorem cell21_1451413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 9].length) (baseStart_1451413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451413 prefixEnd_1451413 := by exact prefixLift 1451413
  have htrace : WordTrace (prefixWord ++ tailWord_1451413) baseStart_1451413 baseEnd_1451413 := by
    simpa [prefixWord, tailWord_1451413, baseEnd_1451413] using wordTrace_append hprefix tailTrace_1451413
  have hstable : (prefixWord ++ tailWord_1451413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451413).length < 2 ^ (prefixWord ++ tailWord_1451413).sum := by decide
  have hdescent : baseEnd_1451413 < baseStart_1451413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451489 : List Nat := [1, 2, 3, 1, 2, 3, 9]
def baseStart_1451489 : Nat := 118140960795 + 1451489 * 2 ^ 59
def prefixEnd_1451489 : Nat := 4983230072969 + 3 ^ 40 * 1451489 * 2
def baseEnd_1451489 : Nat := 36805507245134655620357

theorem tailTrace_1451489 : CollatzResearch.WordTrace tailWord_1451489 prefixEnd_1451489 36805507245134655620357 := by
  unfold tailWord_1451489
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940153038510722430413521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35293435359007148286942347 52940153038510722430413521)
  ·
    refine ⟨39705114778883041822810141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52940153038510722430413521 39705114778883041822810141)
    ·
      refine ⟨14889418042081140683553803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39705114778883041822810141 14889418042081140683553803)
      ·
        refine ⟨22334127063121711025330705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14889418042081140683553803 22334127063121711025330705)
        ·
          refine ⟨16750595297341283268998029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22334127063121711025330705 16750595297341283268998029)
          ·
            refine ⟨6281473236502981225874261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16750595297341283268998029 6281473236502981225874261)
            ·
              refine ⟨36805507245134655620357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6281473236502981225874261 36805507245134655620357)
              ·
                rfl

theorem cell21_1451489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 9].length) (baseStart_1451489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451489 prefixEnd_1451489 := by exact prefixLift 1451489
  have htrace : WordTrace (prefixWord ++ tailWord_1451489) baseStart_1451489 baseEnd_1451489 := by
    simpa [prefixWord, tailWord_1451489, baseEnd_1451489] using wordTrace_append hprefix tailTrace_1451489
  have hstable : (prefixWord ++ tailWord_1451489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451489).length < 2 ^ (prefixWord ++ tailWord_1451489).sum := by decide
  have hdescent : baseEnd_1451489 < baseStart_1451489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451495 : List Nat := [1, 1, 5, 2, 1, 3, 3, 2, 3]
def baseStart_1451495 : Nat := 118140960795 + 1451495 * 2 ^ 59
def prefixEnd_1451495 : Nat := 4983230072969 + 3 ^ 40 * 1451495 * 2
def baseEnd_1451495 : Nat := 331250934487957223483201

theorem tailTrace_1451495 : CollatzResearch.WordTrace tailWord_1451495 prefixEnd_1451495 331250934487957223483201 := by
  unfold tailWord_1451495
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940371876488985455131939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35293581250992656970087959 52940371876488985455131939)
  ·
    refine ⟨79410557814733478182697909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52940371876488985455131939 79410557814733478182697909)
    ·
      refine ⟨7444739795131263579627929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79410557814733478182697909 7444739795131263579627929)
      ·
        refine ⟨5583554846348447684720947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7444739795131263579627929 5583554846348447684720947)
        ·
          refine ⟨8375332269522671527081421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5583554846348447684720947 8375332269522671527081421)
          ·
            refine ⟨3140749601071001822655533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8375332269522671527081421 3140749601071001822655533)
            ·
              refine ⟨1177781100401625683495825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3140749601071001822655533 1177781100401625683495825)
              ·
                refine ⟨883335825301219262621869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1177781100401625683495825 883335825301219262621869)
                ·
                  refine ⟨331250934487957223483201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883335825301219262621869 331250934487957223483201)
                  ·
                    rfl

theorem cell21_1451495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 3, 2, 3].length) (baseStart_1451495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451495 prefixEnd_1451495 := by exact prefixLift 1451495
  have htrace : WordTrace (prefixWord ++ tailWord_1451495) baseStart_1451495 baseEnd_1451495 := by
    simpa [prefixWord, tailWord_1451495, baseEnd_1451495] using wordTrace_append hprefix tailTrace_1451495
  have hstable : (prefixWord ++ tailWord_1451495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451495).length < 2 ^ (prefixWord ++ tailWord_1451495).sum := by decide
  have hdescent : baseEnd_1451495 < baseStart_1451495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451506 : List Nat := [3, 2, 1, 4, 1, 1, 1, 8]
def baseStart_1451506 : Nat := 118140960795 + 1451506 * 2 ^ 59
def prefixEnd_1451506 : Nat := 4983230072969 + 3 ^ 40 * 1451506 * 2
def baseEnd_1451506 : Nat := 110417814945941216266615

theorem tailTrace_1451506 : CollatzResearch.WordTrace tailWord_1451506 prefixEnd_1451506 110417814945941216266615 := by
  unfold tailWord_1451506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235193269862283583445593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35293848719632756222521581 13235193269862283583445593)
  ·
    refine ⟨9926394952396712687584195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13235193269862283583445593 9926394952396712687584195)
    ·
      refine ⟨14889592428595069031376293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9926394952396712687584195 14889592428595069031376293)
      ·
        refine ⟨2791798580361575443383055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14889592428595069031376293 2791798580361575443383055)
        ·
          refine ⟨4187697870542363165074583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791798580361575443383055 4187697870542363165074583)
          ·
            refine ⟨6281546805813544747611875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4187697870542363165074583 6281546805813544747611875)
            ·
              refine ⟨9422320208720317121417813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6281546805813544747611875 9422320208720317121417813)
              ·
                refine ⟨110417814945941216266615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9422320208720317121417813 110417814945941216266615)
                ·
                  rfl

theorem cell21_1451506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_1451506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451506 prefixEnd_1451506 := by exact prefixLift 1451506
  have htrace : WordTrace (prefixWord ++ tailWord_1451506) baseStart_1451506 baseEnd_1451506 := by
    simpa [prefixWord, tailWord_1451506, baseEnd_1451506] using wordTrace_append hprefix tailTrace_1451506
  have hstable : (prefixWord ++ tailWord_1451506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451506).length < 2 ^ (prefixWord ++ tailWord_1451506).sum := by decide
  have hdescent : baseEnd_1451506 < baseStart_1451506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451509 : List Nat := [1, 3, 5, 1, 1, 2, 1, 3, 4]
def baseStart_1451509 : Nat := 118140960795 + 1451509 * 2 ^ 59
def prefixEnd_1451509 : Nat := 4983230072969 + 3 ^ 40 * 1451509 * 2
def baseEnd_1451509 : Nat := 331254129478696310249839

theorem tailTrace_1451509 : CollatzResearch.WordTrace tailWord_1451509 prefixEnd_1451509 331254129478696310249839 := by
  unfold tailWord_1451509
  simp only [CollatzResearch.WordTrace]
  refine ⟨52940882498438265846141581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35293921665625510564094387 52940882498438265846141581)
  ·
    refine ⟨19852830936914349692303093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52940882498438265846141581 19852830936914349692303093)
    ·
      refine ⟨1861202900335720283653415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19852830936914349692303093 1861202900335720283653415)
      ·
        refine ⟨2791804350503580425480123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1861202900335720283653415 2791804350503580425480123)
        ·
          refine ⟨4187706525755370638220185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791804350503580425480123 4187706525755370638220185)
          ·
            refine ⟨3140779894316527978665139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4187706525755370638220185 3140779894316527978665139)
            ·
              refine ⟨4711169841474791967997709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3140779894316527978665139 4711169841474791967997709)
              ·
                refine ⟨1766688690553046987999141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4711169841474791967997709 1766688690553046987999141)
                ·
                  refine ⟨331254129478696310249839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766688690553046987999141 331254129478696310249839)
                  ·
                    rfl

theorem cell21_1451509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 3, 4].length) (baseStart_1451509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451509 prefixEnd_1451509 := by exact prefixLift 1451509
  have htrace : WordTrace (prefixWord ++ tailWord_1451509) baseStart_1451509 baseEnd_1451509 := by
    simpa [prefixWord, tailWord_1451509, baseEnd_1451509] using wordTrace_append hprefix tailTrace_1451509
  have hstable : (prefixWord ++ tailWord_1451509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451509).length < 2 ^ (prefixWord ++ tailWord_1451509).sum := by decide
  have hdescent : baseEnd_1451509 < baseStart_1451509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451537 : List Nat := [1, 2, 2, 1, 1, 2, 4, 5, 3]
def baseStart_1451537 : Nat := 118140960795 + 1451537 * 2 ^ 59
def prefixEnd_1451537 : Nat := 4983230072969 + 3 ^ 40 * 1451537 * 2
def baseEnd_1451537 : Nat := 331260519460174483783115

theorem tailTrace_1451537 : CollatzResearch.WordTrace tailWord_1451537 prefixEnd_1451537 331260519460174483783115 := by
  unfold tailWord_1451537
  simp only [CollatzResearch.WordTrace]
  refine ⟨52941903742336826628160865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35294602494891217752107243 52941903742336826628160865)
  ·
    refine ⟨39706427806752619971120649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52941903742336826628160865 39706427806752619971120649)
    ·
      refine ⟨29779820855064464978340487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39706427806752619971120649 29779820855064464978340487)
      ·
        refine ⟨44669731282596697467510731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29779820855064464978340487 44669731282596697467510731)
        ·
          refine ⟨67004596923895046201266097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44669731282596697467510731 67004596923895046201266097)
          ·
            refine ⟨50253447692921284650949573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67004596923895046201266097 50253447692921284650949573)
            ·
              refine ⟨9422521442422740872053045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50253447692921284650949573 9422521442422740872053045)
              ·
                refine ⟨883361385227131956754973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9422521442422740872053045 883361385227131956754973)
                ·
                  refine ⟨331260519460174483783115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883361385227131956754973 331260519460174483783115)
                  ·
                    rfl

theorem cell21_1451537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 5, 3].length) (baseStart_1451537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451537 prefixEnd_1451537 := by exact prefixLift 1451537
  have htrace : WordTrace (prefixWord ++ tailWord_1451537) baseStart_1451537 baseEnd_1451537 := by
    simpa [prefixWord, tailWord_1451537, baseEnd_1451537] using wordTrace_append hprefix tailTrace_1451537
  have hstable : (prefixWord ++ tailWord_1451537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451537).length < 2 ^ (prefixWord ++ tailWord_1451537).sum := by decide
  have hdescent : baseEnd_1451537 < baseStart_1451537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451551 : List Nat := [1, 1, 2, 4, 1, 1, 3, 4, 4]
def baseStart_1451551 : Nat := 118140960795 + 1451551 * 2 ^ 59
def prefixEnd_1451551 : Nat := 4983230072969 + 3 ^ 40 * 1451551 * 2
def baseEnd_1451551 : Nat := 331263714450913570549753

theorem tailTrace_1451551 : CollatzResearch.WordTrace tailWord_1451551 prefixEnd_1451551 331263714450913570549753 := by
  unfold tailWord_1451551
  simp only [CollatzResearch.WordTrace]
  refine ⟨52942414364286107019170507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35294942909524071346113671 52942414364286107019170507)
  ·
    refine ⟨79413621546429160528755761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52942414364286107019170507 79413621546429160528755761)
    ·
      refine ⟨59560216159821870396566821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79413621546429160528755761 59560216159821870396566821)
      ·
        refine ⟨11167540529966600699356279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59560216159821870396566821 11167540529966600699356279)
        ·
          refine ⟨16751310794949901049034419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11167540529966600699356279 16751310794949901049034419)
          ·
            refine ⟨25126966192424851573551629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16751310794949901049034419 25126966192424851573551629)
            ·
              refine ⟨9422612322159319340081861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25126966192424851573551629 9422612322159319340081861)
              ·
                refine ⟨1766739810404872376265349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9422612322159319340081861 1766739810404872376265349)
                ·
                  refine ⟨331263714450913570549753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766739810404872376265349 331263714450913570549753)
                  ·
                    rfl

theorem cell21_1451551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4, 4].length) (baseStart_1451551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451551 prefixEnd_1451551 := by exact prefixLift 1451551
  have htrace : WordTrace (prefixWord ++ tailWord_1451551) baseStart_1451551 baseEnd_1451551 := by
    simpa [prefixWord, tailWord_1451551, baseEnd_1451551] using wordTrace_append hprefix tailTrace_1451551
  have hstable : (prefixWord ++ tailWord_1451551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451551).length < 2 ^ (prefixWord ++ tailWord_1451551).sum := by decide
  have hdescent : baseEnd_1451551 < baseStart_1451551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451641 : List Nat := [1, 2, 1, 3, 3, 1, 3, 7]
def baseStart_1451641 : Nat := 118140960795 + 1451641 * 2 ^ 59
def prefixEnd_1451641 : Nat := 4983230072969 + 3 ^ 40 * 1451641 * 2
def baseEnd_1451641 : Nat := 110428084559031138016523

theorem tailTrace_1451641 : CollatzResearch.WordTrace tailWord_1451641 prefixEnd_1451641 110428084559031138016523 := by
  unfold tailWord_1451641
  simp only [CollatzResearch.WordTrace]
  refine ⟨52945696933960052389946777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35297131289306701593297851 52945696933960052389946777)
  ·
    refine ⟨39709272700470039292460083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52945696933960052389946777 39709272700470039292460083)
    ·
      refine ⟨59563909050705058938690125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39709272700470039292460083 59563909050705058938690125)
      ·
        refine ⟨22336465894014397102008797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59563909050705058938690125 22336465894014397102008797)
        ·
          refine ⟨8376174710255398913253299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22336465894014397102008797 8376174710255398913253299)
          ·
            refine ⟨12564262065383098369879949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376174710255398913253299 12564262065383098369879949)
            ·
              refine ⟨4711598274518661888704981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12564262065383098369879949 4711598274518661888704981)
              ·
                refine ⟨110428084559031138016523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4711598274518661888704981 110428084559031138016523)
                ·
                  rfl

theorem cell21_1451641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 7].length) (baseStart_1451641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451641 prefixEnd_1451641 := by exact prefixLift 1451641
  have htrace : WordTrace (prefixWord ++ tailWord_1451641) baseStart_1451641 baseEnd_1451641 := by
    simpa [prefixWord, tailWord_1451641, baseEnd_1451641] using wordTrace_append hprefix tailTrace_1451641
  have hstable : (prefixWord ++ tailWord_1451641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451641).length < 2 ^ (prefixWord ++ tailWord_1451641).sum := by decide
  have hdescent : baseEnd_1451641 < baseStart_1451641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451658 : List Nat := [3, 1, 2, 3, 2, 3, 7]
def baseStart_1451658 : Nat := 118140960795 + 1451658 * 2 ^ 59
def prefixEnd_1451658 : Nat := 4983230072969 + 3 ^ 40 * 1451658 * 2
def baseEnd_1451658 : Nat := 36809792589856129140689

theorem tailTrace_1451658 : CollatzResearch.WordTrace tailWord_1451658 prefixEnd_1451658 36809792589856129140689 := by
  unfold tailWord_1451658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13236579243724616073328907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35297544649932309528877085 13236579243724616073328907)
  ·
    refine ⟨19854868865586924109993361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13236579243724616073328907 19854868865586924109993361)
    ·
      refine ⟨14891151649190193082495021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19854868865586924109993361 14891151649190193082495021)
      ·
        refine ⟨5584181868446322405935633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14891151649190193082495021 5584181868446322405935633)
        ·
          refine ⟨4188136401334741804451725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5584181868446322405935633 4188136401334741804451725)
          ·
            refine ⟨1570551150500528176669397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4188136401334741804451725 1570551150500528176669397)
            ·
              refine ⟨36809792589856129140689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1570551150500528176669397 36809792589856129140689)
              ·
                rfl

theorem cell21_1451658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 3, 7].length) (baseStart_1451658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451658 prefixEnd_1451658 := by exact prefixLift 1451658
  have htrace : WordTrace (prefixWord ++ tailWord_1451658) baseStart_1451658 baseEnd_1451658 := by
    simpa [prefixWord, tailWord_1451658, baseEnd_1451658] using wordTrace_append hprefix tailTrace_1451658
  have hstable : (prefixWord ++ tailWord_1451658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451658).length < 2 ^ (prefixWord ++ tailWord_1451658).sum := by decide
  have hdescent : baseEnd_1451658 < baseStart_1451658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451678 : List Nat := [4, 3, 1, 1, 1, 4, 2, 1, 4]
def baseStart_1451678 : Nat := 118140960795 + 1451678 * 2 ^ 59
def prefixEnd_1451678 : Nat := 4983230072969 + 3 ^ 40 * 1451678 * 2
def baseEnd_1451678 : Nat := 331292697581189571932827

theorem tailTrace_1451678 : CollatzResearch.WordTrace tailWord_1451678 prefixEnd_1451678 331292697581189571932827 := by
  unfold tailWord_1451678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618380804353250963630461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35298030956550671806029125 6618380804353250963630461)
  ·
    refine ⟨2481892801632469111361423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6618380804353250963630461 2481892801632469111361423)
    ·
      refine ⟨3722839202448703667042135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481892801632469111361423 3722839202448703667042135)
      ·
        refine ⟨5584258803673055500563203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722839202448703667042135 5584258803673055500563203)
        ·
          refine ⟨8376388205509583250844805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5584258803673055500563203 8376388205509583250844805)
          ·
            refine ⟨1570572788533046859533401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8376388205509583250844805 1570572788533046859533401)
            ·
              refine ⟨1177929591399785144650051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1570572788533046859533401 1177929591399785144650051)
              ·
                refine ⟨1766894387099677716975077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177929591399785144650051 1766894387099677716975077)
                ·
                  refine ⟨331292697581189571932827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1766894387099677716975077 331292697581189571932827)
                  ·
                    rfl

theorem cell21_1451678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_1451678 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451678 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451678 prefixEnd_1451678 := by exact prefixLift 1451678
  have htrace : WordTrace (prefixWord ++ tailWord_1451678) baseStart_1451678 baseEnd_1451678 := by
    simpa [prefixWord, tailWord_1451678, baseEnd_1451678] using wordTrace_append hprefix tailTrace_1451678
  have hstable : (prefixWord ++ tailWord_1451678).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451678).length < 2 ^ (prefixWord ++ tailWord_1451678).sum := by decide
  have hdescent : baseEnd_1451678 < baseStart_1451678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451748 : List Nat := [2, 3, 1, 1, 1, 3, 3, 2, 5]
def baseStart_1451748 : Nat := 118140960795 + 1451748 * 2 ^ 59
def prefixEnd_1451748 : Nat := 4983230072969 + 3 ^ 40 * 1451748 * 2
def baseEnd_1451748 : Nat := 331308672534885005766017

theorem tailTrace_1451748 : CollatzResearch.WordTrace tailWord_1451748 prefixEnd_1451748 331308672534885005766017 := by
  unfold tailWord_1451748
  simp only [CollatzResearch.WordTrace]
  refine ⟨26474799772286204832045949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35299733029714939776061265 26474799772286204832045949)
  ·
    refine ⟨9928049914607326812017231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26474799772286204832045949 9928049914607326812017231)
    ·
      refine ⟨14892074871910990218025847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9928049914607326812017231 14892074871910990218025847)
      ·
        refine ⟨22338112307866485327038771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14892074871910990218025847 22338112307866485327038771)
        ·
          refine ⟨33507168461799727990558157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22338112307866485327038771 33507168461799727990558157)
          ·
            refine ⟨12565188173174897996459309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33507168461799727990558157 12565188173174897996459309)
            ·
              refine ⟨4711945564940586748672241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12565188173174897996459309 4711945564940586748672241)
              ·
                refine ⟨3533959173705440061504181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4711945564940586748672241 3533959173705440061504181)
                ·
                  refine ⟨331308672534885005766017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3533959173705440061504181 331308672534885005766017)
                  ·
                    rfl

theorem cell21_1451748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_1451748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451748 prefixEnd_1451748 := by exact prefixLift 1451748
  have htrace : WordTrace (prefixWord ++ tailWord_1451748) baseStart_1451748 baseEnd_1451748 := by
    simpa [prefixWord, tailWord_1451748, baseEnd_1451748] using wordTrace_append hprefix tailTrace_1451748
  have hstable : (prefixWord ++ tailWord_1451748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451748).length < 2 ^ (prefixWord ++ tailWord_1451748).sum := by decide
  have hdescent : baseEnd_1451748 < baseStart_1451748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451779 : List Nat := [1, 1, 1, 3, 2, 2, 5, 2, 4]
def baseStart_1451779 : Nat := 118140960795 + 1451779 * 2 ^ 59
def prefixEnd_1451779 : Nat := 4983230072969 + 3 ^ 40 * 1451779 * 2
def baseEnd_1451779 : Nat := 331315747157235840749287

theorem tailTrace_1451779 : CollatzResearch.WordTrace tailWord_1451779 prefixEnd_1451779 331315747157235840749287 := by
  unfold tailWord_1451779
  simp only [CollatzResearch.WordTrace]
  refine ⟨52950730207460101958470391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35300486804973401305646927 52950730207460101958470391)
  ·
    refine ⟨79426095311190152937705587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52950730207460101958470391 79426095311190152937705587)
    ·
      refine ⟨119139142966785229406558381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79426095311190152937705587 119139142966785229406558381)
      ·
        refine ⟨44677178612544461027459393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119139142966785229406558381 44677178612544461027459393)
        ·
          refine ⟨33507883959408345770594545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44677178612544461027459393 33507883959408345770594545)
          ·
            refine ⟨25130912969556259327945909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33507883959408345770594545 25130912969556259327945909)
            ·
              refine ⟨2356023090895899311994929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25130912969556259327945909 2356023090895899311994929)
              ·
                refine ⟨1767017318171924483996197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2356023090895899311994929 1767017318171924483996197)
                ·
                  refine ⟨331315747157235840749287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1767017318171924483996197 331315747157235840749287)
                  ·
                    rfl

theorem cell21_1451779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 4].length) (baseStart_1451779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451779 prefixEnd_1451779 := by exact prefixLift 1451779
  have htrace : WordTrace (prefixWord ++ tailWord_1451779) baseStart_1451779 baseEnd_1451779 := by
    simpa [prefixWord, tailWord_1451779, baseEnd_1451779] using wordTrace_append hprefix tailTrace_1451779
  have hstable : (prefixWord ++ tailWord_1451779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451779).length < 2 ^ (prefixWord ++ tailWord_1451779).sum := by decide
  have hdescent : baseEnd_1451779 < baseStart_1451779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451976 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 5]
def baseStart_1451976 : Nat := 118140960795 + 1451976 * 2 ^ 59
def prefixEnd_1451976 : Nat := 4983230072969 + 3 ^ 40 * 1451976 * 2
def baseEnd_1451976 : Nat := 331360705241207275965551

theorem tailTrace_1451976 : CollatzResearch.WordTrace tailWord_1451976 prefixEnd_1451976 331360705241207275965551 := by
  unfold tailWord_1451976
  simp only [CollatzResearch.WordTrace]
  refine ⟨26478957693873202301695891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35305276925164269735594521 26478957693873202301695891)
  ·
    refine ⟨39718436540809803452543837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26478957693873202301695891 39718436540809803452543837)
    ·
      refine ⟨14894413702803676294703939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39718436540809803452543837 14894413702803676294703939)
      ·
        refine ⟨22341620554205514442055909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14894413702803676294703939 22341620554205514442055909)
        ·
          refine ⟨4189053853913533957885483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22341620554205514442055909 4189053853913533957885483)
          ·
            refine ⟨6283580780870300936828225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189053853913533957885483 6283580780870300936828225)
            ·
              refine ⟨4712685585652725702621169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6283580780870300936828225 4712685585652725702621169)
              ·
                refine ⟨3534514189239544276965877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4712685585652725702621169 3534514189239544276965877)
                ·
                  refine ⟨331360705241207275965551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534514189239544276965877 331360705241207275965551)
                  ·
                    rfl

theorem cell21_1451976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 5].length) (baseStart_1451976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451976 prefixEnd_1451976 := by exact prefixLift 1451976
  have htrace : WordTrace (prefixWord ++ tailWord_1451976) baseStart_1451976 baseEnd_1451976 := by
    simpa [prefixWord, tailWord_1451976, baseEnd_1451976] using wordTrace_append hprefix tailTrace_1451976
  have hstable : (prefixWord ++ tailWord_1451976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451976).length < 2 ^ (prefixWord ++ tailWord_1451976).sum := by decide
  have hdescent : baseEnd_1451976 < baseStart_1451976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1451996 : List Nat := [2, 2, 6, 1, 1, 2, 7]
def baseStart_1451996 : Nat := 118140960795 + 1451996 * 2 ^ 59
def prefixEnd_1451996 : Nat := 4983230072969 + 3 ^ 40 * 1451996 * 2
def baseEnd_1451996 : Nat := 36818363279299076181353

theorem tailTrace_1451996 : CollatzResearch.WordTrace tailWord_1451996 prefixEnd_1451996 36818363279299076181353 := by
  unfold tailWord_1451996
  simp only [CollatzResearch.WordTrace]
  refine ⟨26479322423836974009559921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35305763231782632012746561 26479322423836974009559921)
  ·
    refine ⟨19859491817877730507169941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26479322423836974009559921 19859491817877730507169941)
    ·
      refine ⟨930913678963018617523591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19859491817877730507169941 930913678963018617523591)
      ·
        refine ⟨1396370518444527926285387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930913678963018617523591 1396370518444527926285387)
        ·
          refine ⟨2094555777666791889428081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396370518444527926285387 2094555777666791889428081)
          ·
            refine ⟨1570916833250093917071061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2094555777666791889428081 1570916833250093917071061)
            ·
              refine ⟨36818363279299076181353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1570916833250093917071061 36818363279299076181353)
              ·
                rfl

theorem cell21_1451996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 2, 7].length) (baseStart_1451996 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1451996 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1451996 prefixEnd_1451996 := by exact prefixLift 1451996
  have htrace : WordTrace (prefixWord ++ tailWord_1451996) baseStart_1451996 baseEnd_1451996 := by
    simpa [prefixWord, tailWord_1451996, baseEnd_1451996] using wordTrace_append hprefix tailTrace_1451996
  have hstable : (prefixWord ++ tailWord_1451996).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1451996).length < 2 ^ (prefixWord ++ tailWord_1451996).sum := by decide
  have hdescent : baseEnd_1451996 < baseStart_1451996 := by decide
  rcases family_descends (prefixWord ++ tailWord_1451996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452010 : List Nat := [3, 1, 3, 1, 2, 1, 5, 2, 3]
def baseStart_1452010 : Nat := 118140960795 + 1452010 * 2 ^ 59
def prefixEnd_1452010 : Nat := 4983230072969 + 3 ^ 40 * 1452010 * 2
def baseEnd_1452010 : Nat := 331368464504430772398815

theorem tailTrace_1452010 : CollatzResearch.WordTrace tailWord_1452010 prefixEnd_1452010 331368464504430772398815 := by
  unfold tailWord_1452010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13239788867405807102532371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35306103646415485606752989 13239788867405807102532371)
  ·
    refine ⟨19859683301108710653798557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13239788867405807102532371 19859683301108710653798557)
    ·
      refine ⟨7447381237915766495174459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19859683301108710653798557 7447381237915766495174459)
      ·
        refine ⟨11171071856873649742761689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7447381237915766495174459 11171071856873649742761689)
        ·
          refine ⟨8378303892655237307071267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11171071856873649742761689 8378303892655237307071267)
          ·
            refine ⟨12567455838982855960606901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8378303892655237307071267 12567455838982855960606901)
            ·
              refine ⟨1178198984904642746306897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12567455838982855960606901 1178198984904642746306897)
              ·
                refine ⟨883649238678482059730173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178198984904642746306897 883649238678482059730173)
                ·
                  refine ⟨331368464504430772398815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883649238678482059730173 331368464504430772398815)
                  ·
                    rfl

theorem cell21_1452010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 3].length) (baseStart_1452010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452010 prefixEnd_1452010 := by exact prefixLift 1452010
  have htrace : WordTrace (prefixWord ++ tailWord_1452010) baseStart_1452010 baseEnd_1452010 := by
    simpa [prefixWord, tailWord_1452010, baseEnd_1452010] using wordTrace_append hprefix tailTrace_1452010
  have hstable : (prefixWord ++ tailWord_1452010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452010).length < 2 ^ (prefixWord ++ tailWord_1452010).sum := by decide
  have hdescent : baseEnd_1452010 < baseStart_1452010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452035 : List Nat := [1, 1, 1, 3, 2, 1, 1, 6, 5]
def baseStart_1452035 : Nat := 118140960795 + 1452035 * 2 ^ 59
def prefixEnd_1452035 : Nat := 4983230072969 + 3 ^ 40 * 1452035 * 2
def baseEnd_1452035 : Nat := 331374169845036284482097

theorem tailTrace_1452035 : CollatzResearch.WordTrace tailWord_1452035 prefixEnd_1452035 331374169845036284482097 := by
  unfold tailWord_1452035
  simp only [CollatzResearch.WordTrace]
  refine ⟨52960067294532657679789559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35306711529688438453193039 52960067294532657679789559)
  ·
    refine ⟨79440100941798986519684339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52960067294532657679789559 79440100941798986519684339)
    ·
      refine ⟨119160151412698479779526509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79440100941798986519684339 119160151412698479779526509)
      ·
        refine ⟨44685056779761929917322441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119160151412698479779526509 44685056779761929917322441)
        ·
          refine ⟨33513792584821447437991831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44685056779761929917322441 33513792584821447437991831)
          ·
            refine ⟨50270688877232171156987747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33513792584821447437991831 50270688877232171156987747)
            ·
              refine ⟨75406033315848256735481621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50270688877232171156987747 75406033315848256735481621)
              ·
                refine ⟨3534657811680387034475701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 75406033315848256735481621 3534657811680387034475701)
                ·
                  refine ⟨331374169845036284482097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534657811680387034475701 331374169845036284482097)
                  ·
                    rfl

theorem cell21_1452035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 6, 5].length) (baseStart_1452035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452035 prefixEnd_1452035 := by exact prefixLift 1452035
  have htrace : WordTrace (prefixWord ++ tailWord_1452035) baseStart_1452035 baseEnd_1452035 := by
    simpa [prefixWord, tailWord_1452035, baseEnd_1452035] using wordTrace_append hprefix tailTrace_1452035
  have hstable : (prefixWord ++ tailWord_1452035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452035).length < 2 ^ (prefixWord ++ tailWord_1452035).sum := by decide
  have hdescent : baseEnd_1452035 < baseStart_1452035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452069 : List Nat := [1, 3, 1, 2, 2, 4, 1, 4, 3]
def baseStart_1452069 : Nat := 118140960795 + 1452069 * 2 ^ 59
def prefixEnd_1452069 : Nat := 4983230072969 + 3 ^ 40 * 1452069 * 2
def baseEnd_1452069 : Nat := 331381929108259780915361

theorem tailTrace_1452069 : CollatzResearch.WordTrace tailWord_1452069 prefixEnd_1452069 331381929108259780915361 := by
  unfold tailWord_1452069
  simp only [CollatzResearch.WordTrace]
  refine ⟨52961307376409481486527261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35307538250939654324351507 52961307376409481486527261)
  ·
    refine ⟨19860490266153555557447723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52961307376409481486527261 19860490266153555557447723)
    ·
      refine ⟨29790735399230333336171585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19860490266153555557447723 29790735399230333336171585)
      ·
        refine ⟨22343051549422750002128689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29790735399230333336171585 22343051549422750002128689)
        ·
          refine ⟨16757288662067062501596517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22343051549422750002128689 16757288662067062501596517)
          ·
            refine ⟨3141991624137574219049347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16757288662067062501596517 3141991624137574219049347)
            ·
              refine ⟨4712987436206361328574021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3141991624137574219049347 4712987436206361328574021)
              ·
                refine ⟨883685144288692749107629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4712987436206361328574021 883685144288692749107629)
                ·
                  refine ⟨331381929108259780915361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883685144288692749107629 331381929108259780915361)
                  ·
                    rfl

theorem cell21_1452069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_1452069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452069 prefixEnd_1452069 := by exact prefixLift 1452069
  have htrace : WordTrace (prefixWord ++ tailWord_1452069) baseStart_1452069 baseEnd_1452069 := by
    simpa [prefixWord, tailWord_1452069, baseEnd_1452069] using wordTrace_append hprefix tailTrace_1452069
  have hstable : (prefixWord ++ tailWord_1452069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452069).length < 2 ^ (prefixWord ++ tailWord_1452069).sum := by decide
  have hdescent : baseEnd_1452069 < baseStart_1452069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452072 : List Nat := [2, 1, 5, 3, 2, 1, 1, 6]
def baseStart_1452072 : Nat := 118140960795 + 1452072 * 2 ^ 59
def prefixEnd_1452072 : Nat := 4983230072969 + 3 ^ 40 * 1452072 * 2
def baseEnd_1452072 : Nat := 110460871249710814121785

theorem tailTrace_1452072 : CollatzResearch.WordTrace tailWord_1452072 prefixEnd_1452072 110460871249710814121785 := by
  unfold tailWord_1452072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26480708397699306499443235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35307611196932408665924313 26480708397699306499443235)
  ·
    refine ⟨39721062596548959749164853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26480708397699306499443235 39721062596548959749164853)
    ·
      refine ⟨3723849618426464976484205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39721062596548959749164853 3723849618426464976484205)
      ·
        refine ⟨1396443606909924366181577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3723849618426464976484205 1396443606909924366181577)
        ·
          refine ⟨1047332705182443274636183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1396443606909924366181577 1047332705182443274636183)
          ·
            refine ⟨1570999057773664911954275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1047332705182443274636183 1570999057773664911954275)
            ·
              refine ⟨2356498586660497367931413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570999057773664911954275 2356498586660497367931413)
              ·
                refine ⟨110460871249710814121785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2356498586660497367931413 110460871249710814121785)
                ·
                  rfl

theorem cell21_1452072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 6].length) (baseStart_1452072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452072 prefixEnd_1452072 := by exact prefixLift 1452072
  have htrace : WordTrace (prefixWord ++ tailWord_1452072) baseStart_1452072 baseEnd_1452072 := by
    simpa [prefixWord, tailWord_1452072, baseEnd_1452072] using wordTrace_append hprefix tailTrace_1452072
  have hstable : (prefixWord ++ tailWord_1452072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452072).length < 2 ^ (prefixWord ++ tailWord_1452072).sum := by decide
  have hdescent : baseEnd_1452072 < baseStart_1452072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452128 : List Nat := [2, 1, 1, 3, 2, 4, 2, 1, 5]
def baseStart_1452128 : Nat := 118140960795 + 1452128 * 2 ^ 59
def prefixEnd_1452128 : Nat := 4983230072969 + 3 ^ 40 * 1452128 * 2
def baseEnd_1452128 : Nat := 331395393712088789431907

theorem tailTrace_1452128 : CollatzResearch.WordTrace tailWord_1452128 prefixEnd_1452128 331395393712088789431907 := by
  unfold tailWord_1452128
  simp only [CollatzResearch.WordTrace]
  refine ⟨26481729641597867281462519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35308972855463823041950025 26481729641597867281462519)
  ·
    refine ⟨39722594462396800922193779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26481729641597867281462519 39722594462396800922193779)
    ·
      refine ⟨59583891693595201383290669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39722594462396800922193779 59583891693595201383290669)
      ·
        refine ⟨22343959385098200518734001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59583891693595201383290669 22343959385098200518734001)
        ·
          refine ⟨16757969538823650389050501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22343959385098200518734001 16757969538823650389050501)
          ·
            refine ⟨3142119288529434447946969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16757969538823650389050501 3142119288529434447946969)
            ·
              refine ⟨2356589466397075835960227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3142119288529434447946969 2356589466397075835960227)
              ·
                refine ⟨3534884199595613753940341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2356589466397075835960227 3534884199595613753940341)
                ·
                  refine ⟨331395393712088789431907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3534884199595613753940341 331395393712088789431907)
                  ·
                    rfl

theorem cell21_1452128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 1, 5].length) (baseStart_1452128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452128 prefixEnd_1452128 := by exact prefixLift 1452128
  have htrace : WordTrace (prefixWord ++ tailWord_1452128) baseStart_1452128 baseEnd_1452128 := by
    simpa [prefixWord, tailWord_1452128, baseEnd_1452128] using wordTrace_append hprefix tailTrace_1452128
  have hstable : (prefixWord ++ tailWord_1452128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452128).length < 2 ^ (prefixWord ++ tailWord_1452128).sum := by decide
  have hdescent : baseEnd_1452128 < baseStart_1452128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452238 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 3]
def baseStart_1452238 : Nat := 118140960795 + 1452238 * 2 ^ 59
def prefixEnd_1452238 : Nat := 4983230072969 + 3 ^ 40 * 1452238 * 2
def baseEnd_1452238 : Nat := 331420497210753042598349

theorem tailTrace_1452238 : CollatzResearch.WordTrace tailWord_1452238 prefixEnd_1452238 331420497210753042598349 := by
  unfold tailWord_1452238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6620933914099652918678671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35311647541864815566286245 6620933914099652918678671)
  ·
    refine ⟨9931400871149479378018007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6620933914099652918678671 9931400871149479378018007)
    ·
      refine ⟨14897101306724219067027011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9931400871149479378018007 14897101306724219067027011)
      ·
        refine ⟨22345651960086328600540517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14897101306724219067027011 22345651960086328600540517)
        ·
          refine ⟨4189809742516186612601347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22345651960086328600540517 4189809742516186612601347)
          ·
            refine ⟨6284714613774279918902021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4189809742516186612601347 6284714613774279918902021)
            ·
              refine ⟨1178383990082677484794129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6284714613774279918902021 1178383990082677484794129)
              ·
                refine ⟨883787992562008113595597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1178383990082677484794129 883787992562008113595597)
                ·
                  refine ⟨331420497210753042598349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883787992562008113595597 331420497210753042598349)
                  ·
                    rfl

theorem cell21_1452238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_1452238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452238 prefixEnd_1452238 := by exact prefixLift 1452238
  have htrace : WordTrace (prefixWord ++ tailWord_1452238) baseStart_1452238 baseEnd_1452238 := by
    simpa [prefixWord, tailWord_1452238, baseEnd_1452238] using wordTrace_append hprefix tailTrace_1452238
  have hstable : (prefixWord ++ tailWord_1452238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452238).length < 2 ^ (prefixWord ++ tailWord_1452238).sum := by decide
  have hdescent : baseEnd_1452238 < baseStart_1452238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452325 : List Nat := [1, 3, 1, 2, 5, 1, 1, 7]
def baseStart_1452325 : Nat := 118140960795 + 1452325 * 2 ^ 59
def prefixEnd_1452325 : Nat := 4983230072969 + 3 ^ 40 * 1452325 * 2
def baseEnd_1452325 : Nat := 110480117265353408216057

theorem tailTrace_1452325 : CollatzResearch.WordTrace tailWord_1452325 prefixEnd_1452325 110480117265353408216057 := by
  unfold tailWord_1452325
  simp only [CollatzResearch.WordTrace]
  refine ⟨52970644463482037207846429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35313762975654691471897619 52970644463482037207846429)
  ·
    refine ⟨19863991673805763952942411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52970644463482037207846429 19863991673805763952942411)
    ·
      refine ⟨29795987510708645929413617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19863991673805763952942411 29795987510708645929413617)
      ·
        refine ⟨22346990633031484447060213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29795987510708645929413617 22346990633031484447060213)
        ·
          refine ⟨2095030371846701666911895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22346990633031484447060213 2095030371846701666911895)
          ·
            refine ⟨3142545557770052500367843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095030371846701666911895 3142545557770052500367843)
            ·
              refine ⟨4713818336655078750551765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3142545557770052500367843 4713818336655078750551765)
              ·
                refine ⟨110480117265353408216057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4713818336655078750551765 110480117265353408216057)
                ·
                  rfl

theorem cell21_1452325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 7].length) (baseStart_1452325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452325 prefixEnd_1452325 := by exact prefixLift 1452325
  have htrace : WordTrace (prefixWord ++ tailWord_1452325) baseStart_1452325 baseEnd_1452325 := by
    simpa [prefixWord, tailWord_1452325, baseEnd_1452325] using wordTrace_append hprefix tailTrace_1452325
  have hstable : (prefixWord ++ tailWord_1452325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452325).length < 2 ^ (prefixWord ++ tailWord_1452325).sum := by decide
  have hdescent : baseEnd_1452325 < baseStart_1452325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452505 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 8]
def baseStart_1452505 : Nat := 118140960795 + 1452505 * 2 ^ 59
def prefixEnd_1452505 : Nat := 4983230072969 + 3 ^ 40 * 1452505 * 2
def baseEnd_1452505 : Nat := 331481430248419911647803

theorem tailTrace_1452505 : CollatzResearch.WordTrace tailWord_1452505 prefixEnd_1452505 331481430248419911647803 := by
  unfold tailWord_1452505
  simp only [CollatzResearch.WordTrace]
  refine ⟨52977209602829927949398969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35318139735219951966265979 52977209602829927949398969)
  ·
    refine ⟨39732907202122445962049227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52977209602829927949398969 39732907202122445962049227)
    ·
      refine ⟨59599360803183668943073841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39732907202122445962049227 59599360803183668943073841)
      ·
        refine ⟨44699520602387751707305381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59599360803183668943073841 44699520602387751707305381)
        ·
          refine ⟨8381160112947703445119759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44699520602387751707305381 8381160112947703445119759)
          ·
            refine ⟨12571740169421555167679639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8381160112947703445119759 12571740169421555167679639)
            ·
              refine ⟨18857610254132332751519459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12571740169421555167679639 18857610254132332751519459)
              ·
                refine ⟨28286415381198499127279189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18857610254132332751519459 28286415381198499127279189)
                ·
                  refine ⟨331481430248419911647803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28286415381198499127279189 331481430248419911647803)
                  ·
                    rfl

theorem cell21_1452505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 8].length) (baseStart_1452505 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452505 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452505 prefixEnd_1452505 := by exact prefixLift 1452505
  have htrace : WordTrace (prefixWord ++ tailWord_1452505) baseStart_1452505 baseEnd_1452505 := by
    simpa [prefixWord, tailWord_1452505, baseEnd_1452505] using wordTrace_append hprefix tailTrace_1452505
  have hstable : (prefixWord ++ tailWord_1452505).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452505).length < 2 ^ (prefixWord ++ tailWord_1452505).sum := by decide
  have hdescent : baseEnd_1452505 < baseStart_1452505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452522 : List Nat := [3, 1, 3, 1, 3, 1, 2, 1, 6]
def baseStart_1452522 : Nat := 118140960795 + 1452522 * 2 ^ 59
def prefixEnd_1452522 : Nat := 4983230072969 + 3 ^ 40 * 1452522 * 2
def baseEnd_1452522 : Nat := 331485309880031659864435

theorem tailTrace_1452522 : CollatzResearch.WordTrace tailWord_1452522 prefixEnd_1452522 331485309880031659864435 := by
  unfold tailWord_1452522
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244457410942084963191955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35318553095845559901845213 13244457410942084963191955)
  ·
    refine ⟨19866686116413127444787933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13244457410942084963191955 19866686116413127444787933)
    ·
      refine ⟨7450007293654922791795475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19866686116413127444787933 7450007293654922791795475)
      ·
        refine ⟨11175010940482384187693213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7450007293654922791795475 11175010940482384187693213)
        ·
          refine ⟨4190629102680894070384955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11175010940482384187693213 4190629102680894070384955)
          ·
            refine ⟨6285943654021341105577433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4190629102680894070384955 6285943654021341105577433)
            ·
              refine ⟨4714457740516005829183075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6285943654021341105577433 4714457740516005829183075)
              ·
                refine ⟨7071686610774008743774613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4714457740516005829183075 7071686610774008743774613)
                ·
                  refine ⟨331485309880031659864435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7071686610774008743774613 331485309880031659864435)
                  ·
                    rfl

theorem cell21_1452522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_1452522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452522 prefixEnd_1452522 := by exact prefixLift 1452522
  have htrace : WordTrace (prefixWord ++ tailWord_1452522) baseStart_1452522 baseEnd_1452522 := by
    simpa [prefixWord, tailWord_1452522, baseEnd_1452522] using wordTrace_append hprefix tailTrace_1452522
  have hstable : (prefixWord ++ tailWord_1452522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452522).length < 2 ^ (prefixWord ++ tailWord_1452522).sum := by decide
  have hdescent : baseEnd_1452522 < baseStart_1452522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452525 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 5]
def baseStart_1452525 : Nat := 118140960795 + 1452525 * 2 ^ 59
def prefixEnd_1452525 : Nat := 4983230072969 + 3 ^ 40 * 1452525 * 2
def baseEnd_1452525 : Nat := 331485994520904321314429

theorem tailTrace_1452525 : CollatzResearch.WordTrace tailWord_1452525 prefixEnd_1452525 331485994520904321314429 := by
  unfold tailWord_1452525
  simp only [CollatzResearch.WordTrace]
  refine ⟨52977939062757471365127029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35318626041838314243418019 52977939062757471365127029)
  ·
    refine ⟨4966681787133512940480659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52977939062757471365127029 4966681787133512940480659)
    ·
      refine ⟨7450022680700269410720989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4966681787133512940480659 7450022680700269410720989)
      ·
        refine ⟨2793758505262601029020371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7450022680700269410720989 2793758505262601029020371)
        ·
          refine ⟨4190637757893901543530557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2793758505262601029020371 4190637757893901543530557)
          ·
            refine ⟨1571489159210213078823959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4190637757893901543530557 1571489159210213078823959)
            ·
              refine ⟨2357233738815319618235939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571489159210213078823959 2357233738815319618235939)
              ·
                refine ⟨3535850608222979427353909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357233738815319618235939 3535850608222979427353909)
                ·
                  refine ⟨331485994520904321314429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3535850608222979427353909 331485994520904321314429)
                  ·
                    rfl

theorem cell21_1452525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_1452525 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452525 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452525 prefixEnd_1452525 := by exact prefixLift 1452525
  have htrace : WordTrace (prefixWord ++ tailWord_1452525) baseStart_1452525 baseEnd_1452525 := by
    simpa [prefixWord, tailWord_1452525, baseEnd_1452525] using wordTrace_append hprefix tailTrace_1452525
  have hstable : (prefixWord ++ tailWord_1452525).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452525).length < 2 ^ (prefixWord ++ tailWord_1452525).sum := by decide
  have hdescent : baseEnd_1452525 < baseStart_1452525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452536 : List Nat := [2, 1, 2, 1, 1, 4, 4, 6]
def baseStart_1452536 : Nat := 118140960795 + 1452536 * 2 ^ 59
def prefixEnd_1452536 : Nat := 4983230072969 + 3 ^ 40 * 1452536 * 2
def baseEnd_1452536 : Nat := 110496168290256915543691

theorem tailTrace_1452536 : CollatzResearch.WordTrace tailWord_1452536 prefixEnd_1452536 110496168290256915543691 := by
  unfold tailWord_1452536
  simp only [CollatzResearch.WordTrace]
  refine ⟨26489170132858810121888731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35318893510478413495851641 26489170132858810121888731)
  ·
    refine ⟨39733755199288215182833097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26489170132858810121888731 39733755199288215182833097)
    ·
      refine ⟨29800316399466161387124823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39733755199288215182833097 29800316399466161387124823)
      ·
        refine ⟨44700474599199242080687235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29800316399466161387124823 44700474599199242080687235)
        ·
          refine ⟨67050711898798863121030853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44700474599199242080687235 67050711898798863121030853)
          ·
            refine ⟨12572008481024786835193285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67050711898798863121030853 12572008481024786835193285)
            ·
              refine ⟨2357251590192147531598741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12572008481024786835193285 2357251590192147531598741)
              ·
                refine ⟨110496168290256915543691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2357251590192147531598741 110496168290256915543691)
                ·
                  rfl

theorem cell21_1452536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 4, 6].length) (baseStart_1452536 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452536 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452536 prefixEnd_1452536 := by exact prefixLift 1452536
  have htrace : WordTrace (prefixWord ++ tailWord_1452536) baseStart_1452536 baseEnd_1452536 := by
    simpa [prefixWord, tailWord_1452536, baseEnd_1452536] using wordTrace_append hprefix tailTrace_1452536
  have hstable : (prefixWord ++ tailWord_1452536).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452536).length < 2 ^ (prefixWord ++ tailWord_1452536).sum := by decide
  have hdescent : baseEnd_1452536 < baseStart_1452536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452581 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1452581 : Nat := 118140960795 + 1452581 * 2 ^ 59
def prefixEnd_1452581 : Nat := 4983230072969 + 3 ^ 40 * 1452581 * 2
def baseEnd_1452581 : Nat := 331498774483860668380981

theorem tailTrace_1452581 : CollatzResearch.WordTrace tailWord_1452581 prefixEnd_1452581 331498774483860668380981 := by
  unfold tailWord_1452581
  simp only [CollatzResearch.WordTrace]
  refine ⟨52979981550554592929165597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35319987700369728619443731 52979981550554592929165597)
  ·
    refine ⟨19867493081457972348437099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52979981550554592929165597 19867493081457972348437099)
    ·
      refine ⟨29801239622186958522655649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19867493081457972348437099 29801239622186958522655649)
      ·
        refine ⟨22350929716640218891991737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29801239622186958522655649 22350929716640218891991737)
        ·
          refine ⟨16763197287480164168993803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22350929716640218891991737 16763197287480164168993803)
          ·
            refine ⟨25144795931220246253490705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16763197287480164168993803 25144795931220246253490705)
            ·
              refine ⟨18858596948415184690118029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25144795931220246253490705 18858596948415184690118029)
              ·
                refine ⟨7071973855655694258794261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18858596948415184690118029 7071973855655694258794261)
                ·
                  refine ⟨331498774483860668380981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7071973855655694258794261 331498774483860668380981)
                  ·
                    rfl

theorem cell21_1452581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1452581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452581 prefixEnd_1452581 := by exact prefixLift 1452581
  have htrace : WordTrace (prefixWord ++ tailWord_1452581) baseStart_1452581 baseEnd_1452581 := by
    simpa [prefixWord, tailWord_1452581, baseEnd_1452581] using wordTrace_append hprefix tailTrace_1452581
  have hstable : (prefixWord ++ tailWord_1452581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452581).length < 2 ^ (prefixWord ++ tailWord_1452581).sum := by decide
  have hdescent : baseEnd_1452581 < baseStart_1452581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452643 : List Nat := [1, 1, 1, 5, 1, 2, 4, 1, 5]
def baseStart_1452643 : Nat := 118140960795 + 1452643 * 2 ^ 59
def prefixEnd_1452643 : Nat := 4983230072969 + 3 ^ 40 * 1452643 * 2
def baseEnd_1452643 : Nat := 331512923728562338347521

theorem tailTrace_1452643 : CollatzResearch.WordTrace tailWord_1452643 prefixEnd_1452643 331512923728562338347521 := by
  unfold tailWord_1452643
  simp only [CollatzResearch.WordTrace]
  refine ⟨52982242876329977517922583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35321495250886651678615055 52982242876329977517922583)
  ·
    refine ⟨79473364314494966276883875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52982242876329977517922583 79473364314494966276883875)
    ·
      refine ⟨119210046471742449415325813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79473364314494966276883875 119210046471742449415325813)
      ·
        refine ⟨11175941856725854632686795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119210046471742449415325813 11175941856725854632686795)
        ·
          refine ⟨16763912785088781949030193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11175941856725854632686795 16763912785088781949030193)
          ·
            refine ⟨12572934588816586461772645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16763912785088781949030193 12572934588816586461772645)
            ·
              refine ⟨2357425235403109961582371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12572934588816586461772645 2357425235403109961582371)
              ·
                refine ⟨3536137853104664942373557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357425235403109961582371 3536137853104664942373557)
                ·
                  refine ⟨331512923728562338347521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3536137853104664942373557 331512923728562338347521)
                  ·
                    rfl

theorem cell21_1452643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 4, 1, 5].length) (baseStart_1452643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452643 prefixEnd_1452643 := by exact prefixLift 1452643
  have htrace : WordTrace (prefixWord ++ tailWord_1452643) baseStart_1452643 baseEnd_1452643 := by
    simpa [prefixWord, tailWord_1452643, baseEnd_1452643] using wordTrace_append hprefix tailTrace_1452643
  have hstable : (prefixWord ++ tailWord_1452643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452643).length < 2 ^ (prefixWord ++ tailWord_1452643).sum := by decide
  have hdescent : baseEnd_1452643 < baseStart_1452643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452677 : List Nat := [1, 3, 1, 1, 4, 4, 1, 3, 3]
def baseStart_1452677 : Nat := 118140960795 + 1452677 * 2 ^ 59
def prefixEnd_1452677 : Nat := 4983230072969 + 3 ^ 40 * 1452677 * 2
def baseEnd_1452677 : Nat := 331520682991785834780785

theorem tailTrace_1452677 : CollatzResearch.WordTrace tailWord_1452677 prefixEnd_1452677 331520682991785834780785 := by
  unfold tailWord_1452677
  simp only [CollatzResearch.WordTrace]
  refine ⟨52983482958206801324660285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35322321972137867549773523 52983482958206801324660285)
  ·
    refine ⟨19868806109327550496747607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52983482958206801324660285 19868806109327550496747607)
    ·
      refine ⟨29803209163991325745121411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19868806109327550496747607 29803209163991325745121411)
      ·
        refine ⟨44704813745986988617682117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29803209163991325745121411 44704813745986988617682117)
        ·
          refine ⟨8382152577372560365815397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44704813745986988617682117 8382152577372560365815397)
          ·
            refine ⟨1571653608257355068590387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8382152577372560365815397 1571653608257355068590387)
            ·
              refine ⟨2357480412386032602885581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571653608257355068590387 2357480412386032602885581)
              ·
                refine ⟨884055154644762226082093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2357480412386032602885581 884055154644762226082093)
                ·
                  refine ⟨331520682991785834780785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884055154644762226082093 331520682991785834780785)
                  ·
                    rfl

theorem cell21_1452677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 3, 3].length) (baseStart_1452677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452677 prefixEnd_1452677 := by exact prefixLift 1452677
  have htrace : WordTrace (prefixWord ++ tailWord_1452677) baseStart_1452677 baseEnd_1452677 := by
    simpa [prefixWord, tailWord_1452677, baseEnd_1452677] using wordTrace_append hprefix tailTrace_1452677
  have hstable : (prefixWord ++ tailWord_1452677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452677).length < 2 ^ (prefixWord ++ tailWord_1452677).sum := by decide
  have hdescent : baseEnd_1452677 < baseStart_1452677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452705 : List Nat := [1, 2, 3, 3, 3, 1, 2, 6]
def baseStart_1452705 : Nat := 118140960795 + 1452705 * 2 ^ 59
def prefixEnd_1452705 : Nat := 4983230072969 + 3 ^ 40 * 1452705 * 2
def baseEnd_1452705 : Nat := 110509024324421336104687

theorem tailTrace_1452705 : CollatzResearch.WordTrace tailWord_1452705 prefixEnd_1452705 110509024324421336104687 := by
  unfold tailWord_1452705
  simp only [CollatzResearch.WordTrace]
  refine ⟨52984504202105362106679569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35323002801403574737786379 52984504202105362106679569)
  ·
    refine ⟨39738378151579021580009677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52984504202105362106679569 39738378151579021580009677)
    ·
      refine ⟨14901891806842133092503629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39738378151579021580009677 14901891806842133092503629)
      ·
        refine ⟨5588209427565799909688861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14901891806842133092503629 5588209427565799909688861)
        ·
          refine ⟨2095578535337174966133323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5588209427565799909688861 2095578535337174966133323)
          ·
            refine ⟨3143367803005762449199985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2095578535337174966133323 3143367803005762449199985)
            ·
              refine ⟨2357525852254321836899989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3143367803005762449199985 2357525852254321836899989)
              ·
                refine ⟨110509024324421336104687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2357525852254321836899989 110509024324421336104687)
                ·
                  rfl

theorem cell21_1452705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 6].length) (baseStart_1452705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452705 prefixEnd_1452705 := by exact prefixLift 1452705
  have htrace : WordTrace (prefixWord ++ tailWord_1452705) baseStart_1452705 baseEnd_1452705 := by
    simpa [prefixWord, tailWord_1452705, baseEnd_1452705] using wordTrace_append hprefix tailTrace_1452705
  have hstable : (prefixWord ++ tailWord_1452705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452705).length < 2 ^ (prefixWord ++ tailWord_1452705).sum := by decide
  have hdescent : baseEnd_1452705 < baseStart_1452705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452750 : List Nat := [4, 1, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1452750 : Nat := 118140960795 + 1452750 * 2 ^ 59
def prefixEnd_1452750 : Nat := 4983230072969 + 3 ^ 40 * 1452750 * 2
def baseEnd_1452750 : Nat := 331537342586353930063969

theorem tailTrace_1452750 : CollatzResearch.WordTrace tailWord_1452750 prefixEnd_1452750 331537342586353930063969 := by
  unfold tailWord_1452750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623268185867791849008463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35324096991294889861378469 6623268185867791849008463)
  ·
    refine ⟨9934902278801687773512695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6623268185867791849008463 9934902278801687773512695)
    ·
      refine ⟨14902353418202531660269043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9934902278801687773512695 14902353418202531660269043)
      ·
        refine ⟨22353530127303797490403565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902353418202531660269043 22353530127303797490403565)
        ·
          refine ⟨8382573797738924058901337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22353530127303797490403565 8382573797738924058901337)
          ·
            refine ⟨6286930348304193044176003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8382573797738924058901337 6286930348304193044176003)
            ·
              refine ⟨9430395522456289566264005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6286930348304193044176003 9430395522456289566264005)
              ·
                refine ⟨1768199160460554293674501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9430395522456289566264005 1768199160460554293674501)
                ·
                  refine ⟨331537342586353930063969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768199160460554293674501 331537342586353930063969)
                  ·
                    rfl

theorem cell21_1452750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1452750 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452750 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452750 prefixEnd_1452750 := by exact prefixLift 1452750
  have htrace : WordTrace (prefixWord ++ tailWord_1452750) baseStart_1452750 baseEnd_1452750 := by
    simpa [prefixWord, tailWord_1452750, baseEnd_1452750] using wordTrace_append hprefix tailTrace_1452750
  have hstable : (prefixWord ++ tailWord_1452750).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452750).length < 2 ^ (prefixWord ++ tailWord_1452750).sum := by decide
  have hdescent : baseEnd_1452750 < baseStart_1452750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452781 : List Nat := [1, 5, 1, 2, 1, 1, 5, 5]
def baseStart_1452781 : Nat := 118140960795 + 1452781 * 2 ^ 59
def prefixEnd_1452781 : Nat := 4983230072969 + 3 ^ 40 * 1452781 * 2
def baseEnd_1452781 : Nat := 110514805736234921682413

theorem tailTrace_1452781 : CollatzResearch.WordTrace tailWord_1452781 prefixEnd_1452781 110514805736234921682413 := by
  unfold tailWord_1452781
  simp only [CollatzResearch.WordTrace]
  refine ⟨52987276149830027086446197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35324850766553351390964131 52987276149830027086446197)
  ·
    refine ⟨4967557139046565039354331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52987276149830027086446197 4967557139046565039354331)
    ·
      refine ⟨7451335708569847559031497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4967557139046565039354331 7451335708569847559031497)
      ·
        refine ⟨5588501781427385669273623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7451335708569847559031497 5588501781427385669273623)
        ·
          refine ⟨8382752672141078503910435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588501781427385669273623 8382752672141078503910435)
          ·
            refine ⟨12574129008211617755865653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8382752672141078503910435 12574129008211617755865653)
            ·
              refine ⟨1178824594519839164612405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12574129008211617755865653 1178824594519839164612405)
              ·
                refine ⟨110514805736234921682413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1178824594519839164612405 110514805736234921682413)
                ·
                  rfl

theorem cell21_1452781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 5, 5].length) (baseStart_1452781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452781 prefixEnd_1452781 := by exact prefixLift 1452781
  have htrace : WordTrace (prefixWord ++ tailWord_1452781) baseStart_1452781 baseEnd_1452781 := by
    simpa [prefixWord, tailWord_1452781, baseEnd_1452781] using wordTrace_append hprefix tailTrace_1452781
  have hstable : (prefixWord ++ tailWord_1452781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452781).length < 2 ^ (prefixWord ++ tailWord_1452781).sum := by decide
  have hdescent : baseEnd_1452781 < baseStart_1452781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452840 : List Nat := [2, 1, 5, 1, 1, 1, 3, 7]
def baseStart_1452840 : Nat := 118140960795 + 1452840 * 2 ^ 59
def prefixEnd_1452840 : Nat := 4983230072969 + 3 ^ 40 * 1452840 * 2
def baseEnd_1452840 : Nat := 110519293937511257854595

theorem tailTrace_1452840 : CollatzResearch.WordTrace tailWord_1452840 prefixEnd_1452840 110519293937511257854595 := by
  unfold tailWord_1452840
  simp only [CollatzResearch.WordTrace]
  refine ⟨26494714028308140081421987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35326285371077520108562649 26494714028308140081421987)
  ·
    refine ⟨39742071042462210122132981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26494714028308140081421987 39742071042462210122132981)
    ·
      refine ⟨3725819160230832198949967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39742071042462210122132981 3725819160230832198949967)
      ·
        refine ⟨5588728740346248298424951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3725819160230832198949967 5588728740346248298424951)
        ·
          refine ⟨8383093110519372447637427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5588728740346248298424951 8383093110519372447637427)
          ·
            refine ⟨12574639665779058671456141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8383093110519372447637427 12574639665779058671456141)
            ·
              refine ⟨4715489874667147001796053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12574639665779058671456141 4715489874667147001796053)
              ·
                refine ⟨110519293937511257854595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4715489874667147001796053 110519293937511257854595)
                ·
                  rfl

theorem cell21_1452840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 7].length) (baseStart_1452840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452840 prefixEnd_1452840 := by exact prefixLift 1452840
  have htrace : WordTrace (prefixWord ++ tailWord_1452840) baseStart_1452840 baseEnd_1452840 := by
    simpa [prefixWord, tailWord_1452840, baseEnd_1452840] using wordTrace_append hprefix tailTrace_1452840
  have hstable : (prefixWord ++ tailWord_1452840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452840).length < 2 ^ (prefixWord ++ tailWord_1452840).sum := by decide
  have hdescent : baseEnd_1452840 < baseStart_1452840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452846 : List Nat := [4, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_1452846 : Nat := 118140960795 + 1452846 * 2 ^ 59
def prefixEnd_1452846 : Nat := 4983230072969 + 3 ^ 40 * 1452846 * 2
def baseEnd_1452846 : Nat := 331559251094279096463773

theorem tailTrace_1452846 : CollatzResearch.WordTrace tailWord_1452846 prefixEnd_1452846 331559251094279096463773 := by
  unfold tailWord_1452846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6623705861824317898445299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35326431263063028791708261 6623705861824317898445299)
  ·
    refine ⟨9935558792736476847667949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6623705861824317898445299 9935558792736476847667949)
    ·
      refine ⟨3725834547276178817875481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9935558792736476847667949 3725834547276178817875481)
      ·
        refine ⟨2794375910457134113406611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3725834547276178817875481 2794375910457134113406611)
        ·
          refine ⟨4191563865685701170109917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794375910457134113406611 4191563865685701170109917)
          ·
            refine ⟨1571836449632137938791219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4191563865685701170109917 1571836449632137938791219)
            ·
              refine ⟨2357754674448206908186829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571836449632137938791219 2357754674448206908186829)
              ·
                refine ⟨884158002918077590570061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2357754674448206908186829 884158002918077590570061)
                ·
                  refine ⟨331559251094279096463773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884158002918077590570061 331559251094279096463773)
                  ·
                    rfl

theorem cell21_1452846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_1452846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452846 prefixEnd_1452846 := by exact prefixLift 1452846
  have htrace : WordTrace (prefixWord ++ tailWord_1452846) baseStart_1452846 baseEnd_1452846 := by
    simpa [prefixWord, tailWord_1452846, baseEnd_1452846] using wordTrace_append hprefix tailTrace_1452846
  have hstable : (prefixWord ++ tailWord_1452846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452846).length < 2 ^ (prefixWord ++ tailWord_1452846).sum := by decide
  have hdescent : baseEnd_1452846 < baseStart_1452846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452877 : List Nat := [1, 6, 1, 2, 2, 2, 2, 1, 4]
def baseStart_1452877 : Nat := 118140960795 + 1452877 * 2 ^ 59
def prefixEnd_1452877 : Nat := 4983230072969 + 3 ^ 40 * 1452877 * 2
def baseEnd_1452877 : Nat := 331566325716629931447043

theorem tailTrace_1452877 : CollatzResearch.WordTrace tailWord_1452877 prefixEnd_1452877 331566325716629931447043 := by
  unfold tailWord_1452877
  simp only [CollatzResearch.WordTrace]
  refine ⟨52990777557482235481940885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35327185038321490321293923 52990777557482235481940885)
  ·
    refine ⟨2483942698006979788215979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52990777557482235481940885 2483942698006979788215979)
    ·
      refine ⟨3725914047010469682323969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2483942698006979788215979 3725914047010469682323969)
      ·
        refine ⟨2794435535257852261742977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3725914047010469682323969 2794435535257852261742977)
        ·
          refine ⟨2095826651443389196307233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2794435535257852261742977 2095826651443389196307233)
          ·
            refine ⟨1571869988582541897230425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2095826651443389196307233 1571869988582541897230425)
            ·
              refine ⟨1178902491436906422922819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1571869988582541897230425 1178902491436906422922819)
              ·
                refine ⟨1768353737155359634384229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1178902491436906422922819 1768353737155359634384229)
                ·
                  refine ⟨331566325716629931447043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768353737155359634384229 331566325716629931447043)
                  ·
                    rfl

theorem cell21_1452877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_1452877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452877 prefixEnd_1452877 := by exact prefixLift 1452877
  have htrace : WordTrace (prefixWord ++ tailWord_1452877) baseStart_1452877 baseEnd_1452877 := by
    simpa [prefixWord, tailWord_1452877, baseEnd_1452877] using wordTrace_append hprefix tailTrace_1452877
  have hstable : (prefixWord ++ tailWord_1452877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452877).length < 2 ^ (prefixWord ++ tailWord_1452877).sum := by decide
  have hdescent : baseEnd_1452877 < baseStart_1452877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1452964 : List Nat := [2, 3, 1, 2, 1, 2, 4, 3, 3]
def baseStart_1452964 : Nat := 118140960795 + 1452964 * 2 ^ 59
def prefixEnd_1452964 : Nat := 4983230072969 + 3 ^ 40 * 1452964 * 2
def baseEnd_1452964 : Nat := 331586180301937113496865

theorem tailTrace_1452964 : CollatzResearch.WordTrace tailWord_1452964 prefixEnd_1452964 331586180301937113496865 := by
  unfold tailWord_1452964
  simp only [CollatzResearch.WordTrace]
  refine ⟨26496975354083524670178973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35329300472111366226905297 26496975354083524670178973)
  ·
    refine ⟨9936365757781321751317115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26496975354083524670178973 9936365757781321751317115)
    ·
      refine ⟨14904548636671982626975673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9936365757781321751317115 14904548636671982626975673)
      ·
        refine ⟨11178411477503986970231755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14904548636671982626975673 11178411477503986970231755)
        ·
          refine ⟨16767617216255980455347633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11178411477503986970231755 16767617216255980455347633)
          ·
            refine ⟨12575712912191985341510725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16767617216255980455347633 12575712912191985341510725)
            ·
              refine ⟨2357946171035997251533261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12575712912191985341510725 2357946171035997251533261)
              ·
                refine ⟨884229814138498969324973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2357946171035997251533261 884229814138498969324973)
                ·
                  refine ⟨331586180301937113496865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884229814138498969324973 331586180301937113496865)
                  ·
                    rfl

theorem cell21_1452964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3, 3].length) (baseStart_1452964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1452964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1452964 prefixEnd_1452964 := by exact prefixLift 1452964
  have htrace : WordTrace (prefixWord ++ tailWord_1452964) baseStart_1452964 baseEnd_1452964 := by
    simpa [prefixWord, tailWord_1452964, baseEnd_1452964] using wordTrace_append hprefix tailTrace_1452964
  have hstable : (prefixWord ++ tailWord_1452964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1452964).length < 2 ^ (prefixWord ++ tailWord_1452964).sum := by decide
  have hdescent : baseEnd_1452964 < baseStart_1452964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1452964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453099 : List Nat := [1, 1, 1, 1, 2, 1, 7, 4, 3]
def baseStart_1453099 : Nat := 118140960795 + 1453099 * 2 ^ 59
def prefixEnd_1453099 : Nat := 4983230072969 + 3 ^ 40 * 1453099 * 2
def baseEnd_1453099 : Nat := 331616989141206878746589

theorem tailTrace_1453099 : CollatzResearch.WordTrace tailWord_1453099 prefixEnd_1453099 331616989141206878746589 := by
  unfold tailWord_1453099
  simp only [CollatzResearch.WordTrace]
  refine ⟨52998874562677967396522351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35332583041785311597681567 52998874562677967396522351)
  ·
    refine ⟨79498311844016951094783527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52998874562677967396522351 79498311844016951094783527)
    ·
      refine ⟨119247467766025426642175291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79498311844016951094783527 119247467766025426642175291)
      ·
        refine ⟨178871201649038139963262937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119247467766025426642175291 178871201649038139963262937)
        ·
          refine ⟨134153401236778604972447203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 178871201649038139963262937 134153401236778604972447203)
          ·
            refine ⟨201230101855167907458670805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134153401236778604972447203 201230101855167907458670805)
            ·
              refine ⟨4716330512230497831062597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 201230101855167907458670805 4716330512230497831062597)
              ·
                refine ⟨884311971043218343324237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4716330512230497831062597 884311971043218343324237)
                ·
                  refine ⟨331616989141206878746589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884311971043218343324237 331616989141206878746589)
                  ·
                    rfl

theorem cell21_1453099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4, 3].length) (baseStart_1453099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453099 prefixEnd_1453099 := by exact prefixLift 1453099
  have htrace : WordTrace (prefixWord ++ tailWord_1453099) baseStart_1453099 baseEnd_1453099 := by
    simpa [prefixWord, tailWord_1453099, baseEnd_1453099] using wordTrace_append hprefix tailTrace_1453099
  have hstable : (prefixWord ++ tailWord_1453099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453099).length < 2 ^ (prefixWord ++ tailWord_1453099).sum := by decide
  have hdescent : baseEnd_1453099 < baseStart_1453099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453133 : List Nat := [1, 6, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1453133 : Nat := 118140960795 + 1453133 * 2 ^ 59
def prefixEnd_1453133 : Nat := 4983230072969 + 3 ^ 40 * 1453133 * 2
def baseEnd_1453133 : Nat := 331624748404430375179853

theorem tailTrace_1453133 : CollatzResearch.WordTrace tailWord_1453133 prefixEnd_1453133 331624748404430375179853 := by
  unfold tailWord_1453133
  simp only [CollatzResearch.WordTrace]
  refine ⟨53000114644554791203260053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35333409763036527468840035 53000114644554791203260053)
  ·
    refine ⟨2484380373963505837652815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 53000114644554791203260053 2484380373963505837652815)
    ·
      refine ⟨3726570560945258756479223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2484380373963505837652815 3726570560945258756479223)
      ·
        refine ⟨5589855841417888134718835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3726570560945258756479223 5589855841417888134718835)
        ·
          refine ⟨8384783762126832202078253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5589855841417888134718835 8384783762126832202078253)
          ·
            refine ⟨3144293910797562075779345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8384783762126832202078253 3144293910797562075779345)
            ·
              refine ⟨2358220433098171556834509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144293910797562075779345 2358220433098171556834509)
              ·
                refine ⟨884332662411814333812941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2358220433098171556834509 884332662411814333812941)
                ·
                  refine ⟨331624748404430375179853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884332662411814333812941 331624748404430375179853)
                  ·
                    rfl

theorem cell21_1453133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1453133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453133 prefixEnd_1453133 := by exact prefixLift 1453133
  have htrace : WordTrace (prefixWord ++ tailWord_1453133) baseStart_1453133 baseEnd_1453133 := by
    simpa [prefixWord, tailWord_1453133, baseEnd_1453133] using wordTrace_append hprefix tailTrace_1453133
  have hstable : (prefixWord ++ tailWord_1453133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453133).length < 2 ^ (prefixWord ++ tailWord_1453133).sum := by decide
  have hdescent : baseEnd_1453133 < baseStart_1453133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453150 : List Nat := [4, 4, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1453150 : Nat := 118140960795 + 1453150 * 2 ^ 59
def prefixEnd_1453150 : Nat := 4983230072969 + 3 ^ 40 * 1453150 * 2
def baseEnd_1453150 : Nat := 331628628036042123396485

theorem tailTrace_1453150 : CollatzResearch.WordTrace tailWord_1453150 prefixEnd_1453150 331628628036042123396485 := by
  unfold tailWord_1453150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625091835686650388328613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35333823123662135404419269 6625091835686650388328613)
  ·
    refine ⟨1242204719191246947811615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6625091835686650388328613 1242204719191246947811615)
    ·
      refine ⟨1863307078786870421717423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242204719191246947811615 1863307078786870421717423)
      ·
        refine ⟨2794960618180305632576135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863307078786870421717423 2794960618180305632576135)
        ·
          refine ⟨4192440927270458448864203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2794960618180305632576135 4192440927270458448864203)
          ·
            refine ⟨6288661390905687673296305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192440927270458448864203 6288661390905687673296305)
            ·
              refine ⟨4716496043179265754972229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6288661390905687673296305 4716496043179265754972229)
              ·
                refine ⟨884343008096112329057293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4716496043179265754972229 884343008096112329057293)
                ·
                  refine ⟨331628628036042123396485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884343008096112329057293 331628628036042123396485)
                  ·
                    rfl

theorem cell21_1453150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1453150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453150 prefixEnd_1453150 := by exact prefixLift 1453150
  have htrace : WordTrace (prefixWord ++ tailWord_1453150) baseStart_1453150 baseEnd_1453150 := by
    simpa [prefixWord, tailWord_1453150, baseEnd_1453150] using wordTrace_append hprefix tailTrace_1453150
  have hstable : (prefixWord ++ tailWord_1453150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453150).length < 2 ^ (prefixWord ++ tailWord_1453150).sum := by decide
  have hdescent : baseEnd_1453150 < baseStart_1453150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453220 : List Nat := [2, 3, 1, 2, 3, 2, 2, 6]
def baseStart_1453220 : Nat := 118140960795 + 1453220 * 2 ^ 59
def prefixEnd_1453220 : Nat := 4983230072969 + 3 ^ 40 * 1453220 * 2
def baseEnd_1453220 : Nat := 110548200996579185743225

theorem tailTrace_1453220 : CollatzResearch.WordTrace tailWord_1453220 prefixEnd_1453220 110548200996579185743225 := by
  unfold tailWord_1453220
  simp only [CollatzResearch.WordTrace]
  refine ⟨26501643897619802530838557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35335525196826403374451409 26501643897619802530838557)
  ·
    refine ⟨9938116461607425949064459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26501643897619802530838557 9938116461607425949064459)
    ·
      refine ⟨14907174692411138923596689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9938116461607425949064459 14907174692411138923596689)
      ·
        refine ⟨11180381019308354192697517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14907174692411138923596689 11180381019308354192697517)
        ·
          refine ⟨4192642882240632822261569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11180381019308354192697517 4192642882240632822261569)
          ·
            refine ⟨3144482161680474616696177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4192642882240632822261569 3144482161680474616696177)
            ·
              refine ⟨2358361621260355962522133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3144482161680474616696177 2358361621260355962522133)
              ·
                refine ⟨110548200996579185743225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2358361621260355962522133 110548200996579185743225)
                ·
                  rfl

theorem cell21_1453220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 6].length) (baseStart_1453220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453220 prefixEnd_1453220 := by exact prefixLift 1453220
  have htrace : WordTrace (prefixWord ++ tailWord_1453220) baseStart_1453220 baseEnd_1453220 := by
    simpa [prefixWord, tailWord_1453220, baseEnd_1453220] using wordTrace_append hprefix tailTrace_1453220
  have hstable : (prefixWord ++ tailWord_1453220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453220).length < 2 ^ (prefixWord ++ tailWord_1453220).sum := by decide
  have hdescent : baseEnd_1453220 < baseStart_1453220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453223 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 4]
def baseStart_1453223 : Nat := 118140960795 + 1453223 * 2 ^ 59
def prefixEnd_1453223 : Nat := 4983230072969 + 3 ^ 40 * 1453223 * 2
def baseEnd_1453223 : Nat := 331645287630610218679669

theorem tailTrace_1453223 : CollatzResearch.WordTrace tailWord_1453223 prefixEnd_1453223 331645287630610218679669 := by
  unfold tailWord_1453223
  simp only [CollatzResearch.WordTrace]
  refine ⟨53003397214228736574036323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35335598142819157716024215 53003397214228736574036323)
  ·
    refine ⟨79505095821343104861054485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53003397214228736574036323 79505095821343104861054485)
    ·
      refine ⟨3726801366625458040361929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79505095821343104861054485 3726801366625458040361929)
      ·
        refine ⟨2795101024969093530271447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3726801366625458040361929 2795101024969093530271447)
        ·
          refine ⟨4192651537453640295407171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2795101024969093530271447 4192651537453640295407171)
          ·
            refine ⟨6288977306180460443110757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192651537453640295407171 6288977306180460443110757)
            ·
              refine ⟨1179183244908836333083267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6288977306180460443110757 1179183244908836333083267)
              ·
                refine ⟨1768774867363254499624901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1179183244908836333083267 1768774867363254499624901)
                ·
                  refine ⟨331645287630610218679669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1768774867363254499624901 331645287630610218679669)
                  ·
                    rfl

theorem cell21_1453223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 4].length) (baseStart_1453223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453223 prefixEnd_1453223 := by exact prefixLift 1453223
  have htrace : WordTrace (prefixWord ++ tailWord_1453223) baseStart_1453223 baseEnd_1453223 := by
    simpa [prefixWord, tailWord_1453223, baseEnd_1453223] using wordTrace_append hprefix tailTrace_1453223
  have hstable : (prefixWord ++ tailWord_1453223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453223).length < 2 ^ (prefixWord ++ tailWord_1453223).sum := by decide
  have hdescent : baseEnd_1453223 < baseStart_1453223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453254 : List Nat := [6, 1, 2, 2, 1, 9]
def baseStart_1453254 : Nat := 118140960795 + 1453254 * 2 ^ 59
def prefixEnd_1453254 : Nat := 4983230072969 + 3 ^ 40 * 1453254 * 2
def baseEnd_1453254 : Nat := 12283420824183742728257

theorem tailTrace_1453254 : CollatzResearch.WordTrace tailWord_1453254 prefixEnd_1453254 12283420824183742728257 := by
  unfold tailWord_1453254
  simp only [CollatzResearch.WordTrace]
  refine ⟨1656391496159888402137963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35336351918077619245609877 1656391496159888402137963)
  ·
    refine ⟨2484587244239832603206945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1656391496159888402137963 2484587244239832603206945)
    ·
      refine ⟨1863440433179874452405209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2484587244239832603206945 1863440433179874452405209)
      ·
        refine ⟨1397580324884905839303907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863440433179874452405209 1397580324884905839303907)
        ·
          refine ⟨2096370487327358758955861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397580324884905839303907 2096370487327358758955861)
          ·
            refine ⟨12283420824183742728257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2096370487327358758955861 12283420824183742728257)
            ·
              rfl

theorem cell21_1453254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 9].length) (baseStart_1453254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453254 prefixEnd_1453254 := by exact prefixLift 1453254
  have htrace : WordTrace (prefixWord ++ tailWord_1453254) baseStart_1453254 baseEnd_1453254 := by
    simpa [prefixWord, tailWord_1453254, baseEnd_1453254] using wordTrace_append hprefix tailTrace_1453254
  have hstable : (prefixWord ++ tailWord_1453254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453254).length < 2 ^ (prefixWord ++ tailWord_1453254).sum := by decide
  have hdescent : baseEnd_1453254 < baseStart_1453254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453279 : List Nat := [1, 1, 2, 3, 2, 1, 5, 6]
def baseStart_1453279 : Nat := 118140960795 + 1453279 * 2 ^ 59
def prefixEnd_1453279 : Nat := 4983230072969 + 3 ^ 40 * 1453279 * 2
def baseEnd_1453279 : Nat := 110552689197855521915407

theorem tailTrace_1453279 : CollatzResearch.WordTrace tailWord_1453279 prefixEnd_1453279 110552689197855521915407 := by
  unfold tailWord_1453279
  simp only [CollatzResearch.WordTrace]
  refine ⟨53005439702025858138074891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35336959801350572092049927 53005439702025858138074891)
  ·
    refine ⟨79508159553038787207112337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53005439702025858138074891 79508159553038787207112337)
    ·
      refine ⟨59631119664779090405334253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79508159553038787207112337 59631119664779090405334253)
      ·
        refine ⟨22361669874292158902000345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59631119664779090405334253 22361669874292158902000345)
        ·
          refine ⟨16771252405719119176500259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22361669874292158902000345 16771252405719119176500259)
          ·
            refine ⟨25156878608578678764750389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16771252405719119176500259 25156878608578678764750389)
            ·
              refine ⟨2358457369554251134195349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25156878608578678764750389 2358457369554251134195349)
              ·
                refine ⟨110552689197855521915407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2358457369554251134195349 110552689197855521915407)
                ·
                  rfl

theorem cell21_1453279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 6].length) (baseStart_1453279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453279 prefixEnd_1453279 := by exact prefixLift 1453279
  have htrace : WordTrace (prefixWord ++ tailWord_1453279) baseStart_1453279 baseEnd_1453279 := by
    simpa [prefixWord, tailWord_1453279, baseEnd_1453279] using wordTrace_append hprefix tailTrace_1453279
  have hstable : (prefixWord ++ tailWord_1453279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453279).length < 2 ^ (prefixWord ++ tailWord_1453279).sum := by decide
  have hdescent : baseEnd_1453279 < baseStart_1453279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453448 : List Nat := [2, 1, 3, 3, 1, 4, 1, 6]
def baseStart_1453448 : Nat := 118140960795 + 1453448 * 2 ^ 59
def prefixEnd_1453448 : Nat := 4983230072969 + 3 ^ 40 * 1453448 * 2
def baseEnd_1453448 : Nat := 110565545232019942476403

theorem tailTrace_1453448 : CollatzResearch.WordTrace tailWord_1453448 prefixEnd_1453448 110565545232019942476403 := by
  unfold tailWord_1453448
  simp only [CollatzResearch.WordTrace]
  refine ⟨26505801819206800000488499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35341069092275733333984665 26505801819206800000488499)
  ·
    refine ⟨39758702728810200000732749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26505801819206800000488499 39758702728810200000732749)
    ·
      refine ⟨14909513523303825000274781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39758702728810200000732749 14909513523303825000274781)
      ·
        refine ⟨5591067571238934375103043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14909513523303825000274781 5591067571238934375103043)
        ·
          refine ⟨8386601356858401562654565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5591067571238934375103043 8386601356858401562654565)
          ·
            refine ⟨1572487754410950292997731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8386601356858401562654565 1572487754410950292997731)
            ·
              refine ⟨2358731631616425439496597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572487754410950292997731 2358731631616425439496597)
              ·
                refine ⟨110565545232019942476403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2358731631616425439496597 110565545232019942476403)
                ·
                  rfl

theorem cell21_1453448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 6].length) (baseStart_1453448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453448 prefixEnd_1453448 := by exact prefixLift 1453448
  have htrace : WordTrace (prefixWord ++ tailWord_1453448) baseStart_1453448 baseEnd_1453448 := by
    simpa [prefixWord, tailWord_1453448, baseEnd_1453448] using wordTrace_append hprefix tailTrace_1453448
  have hstable : (prefixWord ++ tailWord_1453448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453448).length < 2 ^ (prefixWord ++ tailWord_1453448).sum := by decide
  have hdescent : baseEnd_1453448 < baseStart_1453448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453476 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 6]
def baseStart_1453476 : Nat := 118140960795 + 1453476 * 2 ^ 59
def prefixEnd_1453476 : Nat := 4983230072969 + 3 ^ 40 * 1453476 * 2
def baseEnd_1453476 : Nat := 331703025677538000962485

theorem tailTrace_1453476 : CollatzResearch.WordTrace tailWord_1453476 prefixEnd_1453476 331703025677538000962485 := by
  unfold tailWord_1453476
  simp only [CollatzResearch.WordTrace]
  refine ⟨26506312441156080391498141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35341749921541440521997521 26506312441156080391498141)
  ·
    refine ⟨9939867165433530146811803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26506312441156080391498141 9939867165433530146811803)
    ·
      refine ⟨14909800748150295220217705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9939867165433530146811803 14909800748150295220217705)
      ·
        refine ⟨11182350561112721415163279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14909800748150295220217705 11182350561112721415163279)
        ·
          refine ⟨16773525841669082122744919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11182350561112721415163279 16773525841669082122744919)
          ·
            refine ⟨25160288762503623184117379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16773525841669082122744919 25160288762503623184117379)
            ·
              refine ⟨37740433143755434776176069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25160288762503623184117379 37740433143755434776176069)
              ·
                refine ⟨7076331214454144020533013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37740433143755434776176069 7076331214454144020533013)
                ·
                  refine ⟨331703025677538000962485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7076331214454144020533013 331703025677538000962485)
                  ·
                    rfl

theorem cell21_1453476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_1453476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453476 prefixEnd_1453476 := by exact prefixLift 1453476
  have htrace : WordTrace (prefixWord ++ tailWord_1453476) baseStart_1453476 baseEnd_1453476 := by
    simpa [prefixWord, tailWord_1453476, baseEnd_1453476] using wordTrace_append hprefix tailTrace_1453476
  have hstable : (prefixWord ++ tailWord_1453476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453476).length < 2 ^ (prefixWord ++ tailWord_1453476).sum := by decide
  have hdescent : baseEnd_1453476 < baseStart_1453476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453493 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 6]
def baseStart_1453493 : Nat := 118140960795 + 1453493 * 2 ^ 59
def prefixEnd_1453493 : Nat := 4983230072969 + 3 ^ 40 * 1453493 * 2
def baseEnd_1453493 : Nat := 331706905309149749179117

theorem tailTrace_1453493 : CollatzResearch.WordTrace tailWord_1453493 prefixEnd_1453493 331706905309149749179117 := by
  unfold tailWord_1453493
  simp only [CollatzResearch.WordTrace]
  refine ⟨53013244923250572686365133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35342163282167048457576755 53013244923250572686365133)
  ·
    refine ⟨19879966846218964757386925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53013244923250572686365133 19879966846218964757386925)
    ·
      refine ⟨7454987567332111784020097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19879966846218964757386925 7454987567332111784020097)
      ·
        refine ⟨5591240675499083838015073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7454987567332111784020097 5591240675499083838015073)
        ·
          refine ⟨4193430506624312878511305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5591240675499083838015073 4193430506624312878511305)
          ·
            refine ⟨3145072879968234658883479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4193430506624312878511305 3145072879968234658883479)
            ·
              refine ⟨4717609319952351988325219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145072879968234658883479 4717609319952351988325219)
              ·
                refine ⟨7076413979928527982487829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717609319952351988325219 7076413979928527982487829)
                ·
                  refine ⟨331706905309149749179117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7076413979928527982487829 331706905309149749179117)
                  ·
                    rfl

theorem cell21_1453493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_1453493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453493 prefixEnd_1453493 := by exact prefixLift 1453493
  have htrace : WordTrace (prefixWord ++ tailWord_1453493) baseStart_1453493 baseEnd_1453493 := by
    simpa [prefixWord, tailWord_1453493, baseEnd_1453493] using wordTrace_append hprefix tailTrace_1453493
  have hstable : (prefixWord ++ tailWord_1453493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453493).length < 2 ^ (prefixWord ++ tailWord_1453493).sum := by decide
  have hdescent : baseEnd_1453493 < baseStart_1453493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453524 : List Nat := [2, 4, 1, 2, 3, 1, 1, 7]
def baseStart_1453524 : Nat := 118140960795 + 1453524 * 2 ^ 59
def prefixEnd_1453524 : Nat := 4983230072969 + 3 ^ 40 * 1453524 * 2
def baseEnd_1453524 : Nat := 110571326643833528054129

theorem tailTrace_1453524 : CollatzResearch.WordTrace tailWord_1453524 prefixEnd_1453524 110571326643833528054129 := by
  unfold tailWord_1453524
  simp only [CollatzResearch.WordTrace]
  refine ⟨26507187793069132490371813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35342917057425509987162417 26507187793069132490371813)
  ·
    refine ⟨4970097711200462341944715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26507187793069132490371813 4970097711200462341944715)
    ·
      refine ⟨7455146566800693512917073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4970097711200462341944715 7455146566800693512917073)
      ·
        refine ⟨5591359925100520134687805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7455146566800693512917073 5591359925100520134687805)
        ·
          refine ⟨2096759971912695050507927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5591359925100520134687805 2096759971912695050507927)
          ·
            refine ⟨3145139957869042575761891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096759971912695050507927 3145139957869042575761891)
            ·
              refine ⟨4717709936803563863642837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145139957869042575761891 4717709936803563863642837)
              ·
                refine ⟨110571326643833528054129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4717709936803563863642837 110571326643833528054129)
                ·
                  rfl

theorem cell21_1453524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 7].length) (baseStart_1453524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453524 prefixEnd_1453524 := by exact prefixLift 1453524
  have htrace : WordTrace (prefixWord ++ tailWord_1453524) baseStart_1453524 baseEnd_1453524 := by
    simpa [prefixWord, tailWord_1453524, baseEnd_1453524] using wordTrace_append hprefix tailTrace_1453524
  have hstable : (prefixWord ++ tailWord_1453524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453524).length < 2 ^ (prefixWord ++ tailWord_1453524).sum := by decide
  have hdescent : baseEnd_1453524 < baseStart_1453524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453552 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 6]
def baseStart_1453552 : Nat := 118140960795 + 1453552 * 2 ^ 59
def prefixEnd_1453552 : Nat := 4983230072969 + 3 ^ 40 * 1453552 * 2
def baseEnd_1453552 : Nat := 331720369912978757695663

theorem tailTrace_1453552 : CollatzResearch.WordTrace tailWord_1453552 prefixEnd_1453552 331720369912978757695663 := by
  unfold tailWord_1453552
  simp only [CollatzResearch.WordTrace]
  refine ⟨26507698415018412881381455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35343597886691217175175273 26507698415018412881381455)
  ·
    refine ⟨39761547622527619322072183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26507698415018412881381455 39761547622527619322072183)
    ·
      refine ⟨59642321433791428983108275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39761547622527619322072183 59642321433791428983108275)
      ·
        refine ⟨89463482150687143474662413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59642321433791428983108275 89463482150687143474662413)
        ·
          refine ⟨33548805806507678802998405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89463482150687143474662413 33548805806507678802998405)
          ·
            refine ⟨6290401088720189775562201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33548805806507678802998405 6290401088720189775562201)
            ·
              refine ⟨4717800816540142331671651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6290401088720189775562201 4717800816540142331671651)
              ·
                refine ⟨7076701224810213497507477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4717800816540142331671651 7076701224810213497507477)
                ·
                  refine ⟨331720369912978757695663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7076701224810213497507477 331720369912978757695663)
                  ·
                    rfl

theorem cell21_1453552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 6].length) (baseStart_1453552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453552 prefixEnd_1453552 := by exact prefixLift 1453552
  have htrace : WordTrace (prefixWord ++ tailWord_1453552) baseStart_1453552 baseEnd_1453552 := by
    simpa [prefixWord, tailWord_1453552, baseEnd_1453552] using wordTrace_append hprefix tailTrace_1453552
  have hstable : (prefixWord ++ tailWord_1453552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453552).length < 2 ^ (prefixWord ++ tailWord_1453552).sum := by decide
  have hdescent : baseEnd_1453552 < baseStart_1453552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453673 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 5]
def baseStart_1453673 : Nat := 118140960795 + 1453673 * 2 ^ 59
def prefixEnd_1453673 : Nat := 4983230072969 + 3 ^ 40 * 1453673 * 2
def baseEnd_1453673 : Nat := 331747983761509436178749

theorem tailTrace_1453673 : CollatzResearch.WordTrace tailWord_1453673 prefixEnd_1453673 331747983761509436178749 := by
  unfold tailWord_1453673
  simp only [CollatzResearch.WordTrace]
  refine ⟨53019810062598463427917673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35346540041732308951945115 53019810062598463427917673)
  ·
    refine ⟨39764857546948847570938255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53019810062598463427917673 39764857546948847570938255)
    ·
      refine ⟨59647286320423271356407383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39764857546948847570938255 59647286320423271356407383)
      ·
        refine ⟨89470929480634907034611075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59647286320423271356407383 89470929480634907034611075)
        ·
          refine ⟨134206394220952360551916613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89470929480634907034611075 134206394220952360551916613)
          ·
            refine ⟨25163698916428567603484365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134206394220952360551916613 25163698916428567603484365)
            ·
              refine ⟨9436387093660712851306637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25163698916428567603484365 9436387093660712851306637)
              ·
                refine ⟨3538645160122767319239989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9436387093660712851306637 3538645160122767319239989)
                ·
                  refine ⟨331747983761509436178749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3538645160122767319239989 331747983761509436178749)
                  ·
                    rfl

theorem cell21_1453673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_1453673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453673 prefixEnd_1453673 := by exact prefixLift 1453673
  have htrace : WordTrace (prefixWord ++ tailWord_1453673) baseStart_1453673 baseEnd_1453673 := by
    simpa [prefixWord, tailWord_1453673, baseEnd_1453673] using wordTrace_append hprefix tailTrace_1453673
  have hstable : (prefixWord ++ tailWord_1453673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453673).length < 2 ^ (prefixWord ++ tailWord_1453673).sum := by decide
  have hdescent : baseEnd_1453673 < baseStart_1453673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453724 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 5]
def baseStart_1453724 : Nat := 118140960795 + 1453724 * 2 ^ 59
def prefixEnd_1453724 : Nat := 4983230072969 + 3 ^ 40 * 1453724 * 2
def baseEnd_1453724 : Nat := 331759622656344680828645

theorem tailTrace_1453724 : CollatzResearch.WordTrace tailWord_1453724 prefixEnd_1453724 331759622656344680828645 := by
  unfold tailWord_1453724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26510835092706849569012113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35347780123609132758682817 26510835092706849569012113)
  ·
    refine ⟨19883126319530137176759085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26510835092706849569012113 19883126319530137176759085)
    ·
      refine ⟨7456172369823801441284657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19883126319530137176759085 7456172369823801441284657)
      ·
        refine ⟨5592129277367851080963493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7456172369823801441284657 5592129277367851080963493)
        ·
          refine ⟨1048524239506472077680655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5592129277367851080963493 1048524239506472077680655)
          ·
            refine ⟨1572786359259708116520983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048524239506472077680655 1572786359259708116520983)
            ·
              refine ⟨2359179538889562174781475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572786359259708116520983 2359179538889562174781475)
              ·
                refine ⟨3538769308334343262172213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2359179538889562174781475 3538769308334343262172213)
                ·
                  refine ⟨331759622656344680828645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3538769308334343262172213 331759622656344680828645)
                  ·
                    rfl

theorem cell21_1453724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 5].length) (baseStart_1453724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453724 prefixEnd_1453724 := by exact prefixLift 1453724
  have htrace : WordTrace (prefixWord ++ tailWord_1453724) baseStart_1453724 baseEnd_1453724 := by
    simpa [prefixWord, tailWord_1453724, baseEnd_1453724] using wordTrace_append hprefix tailTrace_1453724
  have hstable : (prefixWord ++ tailWord_1453724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453724).length < 2 ^ (prefixWord ++ tailWord_1453724).sum := by decide
  have hdescent : baseEnd_1453724 < baseStart_1453724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453831 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 4]
def baseStart_1453831 : Nat := 118140960795 + 1453831 * 2 ^ 59
def prefixEnd_1453831 : Nat := 4983230072969 + 3 ^ 40 * 1453831 * 2
def baseEnd_1453831 : Nat := 331784041514136272545093

theorem tailTrace_1453831 : CollatzResearch.WordTrace tailWord_1453831 prefixEnd_1453831 331784041514136272545093 := by
  unfold tailWord_1453831
  simp only [CollatzResearch.WordTrace]
  refine ⟨53025572796026056412169347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35350381864017370941446231 53025572796026056412169347)
  ·
    refine ⟨79538359194039084618254021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53025572796026056412169347 79538359194039084618254021)
    ·
      refine ⟨14913442348882328365922629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79538359194039084618254021 14913442348882328365922629)
      ·
        refine ⟨2796270440415436568610493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14913442348882328365922629 2796270440415436568610493)
        ·
          refine ⟨1048601415155788713228935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2796270440415436568610493 1048601415155788713228935)
          ·
            refine ⟨1572902122733683069843403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048601415155788713228935 1572902122733683069843403)
            ·
              refine ⟨2359353184100524604765105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572902122733683069843403 2359353184100524604765105)
              ·
                refine ⟨1769514888075393453573829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2359353184100524604765105 1769514888075393453573829)
                ·
                  refine ⟨331784041514136272545093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1769514888075393453573829 331784041514136272545093)
                  ·
                    rfl

theorem cell21_1453831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 4].length) (baseStart_1453831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453831 prefixEnd_1453831 := by exact prefixLift 1453831
  have htrace : WordTrace (prefixWord ++ tailWord_1453831) baseStart_1453831 baseEnd_1453831 := by
    simpa [prefixWord, tailWord_1453831, baseEnd_1453831] using wordTrace_append hprefix tailTrace_1453831
  have hstable : (prefixWord ++ tailWord_1453831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453831).length < 2 ^ (prefixWord ++ tailWord_1453831).sum := by decide
  have hdescent : baseEnd_1453831 < baseStart_1453831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453876 : List Nat := [2, 5, 1, 1, 2, 1, 3, 3, 3]
def baseStart_1453876 : Nat := 118140960795 + 1453876 * 2 ^ 59
def prefixEnd_1453876 : Nat := 4983230072969 + 3 ^ 40 * 1453876 * 2
def baseEnd_1453876 : Nat := 331794311127226194295001

theorem tailTrace_1453876 : CollatzResearch.WordTrace tailWord_1453876 prefixEnd_1453876 331794311127226194295001 := by
  unfold tailWord_1453876
  simp only [CollatzResearch.WordTrace]
  refine ⟨26513607040431514548778741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35351476053908686065038321 26513607040431514548778741)
  ·
    refine ⟨2485650660040454488948007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26513607040431514548778741 2485650660040454488948007)
    ·
      refine ⟨3728475990060681733422011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2485650660040454488948007 3728475990060681733422011)
      ·
        refine ⟨5592713985091022600133017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728475990060681733422011 5592713985091022600133017)
        ·
          refine ⟨4194535488818266950099763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5592713985091022600133017 4194535488818266950099763)
          ·
            refine ⟨6291803233227400425149645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4194535488818266950099763 6291803233227400425149645)
            ·
              refine ⟨2359426212460275159431117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6291803233227400425149645 2359426212460275159431117)
              ·
                refine ⟨884784829672603184786669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2359426212460275159431117 884784829672603184786669)
                ·
                  refine ⟨331794311127226194295001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884784829672603184786669 331794311127226194295001)
                  ·
                    rfl

theorem cell21_1453876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_1453876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453876 prefixEnd_1453876 := by exact prefixLift 1453876
  have htrace : WordTrace (prefixWord ++ tailWord_1453876) baseStart_1453876 baseEnd_1453876 := by
    simpa [prefixWord, tailWord_1453876, baseEnd_1453876] using wordTrace_append hprefix tailTrace_1453876
  have hstable : (prefixWord ++ tailWord_1453876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453876).length < 2 ^ (prefixWord ++ tailWord_1453876).sum := by decide
  have hdescent : baseEnd_1453876 < baseStart_1453876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453887 : List Nat := [1, 1, 2, 2, 6, 2, 7]
def baseStart_1453887 : Nat := 118140960795 + 1453887 * 2 ^ 59
def prefixEnd_1453887 : Nat := 4983230072969 + 3 ^ 40 * 1453887 * 2
def baseEnd_1453887 : Nat := 36866313497454735512405

theorem tailTrace_1453887 : CollatzResearch.WordTrace tailWord_1453887 prefixEnd_1453887 36866313497454735512405 := by
  unfold tailWord_1453887
  simp only [CollatzResearch.WordTrace]
  refine ⟨53027615283823177976207915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35351743522548785317471943 53027615283823177976207915)
  ·
    refine ⟨79541422925734766964311873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53027615283823177976207915 79541422925734766964311873)
    ·
      refine ⟨59656067194301075223233905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79541422925734766964311873 59656067194301075223233905)
      ·
        refine ⟨44742050395725806417425429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59656067194301075223233905 44742050395725806417425429)
        ·
          refine ⟨2097283612299647175816817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44742050395725806417425429 2097283612299647175816817)
          ·
            refine ⟨1572962709224735381862613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2097283612299647175816817 1572962709224735381862613)
            ·
              refine ⟨36866313497454735512405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1572962709224735381862613 36866313497454735512405)
              ·
                rfl

theorem cell21_1453887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 7].length) (baseStart_1453887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453887 prefixEnd_1453887 := by exact prefixLift 1453887
  have htrace : WordTrace (prefixWord ++ tailWord_1453887) baseStart_1453887 baseEnd_1453887 := by
    simpa [prefixWord, tailWord_1453887, baseEnd_1453887] using wordTrace_append hprefix tailTrace_1453887
  have hstable : (prefixWord ++ tailWord_1453887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453887).length < 2 ^ (prefixWord ++ tailWord_1453887).sum := by decide
  have hdescent : baseEnd_1453887 < baseStart_1453887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1453980 : List Nat := [2, 2, 3, 3, 1, 2, 3, 5]
def baseStart_1453980 : Nat := 118140960795 + 1453980 * 2 ^ 59
def prefixEnd_1453980 : Nat := 4983230072969 + 3 ^ 40 * 1453980 * 2
def baseEnd_1453980 : Nat := 110606015114715041520485

theorem tailTrace_1453980 : CollatzResearch.WordTrace tailWord_1453980 prefixEnd_1453980 110606015114715041520485 := by
  unfold tailWord_1453980
  simp only [CollatzResearch.WordTrace]
  refine ⟨26515503636243127429671697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35354004848324169906228929 26515503636243127429671697)
  ·
    refine ⟨19886627727182345572253773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26515503636243127429671697 19886627727182345572253773)
    ·
      refine ⟨7457485397693379589595165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19886627727182345572253773 7457485397693379589595165)
      ·
        refine ⟨2796557024135017346098187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7457485397693379589595165 2796557024135017346098187)
        ·
          refine ⟨4194835536202526019147281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2796557024135017346098187 4194835536202526019147281)
          ·
            refine ⟨3146126652151894514360461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4194835536202526019147281 3146126652151894514360461)
            ·
              refine ⟨1179797494556960442885173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3146126652151894514360461 1179797494556960442885173)
              ·
                refine ⟨110606015114715041520485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1179797494556960442885173 110606015114715041520485)
                ·
                  rfl

theorem cell21_1453980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 3, 5].length) (baseStart_1453980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1453980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1453980 prefixEnd_1453980 := by exact prefixLift 1453980
  have htrace : WordTrace (prefixWord ++ tailWord_1453980) baseStart_1453980 baseEnd_1453980 := by
    simpa [prefixWord, tailWord_1453980, baseEnd_1453980] using wordTrace_append hprefix tailTrace_1453980
  have hstable : (prefixWord ++ tailWord_1453980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1453980).length < 2 ^ (prefixWord ++ tailWord_1453980).sum := by decide
  have hdescent : baseEnd_1453980 < baseStart_1453980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1453980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454045 : List Nat := [1, 4, 3, 1, 4, 1, 1, 3, 3]
def baseStart_1454045 : Nat := 118140960795 + 1454045 * 2 ^ 59
def prefixEnd_1454045 : Nat := 4983230072969 + 3 ^ 40 * 1454045 * 2
def baseEnd_1454045 : Nat := 331832879229719455977989

theorem tailTrace_1454045 : CollatzResearch.WordTrace tailWord_1454045 prefixEnd_1454045 331832879229719455977989 := by
  unfold tailWord_1454045
  simp only [CollatzResearch.WordTrace]
  refine ⟨53033378017250770960459589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35355585344833847306973059 53033378017250770960459589)
  ·
    refine ⟨9943758378234519555086173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53033378017250770960459589 9943758378234519555086173)
    ·
      refine ⟨3728909391837944833157315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9943758378234519555086173 3728909391837944833157315)
      ·
        refine ⟨5593364087756917249735973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3728909391837944833157315 5593364087756917249735973)
        ·
          refine ⟨1048755766454421984325495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5593364087756917249735973 1048755766454421984325495)
          ·
            refine ⟨1573133649681632976488243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1048755766454421984325495 1573133649681632976488243)
            ·
              refine ⟨2359700474522449464732365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573133649681632976488243 2359700474522449464732365)
              ·
                refine ⟨884887677945918549274637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2359700474522449464732365 884887677945918549274637)
                ·
                  refine ⟨331832879229719455977989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884887677945918549274637 331832879229719455977989)
                  ·
                    rfl

theorem cell21_1454045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_1454045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454045 prefixEnd_1454045 := by exact prefixLift 1454045
  have htrace : WordTrace (prefixWord ++ tailWord_1454045) baseStart_1454045 baseEnd_1454045 := by
    simpa [prefixWord, tailWord_1454045, baseEnd_1454045] using wordTrace_append hprefix tailTrace_1454045
  have hstable : (prefixWord ++ tailWord_1454045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454045).length < 2 ^ (prefixWord ++ tailWord_1454045).sum := by decide
  have hdescent : baseEnd_1454045 < baseStart_1454045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454205 : List Nat := [1, 4, 1, 1, 3, 2, 2, 2, 5]
def baseStart_1454205 : Nat := 118140960795 + 1454205 * 2 ^ 59
def prefixEnd_1454205 : Nat := 4983230072969 + 3 ^ 40 * 1454205 * 2
def baseEnd_1454205 : Nat := 331869393409594733310995

theorem tailTrace_1454205 : CollatzResearch.WordTrace tailWord_1454205 prefixEnd_1454205 331869393409594733310995 := by
  unfold tailWord_1454205
  simp only [CollatzResearch.WordTrace]
  refine ⟨53039213696671118286284069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35359475797780745524189379 53039213696671118286284069)
  ·
    refine ⟨9944852568125834678678263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53039213696671118286284069 9944852568125834678678263)
    ·
      refine ⟨14917278852188752018017395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9944852568125834678678263 14917278852188752018017395)
      ·
        refine ⟨22375918278283128027026093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14917278852188752018017395 22375918278283128027026093)
        ·
          refine ⟨8390969354356173010134785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22375918278283128027026093 8390969354356173010134785)
          ·
            refine ⟨6293227015767129757601089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8390969354356173010134785 6293227015767129757601089)
            ·
              refine ⟨4719920261825347318200817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6293227015767129757601089 4719920261825347318200817)
              ·
                refine ⟨3539940196369010488650613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4719920261825347318200817 3539940196369010488650613)
                ·
                  refine ⟨331869393409594733310995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3539940196369010488650613 331869393409594733310995)
                  ·
                    rfl

theorem cell21_1454205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_1454205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454205 prefixEnd_1454205 := by exact prefixLift 1454205
  have htrace : WordTrace (prefixWord ++ tailWord_1454205) baseStart_1454205 baseEnd_1454205 := by
    simpa [prefixWord, tailWord_1454205, baseEnd_1454205] using wordTrace_append hprefix tailTrace_1454205
  have hstable : (prefixWord ++ tailWord_1454205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454205).length < 2 ^ (prefixWord ++ tailWord_1454205).sum := by decide
  have hdescent : baseEnd_1454205 < baseStart_1454205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454236 : List Nat := [2, 2, 3, 2, 1, 1, 2, 4, 4]
def baseStart_1454236 : Nat := 118140960795 + 1454236 * 2 ^ 59
def prefixEnd_1454236 : Nat := 4983230072969 + 3 ^ 40 * 1454236 * 2
def baseEnd_1454236 : Nat := 331876468031945568294265

theorem tailTrace_1454236 : CollatzResearch.WordTrace tailWord_1454236 prefixEnd_1454236 331876468031945568294265 := by
  unfold tailWord_1454236
  simp only [CollatzResearch.WordTrace]
  refine ⟨26520172179779405290331281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35360229573039207053775041 26520172179779405290331281)
  ·
    refine ⟨19890129134834553967748461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26520172179779405290331281 19890129134834553967748461)
    ·
      refine ⟨7458798425562957737905673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19890129134834553967748461 7458798425562957737905673)
      ·
        refine ⟨5594098819172218303429255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7458798425562957737905673 5594098819172218303429255)
        ·
          refine ⟨8391148228758327455143883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5594098819172218303429255 8391148228758327455143883)
          ·
            refine ⟨12586722343137491182715825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8391148228758327455143883 12586722343137491182715825)
            ·
              refine ⟨9440041757353118387036869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12586722343137491182715825 9440041757353118387036869)
              ·
                refine ⟨1770007829503709697569413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9440041757353118387036869 1770007829503709697569413)
                ·
                  refine ⟨331876468031945568294265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770007829503709697569413 331876468031945568294265)
                  ·
                    rfl

theorem cell21_1454236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 4, 4].length) (baseStart_1454236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454236 prefixEnd_1454236 := by exact prefixLift 1454236
  have htrace : WordTrace (prefixWord ++ tailWord_1454236) baseStart_1454236 baseEnd_1454236 := by
    simpa [prefixWord, tailWord_1454236, baseEnd_1454236] using wordTrace_append hprefix tailTrace_1454236
  have hstable : (prefixWord ++ tailWord_1454236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454236).length < 2 ^ (prefixWord ++ tailWord_1454236).sum := by decide
  have hdescent : baseEnd_1454236 < baseStart_1454236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454253 : List Nat := [1, 5, 2, 1, 2, 2, 1, 3, 4]
def baseStart_1454253 : Nat := 118140960795 + 1454253 * 2 ^ 59
def prefixEnd_1454253 : Nat := 4983230072969 + 3 ^ 40 * 1454253 * 2
def baseEnd_1454253 : Nat := 331880347663557316510897

theorem tailTrace_1454253 : CollatzResearch.WordTrace tailWord_1454253 prefixEnd_1454253 331880347663557316510897 := by
  unfold tailWord_1454253
  simp only [CollatzResearch.WordTrace]
  refine ⟨53040964400497222484031413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35360642933664814989354275 53040964400497222484031413)
  ·
    refine ⟨4972590412546614607877945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53040964400497222484031413 4972590412546614607877945)
    ·
      refine ⟨3729442809409960955908459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4972590412546614607877945 3729442809409960955908459)
      ·
        refine ⟨5594164214114941433862689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729442809409960955908459 5594164214114941433862689)
        ·
          refine ⟨4195623160586206075397017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5594164214114941433862689 4195623160586206075397017)
          ·
            refine ⟨3146717370439654556547763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4195623160586206075397017 3146717370439654556547763)
            ·
              refine ⟨4720076055659481834821645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3146717370439654556547763 4720076055659481834821645)
              ·
                refine ⟨1770028520872305688058117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720076055659481834821645 1770028520872305688058117)
                ·
                  refine ⟨331880347663557316510897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770028520872305688058117 331880347663557316510897)
                  ·
                    rfl

theorem cell21_1454253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_1454253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454253 prefixEnd_1454253 := by exact prefixLift 1454253
  have htrace : WordTrace (prefixWord ++ tailWord_1454253) baseStart_1454253 baseEnd_1454253 := by
    simpa [prefixWord, tailWord_1454253, baseEnd_1454253] using wordTrace_append hprefix tailTrace_1454253
  have hstable : (prefixWord ++ tailWord_1454253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454253).length < 2 ^ (prefixWord ++ tailWord_1454253).sum := by decide
  have hdescent : baseEnd_1454253 < baseStart_1454253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454264 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 7]
def baseStart_1454264 : Nat := 118140960795 + 1454264 * 2 ^ 59
def prefixEnd_1454264 : Nat := 4983230072969 + 3 ^ 40 * 1454264 * 2
def baseEnd_1454264 : Nat := 331882858013423741827541

theorem tailTrace_1454264 : CollatzResearch.WordTrace tailWord_1454264 prefixEnd_1454264 331882858013423741827541 := by
  unfold tailWord_1454264
  simp only [CollatzResearch.WordTrace]
  refine ⟨26520682801728685681340923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35360910402304914241787897 26520682801728685681340923)
  ·
    refine ⟨39781024202593028522011385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26520682801728685681340923 39781024202593028522011385)
    ·
      refine ⟨29835768151944771391508539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39781024202593028522011385 29835768151944771391508539)
      ·
        refine ⟨44753652227917157087262809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29835768151944771391508539 44753652227917157087262809)
        ·
          refine ⟨33565239170937867815447107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44753652227917157087262809 33565239170937867815447107)
          ·
            refine ⟨50347858756406801723170661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33565239170937867815447107 50347858756406801723170661)
            ·
              refine ⟨9440223516826275323094499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50347858756406801723170661 9440223516826275323094499)
              ·
                refine ⟨14160335275239412984641749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9440223516826275323094499 14160335275239412984641749)
                ·
                  refine ⟨331882858013423741827541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14160335275239412984641749 331882858013423741827541)
                  ·
                    rfl

theorem cell21_1454264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 7].length) (baseStart_1454264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454264 prefixEnd_1454264 := by exact prefixLift 1454264
  have htrace : WordTrace (prefixWord ++ tailWord_1454264) baseStart_1454264 baseEnd_1454264 := by
    simpa [prefixWord, tailWord_1454264, baseEnd_1454264] using wordTrace_append hprefix tailTrace_1454264
  have hstable : (prefixWord ++ tailWord_1454264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454264).length < 2 ^ (prefixWord ++ tailWord_1454264).sum := by decide
  have hdescent : baseEnd_1454264 < baseStart_1454264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454312 : List Nat := [2, 1, 4, 1, 2, 2, 2, 3, 4]
def baseStart_1454312 : Nat := 118140960795 + 1454312 * 2 ^ 59
def prefixEnd_1454312 : Nat := 4983230072969 + 3 ^ 40 * 1454312 * 2
def baseEnd_1454312 : Nat := 331893812267386325027443

theorem tailTrace_1454312 : CollatzResearch.WordTrace tailWord_1454312 prefixEnd_1454312 331893812267386325027443 := by
  unfold tailWord_1454312
  simp only [CollatzResearch.WordTrace]
  refine ⟨26521558153641737780214595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35362077538188983706952793 26521558153641737780214595)
  ·
    refine ⟨39782337230462606670321893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26521558153641737780214595 39782337230462606670321893)
    ·
      refine ⟨7459188230711738750685355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39782337230462606670321893 7459188230711738750685355)
      ·
        refine ⟨11188782346067608126028033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459188230711738750685355 11188782346067608126028033)
        ·
          refine ⟨8391586759550706094521025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11188782346067608126028033 8391586759550706094521025)
          ·
            refine ⟨6293690069663029570890769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8391586759550706094521025 6293690069663029570890769)
            ·
              refine ⟨4720267552247272178168077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6293690069663029570890769 4720267552247272178168077)
              ·
                refine ⟨1770100332092727066813029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4720267552247272178168077 1770100332092727066813029)
                ·
                  refine ⟨331893812267386325027443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770100332092727066813029 331893812267386325027443)
                  ·
                    rfl

theorem cell21_1454312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3, 4].length) (baseStart_1454312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454312 prefixEnd_1454312 := by exact prefixLift 1454312
  have htrace : WordTrace (prefixWord ++ tailWord_1454312) baseStart_1454312 baseEnd_1454312 := by
    simpa [prefixWord, tailWord_1454312, baseEnd_1454312] using wordTrace_append hprefix tailTrace_1454312
  have hstable : (prefixWord ++ tailWord_1454312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454312).length < 2 ^ (prefixWord ++ tailWord_1454312).sum := by decide
  have hdescent : baseEnd_1454312 < baseStart_1454312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454326 : List Nat := [5, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1454326 : Nat := 118140960795 + 1454326 * 2 ^ 59
def prefixEnd_1454326 : Nat := 4983230072969 + 3 ^ 40 * 1454326 * 2
def baseEnd_1454326 : Nat := 110632335752708470598027

theorem tailTrace_1454326 : CollatzResearch.WordTrace tailWord_1454326 prefixEnd_1454326 110632335752708470598027 := by
  unfold tailWord_1454326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315226683077047246964927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35362417952821837300959221 3315226683077047246964927)
  ·
    refine ⟨4972840024615570870447391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315226683077047246964927 4972840024615570870447391)
    ·
      refine ⟨7459260036923356305671087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4972840024615570870447391 7459260036923356305671087)
      ·
        refine ⟨11188890055385034458506631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7459260036923356305671087 11188890055385034458506631)
        ·
          refine ⟨16783335083077551687759947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11188890055385034458506631 16783335083077551687759947)
          ·
            refine ⟨25175002624616327531639921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16783335083077551687759947 25175002624616327531639921)
            ·
              refine ⟨18881251968462245648729941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25175002624616327531639921 18881251968462245648729941)
              ·
                refine ⟨110632335752708470598027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18881251968462245648729941 110632335752708470598027)
                ·
                  rfl

theorem cell21_1454326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1454326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454326 prefixEnd_1454326 := by exact prefixLift 1454326
  have htrace : WordTrace (prefixWord ++ tailWord_1454326) baseStart_1454326 baseEnd_1454326 := by
    simpa [prefixWord, tailWord_1454326, baseEnd_1454326] using wordTrace_append hprefix tailTrace_1454326
  have hstable : (prefixWord ++ tailWord_1454326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454326).length < 2 ^ (prefixWord ++ tailWord_1454326).sum := by decide
  have hdescent : baseEnd_1454326 < baseStart_1454326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454343 : List Nat := [1, 1, 4, 5, 1, 1, 8]
def baseStart_1454343 : Nat := 118140960795 + 1454343 * 2 ^ 59
def prefixEnd_1454343 : Nat := 4983230072969 + 3 ^ 40 * 1454343 * 2
def baseEnd_1454343 : Nat := 36877876321081906667857

theorem tailTrace_1454343 : CollatzResearch.WordTrace tailWord_1454343 prefixEnd_1454343 36877876321081906667857 := by
  unfold tailWord_1454343
  simp only [CollatzResearch.WordTrace]
  refine ⟨53044246970171167854807683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35362831313447445236538455 53044246970171167854807683)
  ·
    refine ⟨79566370455256751782211525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53044246970171167854807683 79566370455256751782211525)
    ·
      refine ⟨14918694460360640959164661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79566370455256751782211525 14918694460360640959164661)
      ·
        refine ⟨1398627605658810089921687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14918694460360640959164661 1398627605658810089921687)
        ·
          refine ⟨2097941408488215134882531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398627605658810089921687 2097941408488215134882531)
          ·
            refine ⟨3146912112732322702323797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097941408488215134882531 3146912112732322702323797)
            ·
              refine ⟨36877876321081906667857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3146912112732322702323797 36877876321081906667857)
              ·
                rfl

theorem cell21_1454343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 8].length) (baseStart_1454343 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454343 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454343 prefixEnd_1454343 := by exact prefixLift 1454343
  have htrace : WordTrace (prefixWord ++ tailWord_1454343) baseStart_1454343 baseEnd_1454343 := by
    simpa [prefixWord, tailWord_1454343, baseEnd_1454343] using wordTrace_append hprefix tailTrace_1454343
  have hstable : (prefixWord ++ tailWord_1454343).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454343).length < 2 ^ (prefixWord ++ tailWord_1454343).sum := by decide
  have hdescent : baseEnd_1454343 < baseStart_1454343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454388 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 6]
def baseStart_1454388 : Nat := 118140960795 + 1454388 * 2 ^ 59
def prefixEnd_1454388 : Nat := 4983230072969 + 3 ^ 40 * 1454388 * 2
def baseEnd_1454388 : Nat := 331911156502827081760621

theorem tailTrace_1454388 : CollatzResearch.WordTrace tailWord_1454388 prefixEnd_1454388 331911156502827081760621 := by
  unfold tailWord_1454388
  simp only [CollatzResearch.WordTrace]
  refine ⟨26522944127504070270097909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35363925503338760360130545 26522944127504070270097909)
  ·
    refine ⟨2486526011953506587821679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26522944127504070270097909 2486526011953506587821679)
    ·
      refine ⟨3729789017930259881732519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2486526011953506587821679 3729789017930259881732519)
      ·
        refine ⟨5594683526895389822598779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3729789017930259881732519 5594683526895389822598779)
        ·
          refine ⟨8392025290343084733898169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5594683526895389822598779 8392025290343084733898169)
          ·
            refine ⟨6294018967757313550423627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8392025290343084733898169 6294018967757313550423627)
            ·
              refine ⟨9441028451635970325635441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6294018967757313550423627 9441028451635970325635441)
              ·
                refine ⟨7080771338726977744226581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9441028451635970325635441 7080771338726977744226581)
                ·
                  refine ⟨331911156502827081760621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7080771338726977744226581 331911156502827081760621)
                  ·
                    rfl

theorem cell21_1454388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_1454388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454388 prefixEnd_1454388 := by exact prefixLift 1454388
  have htrace : WordTrace (prefixWord ++ tailWord_1454388) baseStart_1454388 baseEnd_1454388 := by
    simpa [prefixWord, tailWord_1454388, baseEnd_1454388] using wordTrace_append hprefix tailTrace_1454388
  have hstable : (prefixWord ++ tailWord_1454388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454388).length < 2 ^ (prefixWord ++ tailWord_1454388).sum := by decide
  have hdescent : baseEnd_1454388 < baseStart_1454388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454461 : List Nat := [1, 4, 1, 1, 2, 12]
def baseStart_1454461 : Nat := 118140960795 + 1454461 * 2 ^ 59
def prefixEnd_1454461 : Nat := 4983230072969 + 3 ^ 40 * 1454461 * 2
def baseEnd_1454461 : Nat := 12293622818422043594215

theorem tailTrace_1454461 : CollatzResearch.WordTrace tailWord_1454461 prefixEnd_1454461 12293622818422043594215 := by
  unfold tailWord_1454461
  simp only [CollatzResearch.WordTrace]
  refine ⟨53048550783743674007603237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35365700522495782671735491 53048550783743674007603237)
  ·
    refine ⟨9946603271951938876425607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53048550783743674007603237 9946603271951938876425607)
    ·
      refine ⟨14919904907927908314638411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9946603271951938876425607 14919904907927908314638411)
      ·
        refine ⟨22379857361891862471957617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14919904907927908314638411 22379857361891862471957617)
        ·
          refine ⟨16784893021418896853968213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22379857361891862471957617 16784893021418896853968213)
          ·
            refine ⟨12293622818422043594215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 16784893021418896853968213 12293622818422043594215)
            ·
              rfl

theorem cell21_1454461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 12].length) (baseStart_1454461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454461 prefixEnd_1454461 := by exact prefixLift 1454461
  have htrace : WordTrace (prefixWord ++ tailWord_1454461) baseStart_1454461 baseEnd_1454461 := by
    simpa [prefixWord, tailWord_1454461, baseEnd_1454461] using wordTrace_append hprefix tailTrace_1454461
  have hstable : (prefixWord ++ tailWord_1454461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454461).length < 2 ^ (prefixWord ++ tailWord_1454461).sum := by decide
  have hdescent : baseEnd_1454461 < baseStart_1454461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454526 : List Nat := [4, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_1454526 : Nat := 118140960795 + 1454526 * 2 ^ 59
def prefixEnd_1454526 : Nat := 4983230072969 + 3 ^ 40 * 1454526 * 2
def baseEnd_1454526 : Nat := 331942649982969508460339

theorem tailTrace_1454526 : CollatzResearch.WordTrace tailWord_1454526 prefixEnd_1454526 331942649982969508460339 := by
  unfold tailWord_1454526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6631365191063523763589929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35367281019005460072479621 6631365191063523763589929)
  ·
    refine ⟨4973523893297642822692447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6631365191063523763589929 4973523893297642822692447)
    ·
      refine ⟨7460285839946464234038671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4973523893297642822692447 7460285839946464234038671)
      ·
        refine ⟨11190428759919696351058007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7460285839946464234038671 11190428759919696351058007)
        ·
          refine ⟨16785643139879544526587011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11190428759919696351058007 16785643139879544526587011)
          ·
            refine ⟨25178464709819316789880517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16785643139879544526587011 25178464709819316789880517)
            ·
              refine ⟨4720962133091121898102597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25178464709819316789880517 4720962133091121898102597)
              ·
                refine ⟨885180399954585355894237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4720962133091121898102597 885180399954585355894237)
                ·
                  refine ⟨331942649982969508460339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885180399954585355894237 331942649982969508460339)
                  ·
                    rfl

theorem cell21_1454526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_1454526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454526 prefixEnd_1454526 := by exact prefixLift 1454526
  have htrace : WordTrace (prefixWord ++ tailWord_1454526) baseStart_1454526 baseEnd_1454526 := by
    simpa [prefixWord, tailWord_1454526, baseEnd_1454526] using wordTrace_append hprefix tailTrace_1454526
  have hstable : (prefixWord ++ tailWord_1454526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454526).length < 2 ^ (prefixWord ++ tailWord_1454526).sum := by decide
  have hdescent : baseEnd_1454526 < baseStart_1454526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454585 : List Nat := [1, 2, 1, 3, 1, 2, 2, 6, 3]
def baseStart_1454585 : Nat := 118140960795 + 1454585 * 2 ^ 59
def prefixEnd_1454585 : Nat := 4983230072969 + 3 ^ 40 * 1454585 * 2
def baseEnd_1454585 : Nat := 331956114586798516976885

theorem tailTrace_1454585 : CollatzResearch.WordTrace tailWord_1454585 prefixEnd_1454585 331956114586798516976885 := by
  unfold tailWord_1454585
  simp only [CollatzResearch.WordTrace]
  refine ⟨53053073435294443185117209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35368715623529628790078139 53053073435294443185117209)
  ·
    refine ⟨39789805076470832388837907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53053073435294443185117209 39789805076470832388837907)
    ·
      refine ⟨59684707614706248583256861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39789805076470832388837907 59684707614706248583256861)
      ·
        refine ⟨22381765355514843218721323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59684707614706248583256861 22381765355514843218721323)
        ·
          refine ⟨33572648033272264828081985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22381765355514843218721323 33572648033272264828081985)
          ·
            refine ⟨25179486024954198621061489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33572648033272264828081985 25179486024954198621061489)
            ·
              refine ⟨18884614518715648965796117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25179486024954198621061489 18884614518715648965796117)
              ·
                refine ⟨885216305564796045271693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18884614518715648965796117 885216305564796045271693)
                ·
                  refine ⟨331956114586798516976885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885216305564796045271693 331956114586798516976885)
                  ·
                    rfl

theorem cell21_1454585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 6, 3].length) (baseStart_1454585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454585 prefixEnd_1454585 := by exact prefixLift 1454585
  have htrace : WordTrace (prefixWord ++ tailWord_1454585) baseStart_1454585 baseEnd_1454585 := by
    simpa [prefixWord, tailWord_1454585, baseEnd_1454585] using wordTrace_append hprefix tailTrace_1454585
  have hstable : (prefixWord ++ tailWord_1454585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454585).length < 2 ^ (prefixWord ++ tailWord_1454585).sum := by decide
  have hdescent : baseEnd_1454585 < baseStart_1454585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454613 : List Nat := [1, 3, 2, 1, 3, 1, 1, 9]
def baseStart_1454613 : Nat := 118140960795 + 1454613 * 2 ^ 59
def prefixEnd_1454613 : Nat := 4983230072969 + 3 ^ 40 * 1454613 * 2
def baseEnd_1454613 : Nat := 110654168189425563503387

theorem tailTrace_1454613 : CollatzResearch.WordTrace tailWord_1454613 prefixEnd_1454613 110654168189425563503387 := by
  unfold tailWord_1454613
  simp only [CollatzResearch.WordTrace]
  refine ⟨53054094679193003967136493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35369396452795335978090995 53054094679193003967136493)
  ·
    refine ⟨19895285504697376487676185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53054094679193003967136493 19895285504697376487676185)
    ·
      refine ⟨14921464128523032365757139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19895285504697376487676185 14921464128523032365757139)
      ·
        refine ⟨22382196192784548548635709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921464128523032365757139 22382196192784548548635709)
        ·
          refine ⟨8393323572294205705738391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22382196192784548548635709 8393323572294205705738391)
          ·
            refine ⟨12589985358441308558607587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8393323572294205705738391 12589985358441308558607587)
            ·
              refine ⟨18884978037661962837911381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12589985358441308558607587 18884978037661962837911381)
              ·
                refine ⟨110654168189425563503387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18884978037661962837911381 110654168189425563503387)
                ·
                  rfl

theorem cell21_1454613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 9].length) (baseStart_1454613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454613 prefixEnd_1454613 := by exact prefixLift 1454613
  have htrace : WordTrace (prefixWord ++ tailWord_1454613) baseStart_1454613 baseEnd_1454613 := by
    simpa [prefixWord, tailWord_1454613, baseEnd_1454613] using wordTrace_append hprefix tailTrace_1454613
  have hstable : (prefixWord ++ tailWord_1454613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454613).length < 2 ^ (prefixWord ++ tailWord_1454613).sum := by decide
  have hdescent : baseEnd_1454613 < baseStart_1454613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454689 : List Nat := [1, 2, 3, 1, 1, 5, 8]
def baseStart_1454689 : Nat := 118140960795 + 1454689 * 2 ^ 59
def prefixEnd_1454689 : Nat := 4983230072969 + 3 ^ 40 * 1454689 * 2
def baseEnd_1454689 : Nat := 36886649867079716360371

theorem tailTrace_1454689 : CollatzResearch.WordTrace tailWord_1454689 prefixEnd_1454689 36886649867079716360371 := by
  unfold tailWord_1454689
  simp only [CollatzResearch.WordTrace]
  refine ⟨53056866626917668946903121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35371244417945112631268747 53056866626917668946903121)
  ·
    refine ⟨39792649970188251710177341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53056866626917668946903121 39792649970188251710177341)
    ·
      refine ⟨14922243738820594391316503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39792649970188251710177341 14922243738820594391316503)
      ·
        refine ⟨22383365608230891586974755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14922243738820594391316503 22383365608230891586974755)
        ·
          refine ⟨33575048412346337380462133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22383365608230891586974755 33575048412346337380462133)
          ·
            refine ⟨3147660788657469129418325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33575048412346337380462133 3147660788657469129418325)
            ·
              refine ⟨36886649867079716360371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3147660788657469129418325 36886649867079716360371)
              ·
                rfl

theorem cell21_1454689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 8].length) (baseStart_1454689 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454689 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454689 prefixEnd_1454689 := by exact prefixLift 1454689
  have htrace : WordTrace (prefixWord ++ tailWord_1454689) baseStart_1454689 baseEnd_1454689 := by
    simpa [prefixWord, tailWord_1454689, baseEnd_1454689] using wordTrace_append hprefix tailTrace_1454689
  have hstable : (prefixWord ++ tailWord_1454689).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454689).length < 2 ^ (prefixWord ++ tailWord_1454689).sum := by decide
  have hdescent : baseEnd_1454689 < baseStart_1454689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454720 : List Nat := [2, 1, 1, 2, 1, 5, 2, 2, 5]
def baseStart_1454720 : Nat := 118140960795 + 1454720 * 2 ^ 59
def prefixEnd_1454720 : Nat := 4983230072969 + 3 ^ 40 * 1454720 * 2
def baseEnd_1454720 : Nat := 331986923426068282226609

theorem tailTrace_1454720 : CollatzResearch.WordTrace tailWord_1454720 prefixEnd_1454720 331986923426068282226609 := by
  unfold tailWord_1454720
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528998644902680620640807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35371998193203574160854409 26528998644902680620640807)
  ·
    refine ⟨39793497967354020930961211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26528998644902680620640807 39793497967354020930961211)
    ·
      refine ⟨59690246951031031396441817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39793497967354020930961211 59690246951031031396441817)
      ·
        refine ⟨44767685213273273547331363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59690246951031031396441817 44767685213273273547331363)
        ·
          refine ⟨67151527819909910320997045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44767685213273273547331363 67151527819909910320997045)
          ·
            refine ⟨6295455733116554092593473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67151527819909910320997045 6295455733116554092593473)
            ·
              refine ⟨4721591799837415569445105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6295455733116554092593473 4721591799837415569445105)
              ·
                refine ⟨3541193849878061677083829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4721591799837415569445105 3541193849878061677083829)
                ·
                  refine ⟨331986923426068282226609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3541193849878061677083829 331986923426068282226609)
                  ·
                    rfl

theorem cell21_1454720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 2, 5].length) (baseStart_1454720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454720 prefixEnd_1454720 := by exact prefixLift 1454720
  have htrace : WordTrace (prefixWord ++ tailWord_1454720) baseStart_1454720 baseEnd_1454720 := by
    simpa [prefixWord, tailWord_1454720, baseEnd_1454720] using wordTrace_append hprefix tailTrace_1454720
  have hstable : (prefixWord ++ tailWord_1454720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454720).length < 2 ^ (prefixWord ++ tailWord_1454720).sum := by decide
  have hdescent : baseEnd_1454720 < baseStart_1454720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454805 : List Nat := [1, 3, 2, 5, 2, 1, 2, 2, 3]
def baseStart_1454805 : Nat := 118140960795 + 1454805 * 2 ^ 59
def prefixEnd_1454805 : Nat := 4983230072969 + 3 ^ 40 * 1454805 * 2
def baseEnd_1454805 : Nat := 332006321584127023309769

theorem tailTrace_1454805 : CollatzResearch.WordTrace tailWord_1454805 prefixEnd_1454805 332006321584127023309769 := by
  unfold tailWord_1454805
  simp only [CollatzResearch.WordTrace]
  refine ⟨53061097494497420758125869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35374064996331613838750579 53061097494497420758125869)
  ·
    refine ⟨19897911560436532784297201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53061097494497420758125869 19897911560436532784297201)
    ·
      refine ⟨14923433670327399588222901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19897911560436532784297201 14923433670327399588222901)
      ·
        refine ⟨1399071906593193711395897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14923433670327399588222901 1399071906593193711395897)
        ·
          refine ⟨1049303929944895283546923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399071906593193711395897 1049303929944895283546923)
          ·
            refine ⟨1573955894917342925320385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049303929944895283546923 1573955894917342925320385)
            ·
              refine ⟨1180466921188007193990289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1573955894917342925320385 1180466921188007193990289)
              ·
                refine ⟨885350190891005395492717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180466921188007193990289 885350190891005395492717)
                ·
                  refine ⟨332006321584127023309769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885350190891005395492717 332006321584127023309769)
                  ·
                    rfl

theorem cell21_1454805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_1454805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454805 prefixEnd_1454805 := by exact prefixLift 1454805
  have htrace : WordTrace (prefixWord ++ tailWord_1454805) baseStart_1454805 baseEnd_1454805 := by
    simpa [prefixWord, tailWord_1454805, baseEnd_1454805] using wordTrace_append hprefix tailTrace_1454805
  have hstable : (prefixWord ++ tailWord_1454805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454805).length < 2 ^ (prefixWord ++ tailWord_1454805).sum := by decide
  have hdescent : baseEnd_1454805 < baseStart_1454805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454962 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_1454962 : Nat := 118140960795 + 1454962 * 2 ^ 59
def prefixEnd_1454962 : Nat := 4983230072969 + 3 ^ 40 * 1454962 * 2
def baseEnd_1454962 : Nat := 332042151123129639192781

theorem tailTrace_1454962 : CollatzResearch.WordTrace tailWord_1454962 prefixEnd_1454962 332042151123129639192781 := by
  unfold tailWord_1454962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13266705938732159142897785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35377882503285757714394093 13266705938732159142897785)
  ·
    refine ⟨9950029454049119357173339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13266705938732159142897785 9950029454049119357173339)
    ·
      refine ⟨14925044181073679035760009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9950029454049119357173339 14925044181073679035760009)
      ·
        refine ⟨11193783135805259276820007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14925044181073679035760009 11193783135805259276820007)
        ·
          refine ⟨16790674703707888915230011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193783135805259276820007 16790674703707888915230011)
          ·
            refine ⟨25186012055561833372845017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16790674703707888915230011 25186012055561833372845017)
            ·
              refine ⟨18889509041671375029633763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25186012055561833372845017 18889509041671375029633763)
              ·
                refine ⟨28334263562507062544450645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18889509041671375029633763 28334263562507062544450645)
                ·
                  refine ⟨332042151123129639192781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28334263562507062544450645 332042151123129639192781)
                  ·
                    rfl

theorem cell21_1454962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_1454962 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454962 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454962 prefixEnd_1454962 := by exact prefixLift 1454962
  have htrace : WordTrace (prefixWord ++ tailWord_1454962) baseStart_1454962 baseEnd_1454962 := by
    simpa [prefixWord, tailWord_1454962, baseEnd_1454962] using wordTrace_append hprefix tailTrace_1454962
  have hstable : (prefixWord ++ tailWord_1454962).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454962).length < 2 ^ (prefixWord ++ tailWord_1454962).sum := by decide
  have hdescent : baseEnd_1454962 < baseStart_1454962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454979 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 4]
def baseStart_1454979 : Nat := 118140960795 + 1454979 * 2 ^ 59
def prefixEnd_1454979 : Nat := 4983230072969 + 3 ^ 40 * 1454979 * 2
def baseEnd_1454979 : Nat := 332046030754741387409413

theorem tailTrace_1454979 : CollatzResearch.WordTrace tailWord_1454979 prefixEnd_1454979 332046030754741387409413 := by
  unfold tailWord_1454979
  simp only [CollatzResearch.WordTrace]
  refine ⟨53067443795867048474959991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35378295863911365649973327 53067443795867048474959991)
  ·
    refine ⟨79601165693800572712439987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53067443795867048474959991 79601165693800572712439987)
    ·
      refine ⟨119401748540700859068659981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79601165693800572712439987 119401748540700859068659981)
      ·
        refine ⟨44775655702762822150747493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119401748540700859068659981 44775655702762822150747493)
        ·
          refine ⟨8395435444268029153265155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44775655702762822150747493 8395435444268029153265155)
          ·
            refine ⟨12593153166402043729897733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8395435444268029153265155 12593153166402043729897733)
            ·
              refine ⟨2361216218700383199355825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12593153166402043729897733 2361216218700383199355825)
              ·
                refine ⟨1770912164025287399516869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361216218700383199355825 1770912164025287399516869)
                ·
                  refine ⟨332046030754741387409413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1770912164025287399516869 332046030754741387409413)
                  ·
                    rfl

theorem cell21_1454979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 4].length) (baseStart_1454979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1454979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1454979 prefixEnd_1454979 := by exact prefixLift 1454979
  have htrace : WordTrace (prefixWord ++ tailWord_1454979) baseStart_1454979 baseEnd_1454979 := by
    simpa [prefixWord, tailWord_1454979, baseEnd_1454979] using wordTrace_append hprefix tailTrace_1454979
  have hstable : (prefixWord ++ tailWord_1454979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454979).length < 2 ^ (prefixWord ++ tailWord_1454979).sum := by decide
  have hdescent : baseEnd_1454979 < baseStart_1454979 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455030 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_1455030 : Nat := 118140960795 + 1455030 * 2 ^ 59
def prefixEnd_1455030 : Nat := 4983230072969 + 3 ^ 40 * 1455030 * 2
def baseEnd_1455030 : Nat := 332057669649576632059309

theorem tailTrace_1455030 : CollatzResearch.WordTrace tailWord_1455030 prefixEnd_1455030 332057669649576632059309 := by
  unfold tailWord_1455030
  simp only [CollatzResearch.WordTrace]
  refine ⟨3316831494917642761566659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35379535945788189456711029 3316831494917642761566659)
  ·
    refine ⟨4975247242376464142349989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3316831494917642761566659 4975247242376464142349989)
    ·
      refine ⟨932858857945587026690623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4975247242376464142349989 932858857945587026690623)
      ·
        refine ⟨1399288286918380540035935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932858857945587026690623 1399288286918380540035935)
        ·
          refine ⟨2098932430377570810053903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399288286918380540035935 2098932430377570810053903)
          ·
            refine ⟨3148398645566356215080855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098932430377570810053903 3148398645566356215080855)
            ·
              refine ⟨4722597968349534322621283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148398645566356215080855 4722597968349534322621283)
              ·
                refine ⟨7083896952524301483931925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4722597968349534322621283 7083896952524301483931925)
                ·
                  refine ⟨332057669649576632059309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7083896952524301483931925 332057669649576632059309)
                  ·
                    rfl

theorem cell21_1455030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_1455030 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455030 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455030 prefixEnd_1455030 := by exact prefixLift 1455030
  have htrace : WordTrace (prefixWord ++ tailWord_1455030) baseStart_1455030 baseEnd_1455030 := by
    simpa [prefixWord, tailWord_1455030, baseEnd_1455030] using wordTrace_append hprefix tailTrace_1455030
  have hstable : (prefixWord ++ tailWord_1455030).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455030).length < 2 ^ (prefixWord ++ tailWord_1455030).sum := by decide
  have hdescent : baseEnd_1455030 < baseStart_1455030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455086 : List Nat := [4, 1, 2, 1, 4, 2, 7]
def baseStart_1455086 : Nat := 118140960795 + 1455086 * 2 ^ 59
def prefixEnd_1455086 : Nat := 4983230072969 + 3 ^ 40 * 1455086 * 2
def baseEnd_1455086 : Nat := 36896716623614775458429

theorem tailTrace_1455086 : CollatzResearch.WordTrace tailWord_1455086 prefixEnd_1455086 36896716623614775458429 := by
  unfold tailWord_1455086
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633918300809925718638139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35380897604319603832736741 6633918300809925718638139)
  ·
    refine ⟨9950877451214888577957209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6633918300809925718638139 9950877451214888577957209)
    ·
      refine ⟨7463158088411166433467907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9950877451214888577957209 7463158088411166433467907)
      ·
        refine ⟨11194737132616749650201861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7463158088411166433467907 11194737132616749650201861)
        ·
          refine ⟨2099013212365640559412849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11194737132616749650201861 2099013212365640559412849)
          ·
            refine ⟨1574259909274230419559637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2099013212365640559412849 1574259909274230419559637)
            ·
              refine ⟨36896716623614775458429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1574259909274230419559637 36896716623614775458429)
              ·
                rfl

theorem cell21_1455086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 7].length) (baseStart_1455086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455086 prefixEnd_1455086 := by exact prefixLift 1455086
  have htrace : WordTrace (prefixWord ++ tailWord_1455086) baseStart_1455086 baseEnd_1455086 := by
    simpa [prefixWord, tailWord_1455086, baseEnd_1455086] using wordTrace_append hprefix tailTrace_1455086
  have hstable : (prefixWord ++ tailWord_1455086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455086).length < 2 ^ (prefixWord ++ tailWord_1455086).sum := by decide
  have hdescent : baseEnd_1455086 < baseStart_1455086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455100 : List Nat := [2, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_1455100 : Nat := 118140960795 + 1455100 * 2 ^ 59
def prefixEnd_1455100 : Nat := 4983230072969 + 3 ^ 40 * 1455100 * 2
def baseEnd_1455100 : Nat := 332073644603272065892499

theorem tailTrace_1455100 : CollatzResearch.WordTrace tailWord_1455100 prefixEnd_1455100 332073644603272065892499 := by
  unfold tailWord_1455100
  simp only [CollatzResearch.WordTrace]
  refine ⟨26535928514214343070057377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35381238018952457426743169 26535928514214343070057377)
  ·
    refine ⟨19901946385660757302543033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26535928514214343070057377 19901946385660757302543033)
    ·
      refine ⟨14926459789245567976907275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19901946385660757302543033 14926459789245567976907275)
      ·
        refine ⟨22389689683868351965360913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14926459789245567976907275 22389689683868351965360913)
        ·
          refine ⟨16792267262901263974020685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22389689683868351965360913 16792267262901263974020685)
          ·
            refine ⟨6297100223587973990257757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16792267262901263974020685 6297100223587973990257757)
            ·
              refine ⟨2361412583845490246346659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6297100223587973990257757 2361412583845490246346659)
              ·
                refine ⟨3542118875768235369519989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2361412583845490246346659 3542118875768235369519989)
                ·
                  refine ⟨332073644603272065892499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542118875768235369519989 332073644603272065892499)
                  ·
                    rfl

theorem cell21_1455100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_1455100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455100 prefixEnd_1455100 := by exact prefixLift 1455100
  have htrace : WordTrace (prefixWord ++ tailWord_1455100) baseStart_1455100 baseEnd_1455100 := by
    simpa [prefixWord, tailWord_1455100, baseEnd_1455100] using wordTrace_append hprefix tailTrace_1455100
  have hstable : (prefixWord ++ tailWord_1455100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455100).length < 2 ^ (prefixWord ++ tailWord_1455100).sum := by decide
  have hdescent : baseEnd_1455100 < baseStart_1455100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455159 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 5]
def baseStart_1455159 : Nat := 118140960795 + 1455159 * 2 ^ 59
def prefixEnd_1455159 : Nat := 4983230072969 + 3 ^ 40 * 1455159 * 2
def baseEnd_1455159 : Nat := 332087109207101074409045

theorem tailTrace_1455159 : CollatzResearch.WordTrace tailWord_1455159 prefixEnd_1455159 332087109207101074409045 := by
  unfold tailWord_1455159
  simp only [CollatzResearch.WordTrace]
  refine ⟨53074008935214939216512531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35382672623476626144341687 53074008935214939216512531)
  ·
    refine ⟨79611013402822408824768797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53074008935214939216512531 79611013402822408824768797)
    ·
      refine ⟨29854130026058403309288299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79611013402822408824768797 29854130026058403309288299)
      ·
        refine ⟨44781195039087604963932449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29854130026058403309288299 44781195039087604963932449)
        ·
          refine ⟨33585896279315703722949337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44781195039087604963932449 33585896279315703722949337)
          ·
            refine ⟨25189422209486777792212003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33585896279315703722949337 25189422209486777792212003)
            ·
              refine ⟨37784133314230166688318005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25189422209486777792212003 37784133314230166688318005)
              ·
                refine ⟨3542262498209078127029813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37784133314230166688318005 3542262498209078127029813)
                ·
                  refine ⟨332087109207101074409045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542262498209078127029813 332087109207101074409045)
                  ·
                    rfl

theorem cell21_1455159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 5].length) (baseStart_1455159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455159 prefixEnd_1455159 := by exact prefixLift 1455159
  have htrace : WordTrace (prefixWord ++ tailWord_1455159) baseStart_1455159 baseEnd_1455159 := by
    simpa [prefixWord, tailWord_1455159, baseEnd_1455159] using wordTrace_append hprefix tailTrace_1455159
  have hstable : (prefixWord ++ tailWord_1455159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455159).length < 2 ^ (prefixWord ++ tailWord_1455159).sum := by decide
  have hdescent : baseEnd_1455159 < baseStart_1455159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455207 : List Nat := [1, 1, 5, 1, 1, 3, 3, 2, 4]
def baseStart_1455207 : Nat := 118140960795 + 1455207 * 2 ^ 59
def prefixEnd_1455207 : Nat := 4983230072969 + 3 ^ 40 * 1455207 * 2
def baseEnd_1455207 : Nat := 332098063461063657608947

theorem tailTrace_1455207 : CollatzResearch.WordTrace tailWord_1455207 prefixEnd_1455207 332098063461063657608947 := by
  unfold tailWord_1455207
  simp only [CollatzResearch.WordTrace]
  refine ⟨53075759639041043414259875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35383839759360695609506583 53075759639041043414259875)
  ·
    refine ⟨79613639458561565121389813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53075759639041043414259875 79613639458561565121389813)
    ·
      refine ⟨7463778699240146730130295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79613639458561565121389813 7463778699240146730130295)
      ·
        refine ⟨11195668048860220095195443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7463778699240146730130295 11195668048860220095195443)
        ·
          refine ⟨16793502073290330142793165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11195668048860220095195443 16793502073290330142793165)
          ·
            refine ⟨6297563277483873803547437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16793502073290330142793165 6297563277483873803547437)
            ·
              refine ⟨2361586229056452676330289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6297563277483873803547437 2361586229056452676330289)
              ·
                refine ⟨1771189671792339507247717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361586229056452676330289 1771189671792339507247717)
                ·
                  refine ⟨332098063461063657608947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771189671792339507247717 332098063461063657608947)
                  ·
                    rfl

theorem cell21_1455207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 3, 2, 4].length) (baseStart_1455207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455207 prefixEnd_1455207 := by exact prefixLift 1455207
  have htrace : WordTrace (prefixWord ++ tailWord_1455207) baseStart_1455207 baseEnd_1455207 := by
    simpa [prefixWord, tailWord_1455207, baseEnd_1455207] using wordTrace_append hprefix tailTrace_1455207
  have hstable : (prefixWord ++ tailWord_1455207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455207).length < 2 ^ (prefixWord ++ tailWord_1455207).sum := by decide
  have hdescent : baseEnd_1455207 < baseStart_1455207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455230 : List Nat := [4, 2, 4, 1, 2, 1, 2, 5]
def baseStart_1455230 : Nat := 118140960795 + 1455230 * 2 ^ 59
def prefixEnd_1455230 : Nat := 4983230072969 + 3 ^ 40 * 1455230 * 2
def baseEnd_1455230 : Nat := 110701104124806909575189

theorem tailTrace_1455230 : CollatzResearch.WordTrace tailWord_1455230 prefixEnd_1455230 110701104124806909575189 := by
  unfold tailWord_1455230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6634574814744714792793393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35384399011971812228231429 6634574814744714792793393)
  ·
    refine ⟨4975931111058536094595045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6634574814744714792793393 4975931111058536094595045)
    ·
      refine ⟨932987083323475517736571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4975931111058536094595045 932987083323475517736571)
      ·
        refine ⟨1399480624985213276604857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932987083323475517736571 1399480624985213276604857)
        ·
          refine ⟨1049610468738909957453643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1399480624985213276604857 1049610468738909957453643)
          ·
            refine ⟨1574415703108364936180465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049610468738909957453643 1574415703108364936180465)
            ·
              refine ⟨1180811777331273702135349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1574415703108364936180465 1180811777331273702135349)
              ·
                refine ⟨110701104124806909575189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1180811777331273702135349 110701104124806909575189)
                ·
                  rfl

theorem cell21_1455230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 2, 1, 2, 5].length) (baseStart_1455230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455230 prefixEnd_1455230 := by exact prefixLift 1455230
  have htrace : WordTrace (prefixWord ++ tailWord_1455230) baseStart_1455230 baseEnd_1455230 := by
    simpa [prefixWord, tailWord_1455230, baseEnd_1455230] using wordTrace_append hprefix tailTrace_1455230
  have hstable : (prefixWord ++ tailWord_1455230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455230).length < 2 ^ (prefixWord ++ tailWord_1455230).sum := by decide
  have hdescent : baseEnd_1455230 < baseStart_1455230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455235 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_1455235 : Nat := 118140960795 + 1455235 * 2 ^ 59
def prefixEnd_1455235 : Nat := 4983230072969 + 3 ^ 40 * 1455235 * 2
def baseEnd_1455235 : Nat := 332104453442541831142223

theorem tailTrace_1455235 : CollatzResearch.WordTrace tailWord_1455235 prefixEnd_1455235 332104453442541831142223 := by
  unfold tailWord_1455235
  simp only [CollatzResearch.WordTrace]
  refine ⟨53076780882939604196279159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35384520588626402797519439 53076780882939604196279159)
  ·
    refine ⟨79615171324409406294418739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53076780882939604196279159 79615171324409406294418739)
    ·
      refine ⟨119422756986614109441628109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79615171324409406294418739 119422756986614109441628109)
      ·
        refine ⟨44783533869980291040610541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119422756986614109441628109 44783533869980291040610541)
        ·
          refine ⟨16793825201242609140228953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44783533869980291040610541 16793825201242609140228953)
          ·
            refine ⟨12595368900931956855171715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16793825201242609140228953 12595368900931956855171715)
            ·
              refine ⟨18893053351397935282757573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12595368900931956855171715 18893053351397935282757573)
              ·
                refine ⟨3542447503387112865517045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18893053351397935282757573 3542447503387112865517045)
                ·
                  refine ⟨332104453442541831142223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3542447503387112865517045 332104453442541831142223)
                  ·
                    rfl

theorem cell21_1455235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_1455235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455235 prefixEnd_1455235 := by exact prefixLift 1455235
  have htrace : WordTrace (prefixWord ++ tailWord_1455235) baseStart_1455235 baseEnd_1455235 := by
    simpa [prefixWord, tailWord_1455235, baseEnd_1455235] using wordTrace_append hprefix tailTrace_1455235
  have hstable : (prefixWord ++ tailWord_1455235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455235).length < 2 ^ (prefixWord ++ tailWord_1455235).sum := by decide
  have hdescent : baseEnd_1455235 < baseStart_1455235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455283 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 4]
def baseStart_1455283 : Nat := 118140960795 + 1455283 * 2 ^ 59
def prefixEnd_1455283 : Nat := 4983230072969 + 3 ^ 40 * 1455283 * 2
def baseEnd_1455283 : Nat := 332115407696504414342125

theorem tailTrace_1455283 : CollatzResearch.WordTrace tailWord_1455283 prefixEnd_1455283 332115407696504414342125 := by
  unfold tailWord_1455283
  simp only [CollatzResearch.WordTrace]
  refine ⟨53078531586765708394026503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35385687724510472262684335 53078531586765708394026503)
  ·
    refine ⟨79617797380148562591039755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53078531586765708394026503 79617797380148562591039755)
    ·
      refine ⟨119426696070222843886559633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79617797380148562591039755 119426696070222843886559633)
      ·
        refine ⟨89570022052667132914919725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119426696070222843886559633 89570022052667132914919725)
        ·
          refine ⟨33588758269750174843094897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89570022052667132914919725 33588758269750174843094897)
          ·
            refine ⟨25191568702312631132321173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33588758269750174843094897 25191568702312631132321173)
            ·
              refine ⟨1180854782920904584327555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25191568702312631132321173 1180854782920904584327555)
              ·
                refine ⟨1771282174381356876491333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180854782920904584327555 1771282174381356876491333)
                ·
                  refine ⟨332115407696504414342125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771282174381356876491333 332115407696504414342125)
                  ·
                    rfl

theorem cell21_1455283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 4].length) (baseStart_1455283 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455283 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455283 prefixEnd_1455283 := by exact prefixLift 1455283
  have htrace : WordTrace (prefixWord ++ tailWord_1455283) baseStart_1455283 baseEnd_1455283 := by
    simpa [prefixWord, tailWord_1455283, baseEnd_1455283] using wordTrace_append hprefix tailTrace_1455283
  have hstable : (prefixWord ++ tailWord_1455283).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455283).length < 2 ^ (prefixWord ++ tailWord_1455283).sum := by decide
  have hdescent : baseEnd_1455283 < baseStart_1455283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455497 : List Nat := [1, 2, 1, 1, 7, 1, 1, 4, 3]
def baseStart_1455497 : Nat := 118140960795 + 1455497 * 2 ^ 59
def prefixEnd_1455497 : Nat := 4983230072969 + 3 ^ 40 * 1455497 * 2
def baseEnd_1455497 : Nat := 332164245412087597775021

theorem tailTrace_1455497 : CollatzResearch.WordTrace tailWord_1455497 prefixEnd_1455497 332164245412087597775021 := by
  unfold tailWord_1455497
  simp only [CollatzResearch.WordTrace]
  refine ⟨53086336807990422942316745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35390891205326948628211163 53086336807990422942316745)
  ·
    refine ⟨39814752605992817206737559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53086336807990422942316745 39814752605992817206737559)
    ·
      refine ⟨59722128908989225810106339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39814752605992817206737559 59722128908989225810106339)
      ·
        refine ⟨89583193363483838715159509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59722128908989225810106339 89583193363483838715159509)
        ·
          refine ⟨2099606094456652469886551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 89583193363483838715159509 2099606094456652469886551)
          ·
            refine ⟨3149409141684978704829827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099606094456652469886551 3149409141684978704829827)
            ·
              refine ⟨4724113712527468057244741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149409141684978704829827 4724113712527468057244741)
              ·
                refine ⟨885771321098900260733389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4724113712527468057244741 885771321098900260733389)
                ·
                  refine ⟨332164245412087597775021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885771321098900260733389 332164245412087597775021)
                  ·
                    rfl

theorem cell21_1455497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 4, 3].length) (baseStart_1455497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455497 prefixEnd_1455497 := by exact prefixLift 1455497
  have htrace : WordTrace (prefixWord ++ tailWord_1455497) baseStart_1455497 baseEnd_1455497 := by
    simpa [prefixWord, tailWord_1455497, baseEnd_1455497] using wordTrace_append hprefix tailTrace_1455497
  have hstable : (prefixWord ++ tailWord_1455497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455497).length < 2 ^ (prefixWord ++ tailWord_1455497).sum := by decide
  have hdescent : baseEnd_1455497 < baseStart_1455497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455556 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_1455556 : Nat := 118140960795 + 1455556 * 2 ^ 59
def prefixEnd_1455556 : Nat := 4983230072969 + 3 ^ 40 * 1455556 * 2
def baseEnd_1455556 : Nat := 332177710015916606291567

theorem tailTrace_1455556 : CollatzResearch.WordTrace tailWord_1455556 prefixEnd_1455556 332177710015916606291567 := by
  unfold tailWord_1455556
  simp only [CollatzResearch.WordTrace]
  refine ⟨26544244357388338009357261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35392325809851117345809681 26544244357388338009357261)
  ·
    refine ⟨9954091634020626753508973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26544244357388338009357261 9954091634020626753508973)
    ·
      refine ⟨3732784362757735032565865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9954091634020626753508973 3732784362757735032565865)
      ·
        refine ⟨2799588272068301274424399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3732784362757735032565865 2799588272068301274424399)
        ·
          refine ⟨4199382408102451911636599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799588272068301274424399 4199382408102451911636599)
          ·
            refine ⟨6299073612153677867454899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4199382408102451911636599 6299073612153677867454899)
            ·
              refine ⟨9448610418230516801182349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299073612153677867454899 9448610418230516801182349)
              ·
                refine ⟨3543228906836443800443381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9448610418230516801182349 3543228906836443800443381)
                ·
                  refine ⟨332177710015916606291567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3543228906836443800443381 332177710015916606291567)
                  ·
                    rfl

theorem cell21_1455556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_1455556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455556 prefixEnd_1455556 := by exact prefixLift 1455556
  have htrace : WordTrace (prefixWord ++ tailWord_1455556) baseStart_1455556 baseEnd_1455556 := by
    simpa [prefixWord, tailWord_1455556, baseEnd_1455556] using wordTrace_append hprefix tailTrace_1455556
  have hstable : (prefixWord ++ tailWord_1455556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455556).length < 2 ^ (prefixWord ++ tailWord_1455556).sum := by decide
  have hdescent : baseEnd_1455556 < baseStart_1455556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455618 : List Nat := [3, 4, 1, 2, 1, 2, 2, 6]
def baseStart_1455618 : Nat := 118140960795 + 1455618 * 2 ^ 59
def prefixEnd_1455618 : Nat := 4983230072969 + 3 ^ 40 * 1455618 * 2
def baseEnd_1455618 : Nat := 110730619753539425419369

theorem tailTrace_1455618 : CollatzResearch.WordTrace tailWord_1455618 prefixEnd_1455618 110730619753539425419369 := by
  unfold tailWord_1455618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13272687510138015151867877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35393833360368040404981005 13272687510138015151867877)
  ·
    refine ⟨2488628908150877840975227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13272687510138015151867877 2488628908150877840975227)
    ·
      refine ⟨3732943362226316761462841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2488628908150877840975227 3732943362226316761462841)
      ·
        refine ⟨2799707521669737571097131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3732943362226316761462841 2799707521669737571097131)
        ·
          refine ⟨4199561282504606356645697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2799707521669737571097131 4199561282504606356645697)
          ·
            refine ⟨3149670961878454767484273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4199561282504606356645697 3149670961878454767484273)
            ·
              refine ⟨2362253221408841075613205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149670961878454767484273 2362253221408841075613205)
              ·
                refine ⟨110730619753539425419369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2362253221408841075613205 110730619753539425419369)
                ·
                  rfl

theorem cell21_1455618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 6].length) (baseStart_1455618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455618 prefixEnd_1455618 := by exact prefixLift 1455618
  have htrace : WordTrace (prefixWord ++ tailWord_1455618) baseStart_1455618 baseEnd_1455618 := by
    simpa [prefixWord, tailWord_1455618, baseEnd_1455618] using wordTrace_append hprefix tailTrace_1455618
  have hstable : (prefixWord ++ tailWord_1455618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455618).length < 2 ^ (prefixWord ++ tailWord_1455618).sum := by decide
  have hdescent : baseEnd_1455618 < baseStart_1455618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455722 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1455722 : Nat := 118140960795 + 1455722 * 2 ^ 59
def prefixEnd_1455722 : Nat := 4983230072969 + 3 ^ 40 * 1455722 * 2
def baseEnd_1455722 : Nat := 332215593477537206524561

theorem tailTrace_1455722 : CollatzResearch.WordTrace tailWord_1455722 prefixEnd_1455722 332215593477537206524561 := by
  unfold tailWord_1455722
  simp only [CollatzResearch.WordTrace]
  refine ⟨13273635808043821592314355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35396362154783524246171613 13273635808043821592314355)
  ·
    refine ⟨19910453712065732388471533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13273635808043821592314355 19910453712065732388471533)
    ·
      refine ⟨7466420142024649645676825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19910453712065732388471533 7466420142024649645676825)
      ·
        refine ⟨5599815106518487234257619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7466420142024649645676825 5599815106518487234257619)
        ·
          refine ⟨8399722659777730851386429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599815106518487234257619 8399722659777730851386429)
          ·
            refine ⟨3149895997416649069269911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8399722659777730851386429 3149895997416649069269911)
            ·
              refine ⟨4724843996124973603904867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149895997416649069269911 4724843996124973603904867)
              ·
                refine ⟨7087265994187460405857301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724843996124973603904867 7087265994187460405857301)
                ·
                  refine ⟨332215593477537206524561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7087265994187460405857301 332215593477537206524561)
                  ·
                    rfl

theorem cell21_1455722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1455722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455722 prefixEnd_1455722 := by exact prefixLift 1455722
  have htrace : WordTrace (prefixWord ++ tailWord_1455722) baseStart_1455722 baseEnd_1455722 := by
    simpa [prefixWord, tailWord_1455722, baseEnd_1455722] using wordTrace_append hprefix tailTrace_1455722
  have hstable : (prefixWord ++ tailWord_1455722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455722).length < 2 ^ (prefixWord ++ tailWord_1455722).sum := by decide
  have hdescent : baseEnd_1455722 < baseStart_1455722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455781 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_1455781 : Nat := 118140960795 + 1455781 * 2 ^ 59
def prefixEnd_1455781 : Nat := 4983230072969 + 3 ^ 40 * 1455781 * 2
def baseEnd_1455781 : Nat := 332229058081366215041107

theorem tailTrace_1455781 : CollatzResearch.WordTrace tailWord_1455781 prefixEnd_1455781 332229058081366215041107 := by
  unfold tailWord_1455781
  simp only [CollatzResearch.WordTrace]
  refine ⟨53096695138961539445655197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35397796759307692963770131 53096695138961539445655197)
  ·
    refine ⟨19911260677110577292120699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53096695138961539445655197 19911260677110577292120699)
    ·
      refine ⟨29866891015665865938181049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19911260677110577292120699 29866891015665865938181049)
      ·
        refine ⟨22400168261749399453635787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29866891015665865938181049 22400168261749399453635787)
        ·
          refine ⟨33600252392624099180453681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22400168261749399453635787 33600252392624099180453681)
          ·
            refine ⟨25200189294468074385340261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33600252392624099180453681 25200189294468074385340261)
            ·
              refine ⟨4725035492712763947251299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25200189294468074385340261 4725035492712763947251299)
              ·
                refine ⟨7087553239069145920876949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725035492712763947251299 7087553239069145920876949)
                ·
                  refine ⟨332229058081366215041107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7087553239069145920876949 332229058081366215041107)
                  ·
                    rfl

theorem cell21_1455781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_1455781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455781 prefixEnd_1455781 := by exact prefixLift 1455781
  have htrace : WordTrace (prefixWord ++ tailWord_1455781) baseStart_1455781 baseEnd_1455781 := by
    simpa [prefixWord, tailWord_1455781, baseEnd_1455781] using wordTrace_append hprefix tailTrace_1455781
  have hstable : (prefixWord ++ tailWord_1455781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455781).length < 2 ^ (prefixWord ++ tailWord_1455781).sum := by decide
  have hdescent : baseEnd_1455781 < baseStart_1455781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455790 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1455790 : Nat := 118140960795 + 1455790 * 2 ^ 59
def prefixEnd_1455790 : Nat := 4983230072969 + 3 ^ 40 * 1455790 * 2
def baseEnd_1455790 : Nat := 332231112003984199391089

theorem tailTrace_1455790 : CollatzResearch.WordTrace tailWord_1455790 prefixEnd_1455790 332231112003984199391089 := by
  unfold tailWord_1455790
  simp only [CollatzResearch.WordTrace]
  refine ⟨6637127924491116747841603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35398015597285955988488549 6637127924491116747841603)
  ·
    refine ⟨9955691886736675121762405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6637127924491116747841603 9955691886736675121762405)
    ·
      refine ⟨1866692228763126585330451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9955691886736675121762405 1866692228763126585330451)
      ·
        refine ⟨2800038343144689877995677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866692228763126585330451 2800038343144689877995677)
        ·
          refine ⟨1050014378679258704248379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2800038343144689877995677 1050014378679258704248379)
          ·
            refine ⟨1575021568018888056372569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050014378679258704248379 1575021568018888056372569)
            ·
              refine ⟨1181266176014166042279427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575021568018888056372569 1181266176014166042279427)
              ·
                refine ⟨1771899264021249063419141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181266176014166042279427 1771899264021249063419141)
                ·
                  refine ⟨332231112003984199391089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1771899264021249063419141 332231112003984199391089)
                  ·
                    rfl

theorem cell21_1455790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1455790 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455790 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455790 prefixEnd_1455790 := by exact prefixLift 1455790
  have htrace : WordTrace (prefixWord ++ tailWord_1455790) baseStart_1455790 baseEnd_1455790 := by
    simpa [prefixWord, tailWord_1455790, baseEnd_1455790] using wordTrace_append hprefix tailTrace_1455790
  have hstable : (prefixWord ++ tailWord_1455790).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455790).length < 2 ^ (prefixWord ++ tailWord_1455790).sum := by decide
  have hdescent : baseEnd_1455790 < baseStart_1455790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455812 : List Nat := [2, 3, 3, 1, 1, 1, 1, 9]
def baseStart_1455812 : Nat := 118140960795 + 1455812 * 2 ^ 59
def prefixEnd_1455812 : Nat := 4983230072969 + 3 ^ 40 * 1455812 * 2
def baseEnd_1455812 : Nat := 110745377567905683341459

theorem tailTrace_1455812 : CollatzResearch.WordTrace tailWord_1455812 prefixEnd_1455812 110745377567905683341459 := by
  unfold tailWord_1455812
  simp only [CollatzResearch.WordTrace]
  refine ⟨26548912900924615870016845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35398550534566154493355793 26548912900924615870016845)
  ·
    refine ⟨9955842337846730951256317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26548912900924615870016845 9955842337846730951256317)
    ·
      refine ⟨3733440876692524106721119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9955842337846730951256317 3733440876692524106721119)
      ·
        refine ⟨5600161315038786160081679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733440876692524106721119 5600161315038786160081679)
        ·
          refine ⟨8400241972558179240122519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600161315038786160081679 8400241972558179240122519)
          ·
            refine ⟨12600362958837268860183779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400241972558179240122519 12600362958837268860183779)
            ·
              refine ⟨18900544438255903290275669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12600362958837268860183779 18900544438255903290275669)
              ·
                refine ⟨110745377567905683341459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18900544438255903290275669 110745377567905683341459)
                ·
                  rfl

theorem cell21_1455812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 9].length) (baseStart_1455812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455812 prefixEnd_1455812 := by exact prefixLift 1455812
  have htrace : WordTrace (prefixWord ++ tailWord_1455812) baseStart_1455812 baseEnd_1455812 := by
    simpa [prefixWord, tailWord_1455812, baseEnd_1455812] using wordTrace_append hprefix tailTrace_1455812
  have hstable : (prefixWord ++ tailWord_1455812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455812).length < 2 ^ (prefixWord ++ tailWord_1455812).sum := by decide
  have hdescent : baseEnd_1455812 < baseStart_1455812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455871 : List Nat := [1, 1, 2, 2, 1, 3, 2, 9]
def baseStart_1455871 : Nat := 118140960795 + 1455871 * 2 ^ 59
def prefixEnd_1455871 : Nat := 4983230072969 + 3 ^ 40 * 1455871 * 2
def baseEnd_1455871 : Nat := 110749865769182019513641

theorem tailTrace_1455871 : CollatzResearch.WordTrace tailWord_1455871 prefixEnd_1455871 110749865769182019513641 := by
  unfold tailWord_1455871
  simp only [CollatzResearch.WordTrace]
  refine ⟨53099977708635484816431467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35399985139090323210954311 53099977708635484816431467)
  ·
    refine ⟨79649966562953227224647201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53099977708635484816431467 79649966562953227224647201)
    ·
      refine ⟨59737474922214920418485401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79649966562953227224647201 59737474922214920418485401)
      ·
        refine ⟨44803106191661190313864051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59737474922214920418485401 44803106191661190313864051)
        ·
          refine ⟨67204659287491785470796077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44803106191661190313864051 67204659287491785470796077)
          ·
            refine ⟨25201747232809419551548529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67204659287491785470796077 25201747232809419551548529)
            ·
              refine ⟨18901310424607064663661397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25201747232809419551548529 18901310424607064663661397)
              ·
                refine ⟨110749865769182019513641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18901310424607064663661397 110749865769182019513641)
                ·
                  rfl

theorem cell21_1455871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_1455871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455871 prefixEnd_1455871 := by exact prefixLift 1455871
  have htrace : WordTrace (prefixWord ++ tailWord_1455871) baseStart_1455871 baseEnd_1455871 := by
    simpa [prefixWord, tailWord_1455871, baseEnd_1455871] using wordTrace_append hprefix tailTrace_1455871
  have hstable : (prefixWord ++ tailWord_1455871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455871).length < 2 ^ (prefixWord ++ tailWord_1455871).sum := by decide
  have hdescent : baseEnd_1455871 < baseStart_1455871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455874 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1455874 : Nat := 118140960795 + 1455874 * 2 ^ 59
def prefixEnd_1455874 : Nat := 4983230072969 + 3 ^ 40 * 1455874 * 2
def baseEnd_1455874 : Nat := 332250281948418719990917

theorem tailTrace_1455874 : CollatzResearch.WordTrace tailWord_1455874 prefixEnd_1455874 332250281948418719990917 := by
  unfold tailWord_1455874
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275021781906154082197669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35400058085083077552527117 13275021781906154082197669)
  ·
    refine ⟨2489066584107403890412063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13275021781906154082197669 2489066584107403890412063)
    ·
      refine ⟨3733599876161105835618095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2489066584107403890412063 3733599876161105835618095)
      ·
        refine ⟨5600399814241658753427143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3733599876161105835618095 5600399814241658753427143)
        ·
          refine ⟨8400599721362488130140715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5600399814241658753427143 8400599721362488130140715)
          ·
            refine ⟨12600899582043732195211073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8400599721362488130140715 12600899582043732195211073)
            ·
              refine ⟨9450674686532799146408305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12600899582043732195211073 9450674686532799146408305)
              ·
                refine ⟨7088006014899599359806229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9450674686532799146408305 7088006014899599359806229)
                ·
                  refine ⟨332250281948418719990917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7088006014899599359806229 332250281948418719990917)
                  ·
                    rfl

theorem cell21_1455874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1455874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455874 prefixEnd_1455874 := by exact prefixLift 1455874
  have htrace : WordTrace (prefixWord ++ tailWord_1455874) baseStart_1455874 baseEnd_1455874 := by
    simpa [prefixWord, tailWord_1455874, baseEnd_1455874] using wordTrace_append hprefix tailTrace_1455874
  have hstable : (prefixWord ++ tailWord_1455874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455874).length < 2 ^ (prefixWord ++ tailWord_1455874).sum := by decide
  have hdescent : baseEnd_1455874 < baseStart_1455874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455953 : List Nat := [1, 2, 2, 1, 5, 2, 3, 2, 3]
def baseStart_1455953 : Nat := 118140960795 + 1455953 * 2 ^ 59
def prefixEnd_1455953 : Nat := 4983230072969 + 3 ^ 40 * 1455953 * 2
def baseEnd_1455953 : Nat := 332268310824732138174089

theorem tailTrace_1455953 : CollatzResearch.WordTrace tailWord_1455953 prefixEnd_1455953 332268310824732138174089 := by
  unfold tailWord_1455953
  simp only [CollatzResearch.WordTrace]
  refine ⟨53102968494338412820916513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35401978996225608547277675 53102968494338412820916513)
  ·
    refine ⟨39827226370753809615687385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53102968494338412820916513 39827226370753809615687385)
    ·
      refine ⟨29870419778065357211765539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39827226370753809615687385 29870419778065357211765539)
      ·
        refine ⟨44805629667098035817648309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29870419778065357211765539 44805629667098035817648309)
        ·
          refine ⟨4200527781290440857904529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44805629667098035817648309 4200527781290440857904529)
          ·
            refine ⟨3150395835967830643428397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4200527781290440857904529 3150395835967830643428397)
            ·
              refine ⟨1181398438487936491285649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3150395835967830643428397 1181398438487936491285649)
              ·
                refine ⟨886048828865952368464237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1181398438487936491285649 886048828865952368464237)
                ·
                  refine ⟨332268310824732138174089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886048828865952368464237 332268310824732138174089)
                  ·
                    rfl

theorem cell21_1455953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 3, 2, 3].length) (baseStart_1455953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455953 prefixEnd_1455953 := by exact prefixLift 1455953
  have htrace : WordTrace (prefixWord ++ tailWord_1455953) baseStart_1455953 baseEnd_1455953 := by
    simpa [prefixWord, tailWord_1455953, baseEnd_1455953] using wordTrace_append hprefix tailTrace_1455953
  have hstable : (prefixWord ++ tailWord_1455953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455953).length < 2 ^ (prefixWord ++ tailWord_1455953).sum := by decide
  have hdescent : baseEnd_1455953 < baseStart_1455953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455967 : List Nat := [1, 1, 2, 3, 1, 6, 2, 1, 4]
def baseStart_1455967 : Nat := 118140960795 + 1455967 * 2 ^ 59
def prefixEnd_1455967 : Nat := 4983230072969 + 3 ^ 40 * 1455967 * 2
def baseEnd_1455967 : Nat := 332271505815471224940727

theorem tailTrace_1455967 : CollatzResearch.WordTrace tailWord_1455967 prefixEnd_1455967 332271505815471224940727 := by
  unfold tailWord_1455967
  simp only [CollatzResearch.WordTrace]
  refine ⟨53103479116287693211926155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35402319410858462141284103 53103479116287693211926155)
  ·
    refine ⟨79655218674431539817889233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53103479116287693211926155 79655218674431539817889233)
    ·
      refine ⟨59741414005823654863416925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79655218674431539817889233 59741414005823654863416925)
      ·
        refine ⟨22403030252183870573781347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59741414005823654863416925 22403030252183870573781347)
        ·
          refine ⟨33604545378275805860672021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22403030252183870573781347 33604545378275805860672021)
          ·
            refine ⟨1575213064606678399719001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33604545378275805860672021 1575213064606678399719001)
            ·
              refine ⟨1181409798455008799789251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575213064606678399719001 1181409798455008799789251)
              ·
                refine ⟨1772114697682513199683877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181409798455008799789251 1772114697682513199683877)
                ·
                  refine ⟨332271505815471224940727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772114697682513199683877 332271505815471224940727)
                  ·
                    rfl

theorem cell21_1455967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 4].length) (baseStart_1455967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455967 prefixEnd_1455967 := by exact prefixLift 1455967
  have htrace : WordTrace (prefixWord ++ tailWord_1455967) baseStart_1455967 baseEnd_1455967 := by
    simpa [prefixWord, tailWord_1455967, baseEnd_1455967] using wordTrace_append hprefix tailTrace_1455967
  have hstable : (prefixWord ++ tailWord_1455967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455967).length < 2 ^ (prefixWord ++ tailWord_1455967).sum := by decide
  have hdescent : baseEnd_1455967 < baseStart_1455967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455995 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 3]
def baseStart_1455995 : Nat := 118140960795 + 1455995 * 2 ^ 59
def prefixEnd_1455995 : Nat := 4983230072969 + 3 ^ 40 * 1455995 * 2
def baseEnd_1455995 : Nat := 332277895796949398474003

theorem tailTrace_1455995 : CollatzResearch.WordTrace tailWord_1455995 prefixEnd_1455995 332277895796949398474003 := by
  unfold tailWord_1455995
  simp only [CollatzResearch.WordTrace]
  refine ⟨53104500360186253993945439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35403000240124169329296959 53104500360186253993945439)
  ·
    refine ⟨79656750540279380990918159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53104500360186253993945439 79656750540279380990918159)
    ·
      refine ⟨119485125810419071486377239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79656750540279380990918159 119485125810419071486377239)
      ·
        refine ⟨179227688715628607229565859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119485125810419071486377239 179227688715628607229565859)
        ·
          refine ⟨268841533073442910844348789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179227688715628607229565859 268841533073442910844348789)
          ·
            refine ⟨25203893725635272891657699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 268841533073442910844348789 25203893725635272891657699)
            ·
              refine ⟨37805840588452909337486549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25203893725635272891657699 37805840588452909337486549)
              ·
                refine ⟨886074388791865062597341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 37805840588452909337486549 886074388791865062597341)
                ·
                  refine ⟨332277895796949398474003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886074388791865062597341 332277895796949398474003)
                  ·
                    rfl

theorem cell21_1455995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 3].length) (baseStart_1455995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1455995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1455995 prefixEnd_1455995 := by exact prefixLift 1455995
  have htrace : WordTrace (prefixWord ++ tailWord_1455995) baseStart_1455995 baseEnd_1455995 := by
    simpa [prefixWord, tailWord_1455995, baseEnd_1455995] using wordTrace_append hprefix tailTrace_1455995
  have hstable : (prefixWord ++ tailWord_1455995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455995).length < 2 ^ (prefixWord ++ tailWord_1455995).sum := by decide
  have hdescent : baseEnd_1455995 < baseStart_1455995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456026 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_1456026 : Nat := 118140960795 + 1456026 * 2 ^ 59
def prefixEnd_1456026 : Nat := 4983230072969 + 3 ^ 40 * 1456026 * 2
def baseEnd_1456026 : Nat := 332284970419300233457273

theorem tailTrace_1456026 : CollatzResearch.WordTrace tailWord_1456026 prefixEnd_1456026 332284970419300233457273 := by
  unfold tailWord_1456026
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276407755768486572080983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35403754015382630858882621 13276407755768486572080983)
  ·
    refine ⟨19914611633652729858121475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13276407755768486572080983 19914611633652729858121475)
    ·
      refine ⟨29871917450479094787182213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19914611633652729858121475 29871917450479094787182213)
      ·
        refine ⟨5600984521964830272596665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29871917450479094787182213 5600984521964830272596665)
        ·
          refine ⟨4200738391473622704447499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600984521964830272596665 4200738391473622704447499)
          ·
            refine ⟨6301107587210434056671249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200738391473622704447499 6301107587210434056671249)
            ·
              refine ⟨4725830690407825542503437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6301107587210434056671249 4725830690407825542503437)
              ·
                refine ⟨1772186508902934578438789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4725830690407825542503437 1772186508902934578438789)
                ·
                  refine ⟨332284970419300233457273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772186508902934578438789 332284970419300233457273)
                  ·
                    rfl

theorem cell21_1456026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_1456026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456026 prefixEnd_1456026 := by exact prefixLift 1456026
  have htrace : WordTrace (prefixWord ++ tailWord_1456026) baseStart_1456026 baseEnd_1456026 := by
    simpa [prefixWord, tailWord_1456026, baseEnd_1456026] using wordTrace_append hprefix tailTrace_1456026
  have hstable : (prefixWord ++ tailWord_1456026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456026).length < 2 ^ (prefixWord ++ tailWord_1456026).sum := by decide
  have hdescent : baseEnd_1456026 < baseStart_1456026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456060 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_1456060 : Nat := 118140960795 + 1456060 * 2 ^ 59
def prefixEnd_1456060 : Nat := 4983230072969 + 3 ^ 40 * 1456060 * 2
def baseEnd_1456060 : Nat := 332292729682523729890537

theorem tailTrace_1456060 : CollatzResearch.WordTrace tailWord_1456060 prefixEnd_1456060 332292729682523729890537 := by
  unfold tailWord_1456060
  simp only [CollatzResearch.WordTrace]
  refine ⟨26553435552475385047530817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35404580736633846730041089 26553435552475385047530817)
  ·
    refine ⟨19915076664356538785648113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26553435552475385047530817 19915076664356538785648113)
    ·
      refine ⟨14936307498267404089236085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19915076664356538785648113 14936307498267404089236085)
      ·
        refine ⟨1400278827962569133365883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14936307498267404089236085 1400278827962569133365883)
        ·
          refine ⟨2100418241943853700048825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400278827962569133365883 2100418241943853700048825)
          ·
            refine ⟨1575313681457890275036619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100418241943853700048825 1575313681457890275036619)
            ·
              refine ⟨2362970522186835412554929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575313681457890275036619 2362970522186835412554929)
              ·
                refine ⟨1772227891640126559416197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362970522186835412554929 1772227891640126559416197)
                ·
                  refine ⟨332292729682523729890537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772227891640126559416197 332292729682523729890537)
                  ·
                    rfl

theorem cell21_1456060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_1456060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456060 prefixEnd_1456060 := by exact prefixLift 1456060
  have htrace : WordTrace (prefixWord ++ tailWord_1456060) baseStart_1456060 baseEnd_1456060 := by
    simpa [prefixWord, tailWord_1456060, baseEnd_1456060] using wordTrace_append hprefix tailTrace_1456060
  have hstable : (prefixWord ++ tailWord_1456060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456060).length < 2 ^ (prefixWord ++ tailWord_1456060).sum := by decide
  have hdescent : baseEnd_1456060 < baseStart_1456060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456178 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1456178 : Nat := 118140960795 + 1456178 * 2 ^ 59
def prefixEnd_1456178 : Nat := 4983230072969 + 3 ^ 40 * 1456178 * 2
def baseEnd_1456178 : Nat := 332319658890181746923629

theorem tailTrace_1456178 : CollatzResearch.WordTrace tailWord_1456178 prefixEnd_1456178 332319658890181746923629 := by
  unfold tailWord_1456178
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277793729630819061964297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35407449945682184165238125 13277793729630819061964297)
  ·
    refine ⟨9958345297223114296473223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13277793729630819061964297 9958345297223114296473223)
    ·
      refine ⟨14937517945834671444709835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958345297223114296473223 14937517945834671444709835)
      ·
        refine ⟨22406276918752007167064753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14937517945834671444709835 22406276918752007167064753)
        ·
          refine ⟨16804707689064005375298565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22406276918752007167064753 16804707689064005375298565)
          ·
            refine ⟨3150882691699501007868481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16804707689064005375298565 3150882691699501007868481)
            ·
              refine ⟨2363162018774625755901361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150882691699501007868481 2363162018774625755901361)
              ·
                refine ⟨1772371514080969316926021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363162018774625755901361 1772371514080969316926021)
                ·
                  refine ⟨332319658890181746923629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772371514080969316926021 332319658890181746923629)
                  ·
                    rfl

theorem cell21_1456178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1456178 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456178 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456178 prefixEnd_1456178 := by exact prefixLift 1456178
  have htrace : WordTrace (prefixWord ++ tailWord_1456178) baseStart_1456178 baseEnd_1456178 := by
    simpa [prefixWord, tailWord_1456178, baseEnd_1456178] using wordTrace_append hprefix tailTrace_1456178
  have hstable : (prefixWord ++ tailWord_1456178).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456178).length < 2 ^ (prefixWord ++ tailWord_1456178).sum := by decide
  have hdescent : baseEnd_1456178 < baseStart_1456178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456192 : List Nat := [2, 1, 1, 2, 2, 6, 1, 6]
def baseStart_1456192 : Nat := 118140960795 + 1456192 * 2 ^ 59
def prefixEnd_1456192 : Nat := 4983230072969 + 3 ^ 40 * 1456192 * 2
def baseEnd_1456192 : Nat := 110774284626973611230089

theorem tailTrace_1456192 : CollatzResearch.WordTrace tailWord_1456192 prefixEnd_1456192 110774284626973611230089 := by
  unfold tailWord_1456192
  simp only [CollatzResearch.WordTrace]
  refine ⟨26555842770236278319433415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35407790360315037759244553 26555842770236278319433415)
  ·
    refine ⟨39833764155354417479150123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26555842770236278319433415 39833764155354417479150123)
    ·
      refine ⟨59750646233031626218725185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39833764155354417479150123 59750646233031626218725185)
      ·
        refine ⟨44812984674773719664043889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59750646233031626218725185 44812984674773719664043889)
        ·
          refine ⟨33609738506080289748032917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44812984674773719664043889 33609738506080289748032917)
          ·
            refine ⟨1575456492472513581939043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33609738506080289748032917 1575456492472513581939043)
            ·
              refine ⟨2363184738708770372908565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575456492472513581939043 2363184738708770372908565)
              ·
                refine ⟨110774284626973611230089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2363184738708770372908565 110774284626973611230089)
                ·
                  rfl

theorem cell21_1456192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_1456192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456192 prefixEnd_1456192 := by exact prefixLift 1456192
  have htrace : WordTrace (prefixWord ++ tailWord_1456192) baseStart_1456192 baseEnd_1456192 := by
    simpa [prefixWord, tailWord_1456192, baseEnd_1456192] using wordTrace_append hprefix tailTrace_1456192
  have hstable : (prefixWord ++ tailWord_1456192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456192).length < 2 ^ (prefixWord ++ tailWord_1456192).sum := by decide
  have hdescent : baseEnd_1456192 < baseStart_1456192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456206 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_1456206 : Nat := 118140960795 + 1456206 * 2 ^ 59
def prefixEnd_1456206 : Nat := 4983230072969 + 3 ^ 40 * 1456206 * 2
def baseEnd_1456206 : Nat := 332326048871659920456905

theorem tailTrace_1456206 : CollatzResearch.WordTrace tailWord_1456206 prefixEnd_1456206 332326048871659920456905 := by
  unfold tailWord_1456206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639024520302729628734559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35408130774947891353250981 6639024520302729628734559)
  ·
    refine ⟨9958536780454094443101839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6639024520302729628734559 9958536780454094443101839)
    ·
      refine ⟨14937805170681141664652759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9958536780454094443101839 14937805170681141664652759)
      ·
        refine ⟨22406707756021712496979139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14937805170681141664652759 22406707756021712496979139)
        ·
          refine ⟨33610061634032568745468709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22406707756021712496979139 33610061634032568745468709)
          ·
            refine ⟨6301886556381106639775383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33610061634032568745468709 6301886556381106639775383)
            ·
              refine ⟨9452829834571659959663075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301886556381106639775383 9452829834571659959663075)
              ·
                refine ⟨14179244751857489939494613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9452829834571659959663075 14179244751857489939494613)
                ·
                  refine ⟨332326048871659920456905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14179244751857489939494613 332326048871659920456905)
                  ·
                    rfl

theorem cell21_1456206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_1456206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456206 prefixEnd_1456206 := by exact prefixLift 1456206
  have htrace : WordTrace (prefixWord ++ tailWord_1456206) baseStart_1456206 baseEnd_1456206 := by
    simpa [prefixWord, tailWord_1456206, baseEnd_1456206] using wordTrace_append hprefix tailTrace_1456206
  have hstable : (prefixWord ++ tailWord_1456206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456206).length < 2 ^ (prefixWord ++ tailWord_1456206).sum := by decide
  have hdescent : baseEnd_1456206 < baseStart_1456206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456237 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_1456237 : Nat := 118140960795 + 1456237 * 2 ^ 59
def prefixEnd_1456237 : Nat := 4983230072969 + 3 ^ 40 * 1456237 * 2
def baseEnd_1456237 : Nat := 332333123494010755440175

theorem tailTrace_1456237 : CollatzResearch.WordTrace tailWord_1456237 prefixEnd_1456237 332333123494010755440175 := by
  unfold tailWord_1456237
  simp only [CollatzResearch.WordTrace]
  refine ⟨53113326825309529324254965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35408884550206352882836643 53113326825309529324254965)
  ·
    refine ⟨4979374389872768374148903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53113326825309529324254965 4979374389872768374148903)
    ·
      refine ⟨7469061584809152561223355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4979374389872768374148903 7469061584809152561223355)
      ·
        refine ⟨11203592377213728841835033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469061584809152561223355 11203592377213728841835033)
        ·
          refine ⟨8402694282910296631376275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11203592377213728841835033 8402694282910296631376275)
          ·
            refine ⟨12604041424365444947064413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8402694282910296631376275 12604041424365444947064413)
            ·
              refine ⟨4726515534137041855149155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12604041424365444947064413 4726515534137041855149155)
              ·
                refine ⟨7089773301205562782723733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726515534137041855149155 7089773301205562782723733)
                ·
                  refine ⟨332333123494010755440175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7089773301205562782723733 332333123494010755440175)
                  ·
                    rfl

theorem cell21_1456237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_1456237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456237 prefixEnd_1456237 := by exact prefixLift 1456237
  have htrace : WordTrace (prefixWord ++ tailWord_1456237) baseStart_1456237 baseEnd_1456237 := by
    simpa [prefixWord, tailWord_1456237, baseEnd_1456237] using wordTrace_append hprefix tailTrace_1456237
  have hstable : (prefixWord ++ tailWord_1456237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456237).length < 2 ^ (prefixWord ++ tailWord_1456237).sum := by decide
  have hdescent : baseEnd_1456237 < baseStart_1456237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456302 : List Nat := [4, 1, 4, 2, 1, 1, 2, 6]
def baseStart_1456302 : Nat := 118140960795 + 1456302 * 2 ^ 59
def prefixEnd_1456302 : Nat := 4983230072969 + 3 ^ 40 * 1456302 * 2
def baseEnd_1456302 : Nat := 110782652459861695618903

theorem tailTrace_1456302 : CollatzResearch.WordTrace tailWord_1456302 prefixEnd_1456302 110782652459861695618903 := by
  unfold tailWord_1456302
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639462196259255678171395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35410465046716030283580773 6639462196259255678171395)
  ·
    refine ⟨9959193294388883517257093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6639462196259255678171395 9959193294388883517257093)
    ·
      refine ⟨1867348742697915659485705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9959193294388883517257093 1867348742697915659485705)
      ·
        refine ⟨1400511557023436744614279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1867348742697915659485705 1400511557023436744614279)
        ·
          refine ⟨2100767335535155116921419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400511557023436744614279 2100767335535155116921419)
          ·
            refine ⟨3151151003302732675382129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100767335535155116921419 3151151003302732675382129)
            ·
              refine ⟨2363363252477049506536597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3151151003302732675382129 2363363252477049506536597)
              ·
                refine ⟨110782652459861695618903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2363363252477049506536597 110782652459861695618903)
                ·
                  rfl

theorem cell21_1456302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_1456302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456302 prefixEnd_1456302 := by exact prefixLift 1456302
  have htrace : WordTrace (prefixWord ++ tailWord_1456302) baseStart_1456302 baseEnd_1456302 := by
    simpa [prefixWord, tailWord_1456302, baseEnd_1456302] using wordTrace_append hprefix tailTrace_1456302
  have hstable : (prefixWord ++ tailWord_1456302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456302).length < 2 ^ (prefixWord ++ tailWord_1456302).sum := by decide
  have hdescent : baseEnd_1456302 < baseStart_1456302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456313 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 4]
def baseStart_1456313 : Nat := 118140960795 + 1456313 * 2 ^ 59
def prefixEnd_1456313 : Nat := 4983230072969 + 3 ^ 40 * 1456313 * 2
def baseEnd_1456313 : Nat := 332350467729451512173353

theorem tailTrace_1456313 : CollatzResearch.WordTrace tailWord_1456313 prefixEnd_1456313 332350467729451512173353 := by
  unfold tailWord_1456313
  simp only [CollatzResearch.WordTrace]
  refine ⟨53116098773034194304021593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35410732515356129536014395 53116098773034194304021593)
  ·
    refine ⟨39837074079775645728016195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53116098773034194304021593 39837074079775645728016195)
    ·
      refine ⟨59755611119663468592024293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39837074079775645728016195 59755611119663468592024293)
      ·
        refine ⟨11204177084936900361004555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59755611119663468592024293 11204177084936900361004555)
        ·
          refine ⟨16806265627405350541506833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11204177084936900361004555 16806265627405350541506833)
          ·
            refine ⟨12604699220554012906130125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16806265627405350541506833 12604699220554012906130125)
            ·
              refine ⟨4726762207707754839798797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12604699220554012906130125 4726762207707754839798797)
              ·
                refine ⟨1772535827890408064924549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4726762207707754839798797 1772535827890408064924549)
                ·
                  refine ⟨332350467729451512173353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772535827890408064924549 332350467729451512173353)
                  ·
                    rfl

theorem cell21_1456313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 4].length) (baseStart_1456313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456313 prefixEnd_1456313 := by exact prefixLift 1456313
  have htrace : WordTrace (prefixWord ++ tailWord_1456313) baseStart_1456313 baseEnd_1456313 := by
    simpa [prefixWord, tailWord_1456313, baseEnd_1456313] using wordTrace_append hprefix tailTrace_1456313
  have hstable : (prefixWord ++ tailWord_1456313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456313).length < 2 ^ (prefixWord ++ tailWord_1456313).sum := by decide
  have hdescent : baseEnd_1456313 < baseStart_1456313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456392 : List Nat := [2, 1, 3, 2, 3, 2, 2, 3, 3]
def baseStart_1456392 : Nat := 118140960795 + 1456392 * 2 ^ 59
def prefixEnd_1456392 : Nat := 4983230072969 + 3 ^ 40 * 1456392 * 2
def baseEnd_1456392 : Nat := 332368496605764930356525

theorem tailTrace_1456392 : CollatzResearch.WordTrace tailWord_1456392 prefixEnd_1456392 332368496605764930356525 := by
  unfold tailWord_1456392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26559490069873995398073715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35412653426498660530764953 26559490069873995398073715)
  ·
    refine ⟨39839235104810993097110573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26559490069873995398073715 39839235104810993097110573)
    ·
      refine ⟨14939713164304122411416465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39839235104810993097110573 14939713164304122411416465)
      ·
        refine ⟨11204784873228091808562349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14939713164304122411416465 11204784873228091808562349)
        ·
          refine ⟨4201794327460534428210881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11204784873228091808562349 4201794327460534428210881)
          ·
            refine ⟨3151345745595400821158161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4201794327460534428210881 3151345745595400821158161)
            ·
              refine ⟨2363509309196550615868621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3151345745595400821158161 2363509309196550615868621)
              ·
                refine ⟨886315990948706480950733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2363509309196550615868621 886315990948706480950733)
                ·
                  refine ⟨332368496605764930356525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886315990948706480950733 332368496605764930356525)
                  ·
                    rfl

theorem cell21_1456392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 2, 3, 3].length) (baseStart_1456392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456392 prefixEnd_1456392 := by exact prefixLift 1456392
  have htrace : WordTrace (prefixWord ++ tailWord_1456392) baseStart_1456392 baseEnd_1456392 := by
    simpa [prefixWord, tailWord_1456392, baseEnd_1456392] using wordTrace_append hprefix tailTrace_1456392
  have hstable : (prefixWord ++ tailWord_1456392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456392).length < 2 ^ (prefixWord ++ tailWord_1456392).sum := by decide
  have hdescent : baseEnd_1456392 < baseStart_1456392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456451 : List Nat := [1, 1, 1, 3, 1, 3, 5, 3, 3]
def baseStart_1456451 : Nat := 118140960795 + 1456451 * 2 ^ 59
def prefixEnd_1456451 : Nat := 4983230072969 + 3 ^ 40 * 1456451 * 2
def baseEnd_1456451 : Nat := 332381961209593938873071

theorem tailTrace_1456451 : CollatzResearch.WordTrace tailWord_1456451 prefixEnd_1456451 332381961209593938873071 := by
  unfold tailWord_1456451
  simp only [CollatzResearch.WordTrace]
  refine ⟨53121132046534243872545207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35414088031022829248363471 53121132046534243872545207)
  ·
    refine ⟨79681698069801365808817811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53121132046534243872545207 79681698069801365808817811)
    ·
      refine ⟨119522547104702048713226717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79681698069801365808817811 119522547104702048713226717)
      ·
        refine ⟨44820955164263268267460019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119522547104702048713226717 44820955164263268267460019)
        ·
          refine ⟨67231432746394902401190029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44820955164263268267460019 67231432746394902401190029)
          ·
            refine ⟨25211787279898088400446261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67231432746394902401190029 25211787279898088400446261)
            ·
              refine ⟨2363605057490445787541837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25211787279898088400446261 2363605057490445787541837)
              ·
                refine ⟨886351896558917170328189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2363605057490445787541837 886351896558917170328189)
                ·
                  refine ⟨332381961209593938873071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886351896558917170328189 332381961209593938873071)
                  ·
                    rfl

theorem cell21_1456451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 3, 3].length) (baseStart_1456451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456451 prefixEnd_1456451 := by exact prefixLift 1456451
  have htrace : WordTrace (prefixWord ++ tailWord_1456451) baseStart_1456451 baseEnd_1456451 := by
    simpa [prefixWord, tailWord_1456451, baseEnd_1456451] using wordTrace_append hprefix tailTrace_1456451
  have hstable : (prefixWord ++ tailWord_1456451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456451).length < 2 ^ (prefixWord ++ tailWord_1456451).sum := by decide
  have hdescent : baseEnd_1456451 < baseStart_1456451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456482 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_1456482 : Nat := 118140960795 + 1456482 * 2 ^ 59
def prefixEnd_1456482 : Nat := 4983230072969 + 3 ^ 40 * 1456482 * 2
def baseEnd_1456482 : Nat := 332389035831944773856341

theorem tailTrace_1456482 : CollatzResearch.WordTrace tailWord_1456482 prefixEnd_1456482 332389035831944773856341 := by
  unfold tailWord_1456482
  simp only [CollatzResearch.WordTrace]
  refine ⟨13280565677355484041730925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35414841806281290777949133 13280565677355484041730925)
  ·
    refine ⟨4980212129008306515649097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13280565677355484041730925 4980212129008306515649097)
    ·
      refine ⟨3735159096756229886736823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4980212129008306515649097 3735159096756229886736823)
      ·
        refine ⟨5602738645134344830105235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735159096756229886736823 5602738645134344830105235)
        ·
          refine ⟨8404107967701517245157853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5602738645134344830105235 8404107967701517245157853)
          ·
            refine ⟨3151540487888068966934195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8404107967701517245157853 3151540487888068966934195)
            ·
              refine ⟨4727310731832103450401293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151540487888068966934195 4727310731832103450401293)
              ·
                refine ⟨1772741524437038793900485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4727310731832103450401293 1772741524437038793900485)
                ·
                  refine ⟨332389035831944773856341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772741524437038793900485 332389035831944773856341)
                  ·
                    rfl

theorem cell21_1456482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_1456482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456482 prefixEnd_1456482 := by exact prefixLift 1456482
  have htrace : WordTrace (prefixWord ++ tailWord_1456482) baseStart_1456482 baseEnd_1456482 := by
    simpa [prefixWord, tailWord_1456482, baseEnd_1456482] using wordTrace_append hprefix tailTrace_1456482
  have hstable : (prefixWord ++ tailWord_1456482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456482).length < 2 ^ (prefixWord ++ tailWord_1456482).sum := by decide
  have hdescent : baseEnd_1456482 < baseStart_1456482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456586 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1456586 : Nat := 118140960795 + 1456586 * 2 ^ 59
def prefixEnd_1456586 : Nat := 4983230072969 + 3 ^ 40 * 1456586 * 2
def baseEnd_1456586 : Nat := 332412770048863704122795

theorem tailTrace_1456586 : CollatzResearch.WordTrace tailWord_1456586 prefixEnd_1456586 332412770048863704122795 := by
  unfold tailWord_1456586
  simp only [CollatzResearch.WordTrace]
  refine ⟨13281513975261290482177403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35417370600696774619139741 13281513975261290482177403)
  ·
    refine ⟨19922270962891935723266105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13281513975261290482177403 19922270962891935723266105)
    ·
      refine ⟨14941703222168951792449579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19922270962891935723266105 14941703222168951792449579)
      ·
        refine ⟨22412554833253427688674369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14941703222168951792449579 22412554833253427688674369)
        ·
          refine ⟨16809416124940070766505777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22412554833253427688674369 16809416124940070766505777)
          ·
            refine ⟨12607062093705053074879333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16809416124940070766505777 12607062093705053074879333)
            ·
              refine ⟨2363824142569697451539875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12607062093705053074879333 2363824142569697451539875)
              ·
                refine ⟨3545736213854546177309813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363824142569697451539875 3545736213854546177309813)
                ·
                  refine ⟨332412770048863704122795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3545736213854546177309813 332412770048863704122795)
                  ·
                    rfl

theorem cell21_1456586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1456586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456586 prefixEnd_1456586 := by exact prefixLift 1456586
  have htrace : WordTrace (prefixWord ++ tailWord_1456586) baseStart_1456586 baseEnd_1456586 := by
    simpa [prefixWord, tailWord_1456586, baseEnd_1456586] using wordTrace_append hprefix tailTrace_1456586
  have hstable : (prefixWord ++ tailWord_1456586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456586).length < 2 ^ (prefixWord ++ tailWord_1456586).sum := by decide
  have hdescent : baseEnd_1456586 < baseStart_1456586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456693 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 4]
def baseStart_1456693 : Nat := 118140960795 + 1456693 * 2 ^ 59
def prefixEnd_1456693 : Nat := 4983230072969 + 3 ^ 40 * 1456693 * 2
def baseEnd_1456693 : Nat := 332437188906655295839243

theorem tailTrace_1456693 : CollatzResearch.WordTrace tailWord_1456693 prefixEnd_1456693 332437188906655295839243 := by
  unfold tailWord_1456693
  simp only [CollatzResearch.WordTrace]
  refine ⟨53129958511657519202854733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35419972341105012801903155 53129958511657519202854733)
  ·
    refine ⟨19923734441871569701070525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53129958511657519202854733 19923734441871569701070525)
    ·
      refine ⟨7471400415701838637901447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19923734441871569701070525 7471400415701838637901447)
      ·
        refine ⟨11207100623552757956852171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471400415701838637901447 11207100623552757956852171)
        ·
          refine ⟨16810650935329136935278257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11207100623552757956852171 16810650935329136935278257)
          ·
            refine ⟨12607988201496852701458693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16810650935329136935278257 12607988201496852701458693)
            ·
              refine ⟨2363997787780659881523505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12607988201496852701458693 2363997787780659881523505)
              ·
                refine ⟨1772998340835494911142629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363997787780659881523505 1772998340835494911142629)
                ·
                  refine ⟨332437188906655295839243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1772998340835494911142629 332437188906655295839243)
                  ·
                    rfl

theorem cell21_1456693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_1456693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456693 prefixEnd_1456693 := by exact prefixLift 1456693
  have htrace : WordTrace (prefixWord ++ tailWord_1456693) baseStart_1456693 baseEnd_1456693 := by
    simpa [prefixWord, tailWord_1456693, baseEnd_1456693] using wordTrace_append hprefix tailTrace_1456693
  have hstable : (prefixWord ++ tailWord_1456693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456693).length < 2 ^ (prefixWord ++ tailWord_1456693).sum := by decide
  have hdescent : baseEnd_1456693 < baseStart_1456693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456721 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 7]
def baseStart_1456721 : Nat := 118140960795 + 1456721 * 2 ^ 59
def prefixEnd_1456721 : Nat := 4983230072969 + 3 ^ 40 * 1456721 * 2
def baseEnd_1456721 : Nat := 332443578888133469372519

theorem tailTrace_1456721 : CollatzResearch.WordTrace tailWord_1456721 prefixEnd_1456721 332443578888133469372519 := by
  unfold tailWord_1456721
  simp only [CollatzResearch.WordTrace]
  refine ⟨53130979755556079984874017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35420653170370719989916011 53130979755556079984874017)
  ·
    refine ⟨39848234816667059988655513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53130979755556079984874017 39848234816667059988655513)
    ·
      refine ⟨29886176112500294991491635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39848234816667059988655513 29886176112500294991491635)
      ·
        refine ⟨44829264168750442487237453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29886176112500294991491635 44829264168750442487237453)
        ·
          refine ⟨16810974063281415932714045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44829264168750442487237453 16810974063281415932714045)
          ·
            refine ⟨6304115273730530974767767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16810974063281415932714045 6304115273730530974767767)
            ·
              refine ⟨9456172910595796462151651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6304115273730530974767767 9456172910595796462151651)
              ·
                refine ⟨14184259365893694693227477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456172910595796462151651 14184259365893694693227477)
                ·
                  refine ⟨332443578888133469372519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14184259365893694693227477 332443578888133469372519)
                  ·
                    rfl

theorem cell21_1456721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_1456721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456721 prefixEnd_1456721 := by exact prefixLift 1456721
  have htrace : WordTrace (prefixWord ++ tailWord_1456721) baseStart_1456721 baseEnd_1456721 := by
    simpa [prefixWord, tailWord_1456721, baseEnd_1456721] using wordTrace_append hprefix tailTrace_1456721
  have hstable : (prefixWord ++ tailWord_1456721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456721).length < 2 ^ (prefixWord ++ tailWord_1456721).sum := by decide
  have hdescent : baseEnd_1456721 < baseStart_1456721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456724 : List Nat := [2, 4, 1, 1, 1, 4, 3, 5]
def baseStart_1456724 : Nat := 118140960795 + 1456724 * 2 ^ 59
def prefixEnd_1456724 : Nat := 4983230072969 + 3 ^ 40 * 1456724 * 2
def baseEnd_1456724 : Nat := 110814754509668710274171

theorem tailTrace_1456724 : CollatzResearch.WordTrace tailWord_1456724 prefixEnd_1456724 110814754509668710274171 := by
  unfold tailWord_1456724
  simp only [CollatzResearch.WordTrace]
  refine ⟨26565544587272605748616613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35420726116363474331488817 26565544587272605748616613)
  ·
    refine ⟨4981039610113613577865615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26565544587272605748616613 4981039610113613577865615)
    ·
      refine ⟨7471559415170420366798423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4981039610113613577865615 7471559415170420366798423)
      ·
        refine ⟨11207339122755630550197635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471559415170420366798423 11207339122755630550197635)
        ·
          refine ⟨16811008684133445825296453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11207339122755630550197635 16811008684133445825296453)
          ·
            refine ⟨3152064128275021092243085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16811008684133445825296453 3152064128275021092243085)
            ·
              refine ⟨1182024048103132909591157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3152064128275021092243085 1182024048103132909591157)
              ·
                refine ⟨110814754509668710274171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1182024048103132909591157 110814754509668710274171)
                ·
                  rfl

theorem cell21_1456724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 5].length) (baseStart_1456724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456724 prefixEnd_1456724 := by exact prefixLift 1456724
  have htrace : WordTrace (prefixWord ++ tailWord_1456724) baseStart_1456724 baseEnd_1456724 := by
    simpa [prefixWord, tailWord_1456724, baseEnd_1456724] using wordTrace_append hprefix tailTrace_1456724
  have hstable : (prefixWord ++ tailWord_1456724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456724).length < 2 ^ (prefixWord ++ tailWord_1456724).sum := by decide
  have hdescent : baseEnd_1456724 < baseStart_1456724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456797 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 7]
def baseStart_1456797 : Nat := 118140960795 + 1456797 * 2 ^ 59
def prefixEnd_1456797 : Nat := 4983230072969 + 3 ^ 40 * 1456797 * 2
def baseEnd_1456797 : Nat := 332460923123574226105697

theorem tailTrace_1456797 : CollatzResearch.WordTrace tailWord_1456797 prefixEnd_1456797 332460923123574226105697 := by
  unfold tailWord_1456797
  simp only [CollatzResearch.WordTrace]
  refine ⟨53133751703280744964640645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35422501135520496643093763 53133751703280744964640645)
  ·
    refine ⟨9962578444365139680870121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53133751703280744964640645 9962578444365139680870121)
    ·
      refine ⟨7471933833273854760652591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9962578444365139680870121 7471933833273854760652591)
      ·
        refine ⟨11207900749910782140978887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471933833273854760652591 11207900749910782140978887)
        ·
          refine ⟨16811851124866173211468331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11207900749910782140978887 16811851124866173211468331)
          ·
            refine ⟨25217776687299259817202497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16811851124866173211468331 25217776687299259817202497)
            ·
              refine ⟨18913332515474444862901873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25217776687299259817202497 18913332515474444862901873)
              ·
                refine ⟨14184999386605833647176405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18913332515474444862901873 14184999386605833647176405)
                ·
                  refine ⟨332460923123574226105697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14184999386605833647176405 332460923123574226105697)
                  ·
                    rfl

theorem cell21_1456797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_1456797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456797 prefixEnd_1456797 := by exact prefixLift 1456797
  have htrace : WordTrace (prefixWord ++ tailWord_1456797) baseStart_1456797 baseEnd_1456797 := by
    simpa [prefixWord, tailWord_1456797, baseEnd_1456797] using wordTrace_append hprefix tailTrace_1456797
  have hstable : (prefixWord ++ tailWord_1456797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456797).length < 2 ^ (prefixWord ++ tailWord_1456797).sum := by decide
  have hdescent : baseEnd_1456797 < baseStart_1456797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456800 : List Nat := [2, 1, 1, 4, 5, 1, 7]
def baseStart_1456800 : Nat := 118140960795 + 1456800 * 2 ^ 59
def prefixEnd_1456800 : Nat := 4983230072969 + 3 ^ 40 * 1456800 * 2
def baseEnd_1456800 : Nat := 36940178640494098617299

theorem tailTrace_1456800 : CollatzResearch.WordTrace tailWord_1456800 prefixEnd_1456800 36940178640494098617299 := by
  unfold tailWord_1456800
  simp only [CollatzResearch.WordTrace]
  refine ⟨26566930561134938238499927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35422574081513250984666569 26566930561134938238499927)
  ·
    refine ⟨39850395841702407357749891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26566930561134938238499927 39850395841702407357749891)
    ·
      refine ⟨59775593762553611036624837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39850395841702407357749891 59775593762553611036624837)
      ·
        refine ⟨11207923830478802069367157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59775593762553611036624837 11207923830478802069367157)
        ·
          refine ⟨1050742859107387694003171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11207923830478802069367157 1050742859107387694003171)
          ·
            refine ⟨1576114288661081541004757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050742859107387694003171 1576114288661081541004757)
            ·
              refine ⟨36940178640494098617299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1576114288661081541004757 36940178640494098617299)
              ·
                rfl

theorem cell21_1456800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 7].length) (baseStart_1456800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456800 prefixEnd_1456800 := by exact prefixLift 1456800
  have htrace : WordTrace (prefixWord ++ tailWord_1456800) baseStart_1456800 baseEnd_1456800 := by
    simpa [prefixWord, tailWord_1456800, baseEnd_1456800] using wordTrace_append hprefix tailTrace_1456800
  have hstable : (prefixWord ++ tailWord_1456800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456800).length < 2 ^ (prefixWord ++ tailWord_1456800).sum := by decide
  have hdescent : baseEnd_1456800 < baseStart_1456800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456887 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 8]
def baseStart_1456887 : Nat := 118140960795 + 1456887 * 2 ^ 59
def prefixEnd_1456887 : Nat := 4983230072969 + 3 ^ 40 * 1456887 * 2
def baseEnd_1456887 : Nat := 332481462349754069605513

theorem tailTrace_1456887 : CollatzResearch.WordTrace tailWord_1456887 prefixEnd_1456887 332481462349754069605513 := by
  unfold tailWord_1456887
  simp only [CollatzResearch.WordTrace]
  refine ⟨53137034272954690335416915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35424689515303126890277943 53137034272954690335416915)
  ·
    refine ⟨79705551409432035503125373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53137034272954690335416915 79705551409432035503125373)
    ·
      refine ⟨29889581778537013313672015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79705551409432035503125373 29889581778537013313672015)
      ·
        refine ⟨44834372667805519970508023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29889581778537013313672015 44834372667805519970508023)
        ·
          refine ⟨67251559001708279955762035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44834372667805519970508023 67251559001708279955762035)
          ·
            refine ⟨100877338502562419933643053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67251559001708279955762035 100877338502562419933643053)
            ·
              refine ⟨37829001938460907475116145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100877338502562419933643053 37829001938460907475116145)
              ·
                refine ⟨28371751453845680606337109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37829001938460907475116145 28371751453845680606337109)
                ·
                  refine ⟨332481462349754069605513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28371751453845680606337109 332481462349754069605513)
                  ·
                    rfl

theorem cell21_1456887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_1456887 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456887 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456887 prefixEnd_1456887 := by exact prefixLift 1456887
  have htrace : WordTrace (prefixWord ++ tailWord_1456887) baseStart_1456887 baseEnd_1456887 := by
    simpa [prefixWord, tailWord_1456887, baseEnd_1456887] using wordTrace_append hprefix tailTrace_1456887
  have hstable : (prefixWord ++ tailWord_1456887).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456887).length < 2 ^ (prefixWord ++ tailWord_1456887).sum := by decide
  have hdescent : baseEnd_1456887 < baseStart_1456887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456963 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_1456963 : Nat := 118140960795 + 1456963 * 2 ^ 59
def prefixEnd_1456963 : Nat := 4983230072969 + 3 ^ 40 * 1456963 * 2
def baseEnd_1456963 : Nat := 332498806585194826338691

theorem tailTrace_1456963 : CollatzResearch.WordTrace tailWord_1456963 prefixEnd_1456963 332498806585194826338691 := by
  unfold tailWord_1456963
  simp only [CollatzResearch.WordTrace]
  refine ⟨53139806220679355315183543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35426537480452903543455695 53139806220679355315183543)
  ·
    refine ⟨79709709331019032972775315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53139806220679355315183543 79709709331019032972775315)
    ·
      refine ⟨119564563996528549459162973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79709709331019032972775315 119564563996528549459162973)
      ·
        refine ⟨44836711498698206047186115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119564563996528549459162973 44836711498698206047186115)
        ·
          refine ⟨67255067248047309070779173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44836711498698206047186115 67255067248047309070779173)
          ·
            refine ⟨12610325109008870450771095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67255067248047309070779173 12610325109008870450771095)
            ·
              refine ⟨18915487663513305676156643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12610325109008870450771095 18915487663513305676156643)
              ·
                refine ⟨28373231495269958514234965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18915487663513305676156643 28373231495269958514234965)
                ·
                  refine ⟨332498806585194826338691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28373231495269958514234965 332498806585194826338691)
                  ·
                    rfl

theorem cell21_1456963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_1456963 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456963 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456963 prefixEnd_1456963 := by exact prefixLift 1456963
  have htrace : WordTrace (prefixWord ++ tailWord_1456963) baseStart_1456963 baseEnd_1456963 := by
    simpa [prefixWord, tailWord_1456963, baseEnd_1456963] using wordTrace_append hprefix tailTrace_1456963
  have hstable : (prefixWord ++ tailWord_1456963).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456963).length < 2 ^ (prefixWord ++ tailWord_1456963).sum := by decide
  have hdescent : baseEnd_1456963 < baseStart_1456963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456997 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 4]
def baseStart_1456997 : Nat := 118140960795 + 1456997 * 2 ^ 59
def prefixEnd_1456997 : Nat := 4983230072969 + 3 ^ 40 * 1456997 * 2
def baseEnd_1456997 : Nat := 332506565848418322771955

theorem tailTrace_1456997 : CollatzResearch.WordTrace tailWord_1456997 prefixEnd_1456997 332506565848418322771955 := by
  unfold tailWord_1456997
  simp only [CollatzResearch.WordTrace]
  refine ⟨53141046302556179121921245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35427364201704119414614163 53141046302556179121921245)
  ·
    refine ⟨19927892363458567170720467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53141046302556179121921245 19927892363458567170720467)
    ·
      refine ⟨29891838545187850756080701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19927892363458567170720467 29891838545187850756080701)
      ·
        refine ⟨11209439454445444033530263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29891838545187850756080701 11209439454445444033530263)
        ·
          refine ⟨16814159181668166050295395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11209439454445444033530263 16814159181668166050295395)
          ·
            refine ⟨25221238772502249075443093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16814159181668166050295395 25221238772502249075443093)
            ·
              refine ⟨1182245567461042925411395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25221238772502249075443093 1182245567461042925411395)
              ·
                refine ⟨1773368351191564388117093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182245567461042925411395 1773368351191564388117093)
                ·
                  refine ⟨332506565848418322771955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773368351191564388117093 332506565848418322771955)
                  ·
                    rfl

theorem cell21_1456997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 4].length) (baseStart_1456997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1456997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1456997 prefixEnd_1456997 := by exact prefixLift 1456997
  have htrace : WordTrace (prefixWord ++ tailWord_1456997) baseStart_1456997 baseEnd_1456997 := by
    simpa [prefixWord, tailWord_1456997, baseEnd_1456997] using wordTrace_append hprefix tailTrace_1456997
  have hstable : (prefixWord ++ tailWord_1456997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456997).length < 2 ^ (prefixWord ++ tailWord_1456997).sum := by decide
  have hdescent : baseEnd_1456997 < baseStart_1456997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457056 : List Nat := [2, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_1457056 : Nat := 118140960795 + 1457056 * 2 ^ 59
def prefixEnd_1457056 : Nat := 4983230072969 + 3 ^ 40 * 1457056 * 2
def baseEnd_1457056 : Nat := 332520030452247331288501

theorem tailTrace_1457056 : CollatzResearch.WordTrace tailWord_1457056 prefixEnd_1457056 332520030452247331288501 := by
  unfold tailWord_1457056
  simp only [CollatzResearch.WordTrace]
  refine ⟨26571599104671216099159511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35428798806228288132212681 26571599104671216099159511)
  ·
    refine ⟨39857398657006824148739267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26571599104671216099159511 39857398657006824148739267)
    ·
      refine ⟨59786097985510236223108901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39857398657006824148739267 59786097985510236223108901)
      ·
        refine ⟨11209893372283169291832919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59786097985510236223108901 11209893372283169291832919)
        ·
          refine ⟨16814840058424753937749379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11209893372283169291832919 16814840058424753937749379)
          ·
            refine ⟨25222260087637130906624069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16814840058424753937749379 25222260087637130906624069)
            ·
              refine ⟨4729173766431962044992013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25222260087637130906624069 4729173766431962044992013)
              ·
                refine ⟨1773440162411985766872005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4729173766431962044992013 1773440162411985766872005)
                ·
                  refine ⟨332520030452247331288501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773440162411985766872005 332520030452247331288501)
                  ·
                    rfl

theorem cell21_1457056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_1457056 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457056 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457056 prefixEnd_1457056 := by exact prefixLift 1457056
  have htrace : WordTrace (prefixWord ++ tailWord_1457056) baseStart_1457056 baseEnd_1457056 := by
    simpa [prefixWord, tailWord_1457056, baseEnd_1457056] using wordTrace_append hprefix tailTrace_1457056
  have hstable : (prefixWord ++ tailWord_1457056).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457056).length < 2 ^ (prefixWord ++ tailWord_1457056).sum := by decide
  have hdescent : baseEnd_1457056 < baseStart_1457056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457076 : List Nat := [2, 5, 2, 1, 1, 1, 1, 5, 3]
def baseStart_1457076 : Nat := 118140960795 + 1457076 * 2 ^ 59
def prefixEnd_1457076 : Nat := 4983230072969 + 3 ^ 40 * 1457076 * 2
def baseEnd_1457076 : Nat := 332524594724731740955127

theorem tailTrace_1457076 : CollatzResearch.WordTrace tailWord_1457076 prefixEnd_1457076 332524594724731740955127 := by
  unfold tailWord_1457076
  simp only [CollatzResearch.WordTrace]
  refine ⟨26571963834634987807023541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35429285112846650409364721 26571963834634987807023541)
  ·
    refine ⟨2491121609497030106908457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26571963834634987807023541 2491121609497030106908457)
    ·
      refine ⟨1868341207122772580181343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2491121609497030106908457 1868341207122772580181343)
      ·
        refine ⟨2802511810684158870272015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868341207122772580181343 2802511810684158870272015)
        ·
          refine ⟨4203767716026238305408023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802511810684158870272015 4203767716026238305408023)
          ·
            refine ⟨6305651574039357458112035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203767716026238305408023 6305651574039357458112035)
            ·
              refine ⟨9458477361059036187168053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305651574039357458112035 9458477361059036187168053)
              ·
                refine ⟨886732252599284642547005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9458477361059036187168053 886732252599284642547005)
                ·
                  refine ⟨332524594724731740955127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886732252599284642547005 332524594724731740955127)
                  ·
                    rfl

theorem cell21_1457076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_1457076 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457076 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457076 prefixEnd_1457076 := by exact prefixLift 1457076
  have htrace : WordTrace (prefixWord ++ tailWord_1457076) baseStart_1457076 baseEnd_1457076 := by
    simpa [prefixWord, tailWord_1457076, baseEnd_1457076] using wordTrace_append hprefix tailTrace_1457076
  have hstable : (prefixWord ++ tailWord_1457076).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457076).length < 2 ^ (prefixWord ++ tailWord_1457076).sum := by decide
  have hdescent : baseEnd_1457076 < baseStart_1457076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457135 : List Nat := [1, 1, 2, 1, 4, 5, 1, 3, 3]
def baseStart_1457135 : Nat := 118140960795 + 1457135 * 2 ^ 59
def prefixEnd_1457135 : Nat := 4983230072969 + 3 ^ 40 * 1457135 * 2
def baseEnd_1457135 : Nat := 332538059328560749471673

theorem tailTrace_1457135 : CollatzResearch.WordTrace tailWord_1457135 prefixEnd_1457135 332538059328560749471673 := by
  unfold tailWord_1457135
  simp only [CollatzResearch.WordTrace]
  refine ⟨53146079576056228690444859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35430719717370819126963239 53146079576056228690444859)
  ·
    refine ⟨79719119364084343035667289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53146079576056228690444859 79719119364084343035667289)
    ·
      refine ⟨59789339523063257276750467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79719119364084343035667289 59789339523063257276750467)
      ·
        refine ⟨89684009284594885915125701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59789339523063257276750467 89684009284594885915125701)
        ·
          refine ⟨16815751740861541109086069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89684009284594885915125701 16815751740861541109086069)
          ·
            refine ⟨1576476725705769478976819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16815751740861541109086069 1576476725705769478976819)
            ·
              refine ⟨2364715088558654218465229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576476725705769478976819 2364715088558654218465229)
              ·
                refine ⟨886768158209495331924461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2364715088558654218465229 886768158209495331924461)
                ·
                  refine ⟨332538059328560749471673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886768158209495331924461 332538059328560749471673)
                  ·
                    rfl

theorem cell21_1457135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 3, 3].length) (baseStart_1457135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457135 prefixEnd_1457135 := by exact prefixLift 1457135
  have htrace : WordTrace (prefixWord ++ tailWord_1457135) baseStart_1457135 baseEnd_1457135 := by
    simpa [prefixWord, tailWord_1457135, baseEnd_1457135] using wordTrace_append hprefix tailTrace_1457135
  have hstable : (prefixWord ++ tailWord_1457135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457135).length < 2 ^ (prefixWord ++ tailWord_1457135).sum := by decide
  have hdescent : baseEnd_1457135 < baseStart_1457135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457166 : List Nat := [4, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_1457166 : Nat := 118140960795 + 1457166 * 2 ^ 59
def prefixEnd_1457166 : Nat := 4983230072969 + 3 ^ 40 * 1457166 * 2
def baseEnd_1457166 : Nat := 332545133950911584454943

theorem tailTrace_1457166 : CollatzResearch.WordTrace tailWord_1457166 prefixEnd_1457166 332545133950911584454943 := by
  unfold tailWord_1457166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643401279867990123102919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35431473492629280656548901 6643401279867990123102919)
  ·
    refine ⟨9965101919801985184654379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6643401279867990123102919 9965101919801985184654379)
    ·
      refine ⟨14947652879702977776981569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9965101919801985184654379 14947652879702977776981569)
      ·
        refine ⟨11210739659777233332736177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14947652879702977776981569 11210739659777233332736177)
        ·
          refine ⟨8408054744832924999552133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11210739659777233332736177 8408054744832924999552133)
          ·
            refine ⟨1576510264656173437416025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8408054744832924999552133 1576510264656173437416025)
            ·
              refine ⟨1182382698492130078062019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576510264656173437416025 1182382698492130078062019)
              ·
                refine ⟨1773574047738195117093029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182382698492130078062019 1773574047738195117093029)
                ·
                  refine ⟨332545133950911584454943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773574047738195117093029 332545133950911584454943)
                  ·
                    rfl

theorem cell21_1457166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_1457166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457166 prefixEnd_1457166 := by exact prefixLift 1457166
  have htrace : WordTrace (prefixWord ++ tailWord_1457166) baseStart_1457166 baseEnd_1457166 := by
    simpa [prefixWord, tailWord_1457166, baseEnd_1457166] using wordTrace_append hprefix tailTrace_1457166
  have hstable : (prefixWord ++ tailWord_1457166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457166).length < 2 ^ (prefixWord ++ tailWord_1457166).sum := by decide
  have hdescent : baseEnd_1457166 < baseStart_1457166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457208 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_1457208 : Nat := 118140960795 + 1457208 * 2 ^ 59
def prefixEnd_1457208 : Nat := 4983230072969 + 3 ^ 40 * 1457208 * 2
def baseEnd_1457208 : Nat := 332554718923128844754857

theorem tailTrace_1457208 : CollatzResearch.WordTrace tailWord_1457208 prefixEnd_1457208 332554718923128844754857 := by
  unfold tailWord_1457208
  simp only [CollatzResearch.WordTrace]
  refine ⟨26574371052395881078926139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35432494736527841438568185 26574371052395881078926139)
  ·
    refine ⟨39861556578593821618389209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26574371052395881078926139 39861556578593821618389209)
    ·
      refine ⟨29896167433945366213791907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39861556578593821618389209 29896167433945366213791907)
      ·
        refine ⟨44844251150918049320687861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29896167433945366213791907 44844251150918049320687861)
        ·
          refine ⟨4204148545398567123814487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44844251150918049320687861 4204148545398567123814487)
          ·
            refine ⟨6306222818097850685721731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204148545398567123814487 6306222818097850685721731)
            ·
              refine ⟨9459334227146776028582597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306222818097850685721731 9459334227146776028582597)
              ·
                refine ⟨1773625167590020505359237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9459334227146776028582597 1773625167590020505359237)
                ·
                  refine ⟨332554718923128844754857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773625167590020505359237 332554718923128844754857)
                  ·
                    rfl

theorem cell21_1457208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_1457208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457208 prefixEnd_1457208 := by exact prefixLift 1457208
  have htrace : WordTrace (prefixWord ++ tailWord_1457208) baseStart_1457208 baseEnd_1457208 := by
    simpa [prefixWord, tailWord_1457208, baseEnd_1457208] using wordTrace_append hprefix tailTrace_1457208
  have hstable : (prefixWord ++ tailWord_1457208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457208).length < 2 ^ (prefixWord ++ tailWord_1457208).sum := by decide
  have hdescent : baseEnd_1457208 < baseStart_1457208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457270 : List Nat := [5, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1457270 : Nat := 118140960795 + 1457270 * 2 ^ 59
def prefixEnd_1457270 : Nat := 4983230072969 + 3 ^ 40 * 1457270 * 2
def baseEnd_1457270 : Nat := 332568868167830514721397

theorem tailTrace_1457270 : CollatzResearch.WordTrace tailWord_1457270 prefixEnd_1457270 332568868167830514721397 := by
  unfold tailWord_1457270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3321937714410446671663079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35434002287044764497739509 3321937714410446671663079)
  ·
    refine ⟨4982906571615670007494619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3321937714410446671663079 4982906571615670007494619)
    ·
      refine ⟨7474359857423505011241929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4982906571615670007494619 7474359857423505011241929)
      ·
        refine ⟨5605769893067628758431447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7474359857423505011241929 5605769893067628758431447)
        ·
          refine ⟨8408654839601443137647171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5605769893067628758431447 8408654839601443137647171)
          ·
            refine ⟨12612982259402164706470757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8408654839601443137647171 12612982259402164706470757)
            ·
              refine ⟨2364934173637905882463267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12612982259402164706470757 2364934173637905882463267)
              ·
                refine ⟨3547401260456858823694901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364934173637905882463267 3547401260456858823694901)
                ·
                  refine ⟨332568868167830514721397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3547401260456858823694901 332568868167830514721397)
                  ·
                    rfl

theorem cell21_1457270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1457270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457270 prefixEnd_1457270 := by exact prefixLift 1457270
  have htrace : WordTrace (prefixWord ++ tailWord_1457270) baseStart_1457270 baseEnd_1457270 := by
    simpa [prefixWord, tailWord_1457270, baseEnd_1457270] using wordTrace_append hprefix tailTrace_1457270
  have hstable : (prefixWord ++ tailWord_1457270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457270).length < 2 ^ (prefixWord ++ tailWord_1457270).sum := by decide
  have hdescent : baseEnd_1457270 < baseStart_1457270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457391 : List Nat := [1, 1, 2, 1, 7, 2, 1, 6]
def baseStart_1457391 : Nat := 118140960795 + 1457391 * 2 ^ 59
def prefixEnd_1457391 : Nat := 4983230072969 + 3 ^ 40 * 1457391 * 2
def baseEnd_1457391 : Nat := 110865494005453731068161

theorem tailTrace_1457391 : CollatzResearch.WordTrace tailWord_1457391 prefixEnd_1457391 110865494005453731068161 := by
  unfold tailWord_1457391
  simp only [CollatzResearch.WordTrace]
  refine ⟨53155416663128784411764027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35436944442085856274509351 53155416663128784411764027)
  ·
    refine ⟨79733124994693176617646041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53155416663128784411764027 79733124994693176617646041)
    ·
      refine ⟨59799843746019882463234531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79733124994693176617646041 59799843746019882463234531)
      ·
        refine ⟨89699765619029823694851797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59799843746019882463234531 89699765619029823694851797)
        ·
          refine ⟨2102338256696011492848089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 89699765619029823694851797 2102338256696011492848089)
          ·
            refine ⟨1576753692522008619636067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2102338256696011492848089 1576753692522008619636067)
            ·
              refine ⟨2365130538783012929454101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576753692522008619636067 2365130538783012929454101)
              ·
                refine ⟨110865494005453731068161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2365130538783012929454101 110865494005453731068161)
                ·
                  rfl

theorem cell21_1457391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 6].length) (baseStart_1457391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457391 prefixEnd_1457391 := by exact prefixLift 1457391
  have htrace : WordTrace (prefixWord ++ tailWord_1457391) baseStart_1457391 baseEnd_1457391 := by
    simpa [prefixWord, tailWord_1457391, baseEnd_1457391] using wordTrace_append hprefix tailTrace_1457391
  have hstable : (prefixWord ++ tailWord_1457391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457391).length < 2 ^ (prefixWord ++ tailWord_1457391).sum := by decide
  have hdescent : baseEnd_1457391 < baseStart_1457391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457422 : List Nat := [4, 1, 1, 2, 1, 3, 1, 5, 3]
def baseStart_1457422 : Nat := 118140960795 + 1457422 * 2 ^ 59
def prefixEnd_1457422 : Nat := 4983230072969 + 3 ^ 40 * 1457422 * 2
def baseEnd_1457422 : Nat := 332603556638712028187753

theorem tailTrace_1457422 : CollatzResearch.WordTrace tailWord_1457422 prefixEnd_1457422 332603556638712028187753 := by
  unfold tailWord_1457422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6644568415752059588267815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35437698217344317804095013 6644568415752059588267815)
  ·
    refine ⟨9966852623628089382401723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6644568415752059588267815 9966852623628089382401723)
    ·
      refine ⟨14950278935442134073602585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9966852623628089382401723 14950278935442134073602585)
      ·
        refine ⟨11212709201581600555201939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14950278935442134073602585 11212709201581600555201939)
        ·
          refine ⟨16819063802372400832802909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11212709201581600555201939 16819063802372400832802909)
          ·
            refine ⟨6307148925889650312301091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16819063802372400832802909 6307148925889650312301091)
            ·
              refine ⟨9460723388834475468451637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6307148925889650312301091 9460723388834475468451637)
              ·
                refine ⟨886942817703232075167341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9460723388834475468451637 886942817703232075167341)
                ·
                  refine ⟨332603556638712028187753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886942817703232075167341 332603556638712028187753)
                  ·
                    rfl

theorem cell21_1457422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 5, 3].length) (baseStart_1457422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457422 prefixEnd_1457422 := by exact prefixLift 1457422
  have htrace : WordTrace (prefixWord ++ tailWord_1457422) baseStart_1457422 baseEnd_1457422 := by
    simpa [prefixWord, tailWord_1457422, baseEnd_1457422] using wordTrace_append hprefix tailTrace_1457422
  have hstable : (prefixWord ++ tailWord_1457422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457422).length < 2 ^ (prefixWord ++ tailWord_1457422).sum := by decide
  have hdescent : baseEnd_1457422 < baseStart_1457422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457436 : List Nat := [2, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_1457436 : Nat := 118140960795 + 1457436 * 2 ^ 59
def prefixEnd_1457436 : Nat := 4983230072969 + 3 ^ 40 * 1457436 * 2
def baseEnd_1457436 : Nat := 332606751629451114954391

theorem tailTrace_1457436 : CollatzResearch.WordTrace tailWord_1457436 prefixEnd_1457436 332606751629451114954391 := by
  unfold tailWord_1457436
  simp only [CollatzResearch.WordTrace]
  refine ⟨26578528973982878548576081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35438038631977171398101441 26578528973982878548576081)
  ·
    refine ⟨19933896730487158911432061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26578528973982878548576081 19933896730487158911432061)
    ·
      refine ⟨7475211273932684591787023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19933896730487158911432061 7475211273932684591787023)
      ·
        refine ⟨11212816910899026887680535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475211273932684591787023 11212816910899026887680535)
        ·
          refine ⟨16819225366348540331520803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11212816910899026887680535 16819225366348540331520803)
          ·
            refine ⟨25228838049522810497281205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16819225366348540331520803 25228838049522810497281205)
            ·
              refine ⟨2365203567142763484120113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25228838049522810497281205 2365203567142763484120113)
              ·
                refine ⟨1773902675357072613090085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2365203567142763484120113 1773902675357072613090085)
                ·
                  refine ⟨332606751629451114954391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1773902675357072613090085 332606751629451114954391)
                  ·
                    rfl

theorem cell21_1457436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_1457436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457436 prefixEnd_1457436 := by exact prefixLift 1457436
  have htrace : WordTrace (prefixWord ++ tailWord_1457436) baseStart_1457436 baseEnd_1457436 := by
    simpa [prefixWord, tailWord_1457436, baseEnd_1457436] using wordTrace_append hprefix tailTrace_1457436
  have hstable : (prefixWord ++ tailWord_1457436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457436).length < 2 ^ (prefixWord ++ tailWord_1457436).sum := by decide
  have hdescent : baseEnd_1457436 < baseStart_1457436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457495 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 6]
def baseStart_1457495 : Nat := 118140960795 + 1457495 * 2 ^ 59
def prefixEnd_1457495 : Nat := 4983230072969 + 3 ^ 40 * 1457495 * 2
def baseEnd_1457495 : Nat := 332620216233280123470937

theorem tailTrace_1457495 : CollatzResearch.WordTrace tailWord_1457495 prefixEnd_1457495 332620216233280123470937 := by
  unfold tailWord_1457495
  simp only [CollatzResearch.WordTrace]
  refine ⟨53159209854752010173549939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35439473236501340115699959 53159209854752010173549939)
  ·
    refine ⟨79738814782128015260324909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53159209854752010173549939 79738814782128015260324909)
    ·
      refine ⟨29902055543298005722621841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79738814782128015260324909 29902055543298005722621841)
      ·
        refine ⟨22426541657473504291966381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29902055543298005722621841 22426541657473504291966381)
        ·
          refine ⟨8409953121552564109487393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22426541657473504291966381 8409953121552564109487393)
          ·
            refine ⟨6307464841164423082115545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8409953121552564109487393 6307464841164423082115545)
            ·
              refine ⟨4730598630873317311586659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6307464841164423082115545 4730598630873317311586659)
              ·
                refine ⟨7095897946309975967379989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730598630873317311586659 7095897946309975967379989)
                ·
                  refine ⟨332620216233280123470937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7095897946309975967379989 332620216233280123470937)
                  ·
                    rfl

theorem cell21_1457495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 6].length) (baseStart_1457495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457495 prefixEnd_1457495 := by exact prefixLift 1457495
  have htrace : WordTrace (prefixWord ++ tailWord_1457495) baseStart_1457495 baseEnd_1457495 := by
    simpa [prefixWord, tailWord_1457495, baseEnd_1457495] using wordTrace_append hprefix tailTrace_1457495
  have hstable : (prefixWord ++ tailWord_1457495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457495).length < 2 ^ (prefixWord ++ tailWord_1457495).sum := by decide
  have hdescent : baseEnd_1457495 < baseStart_1457495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457501 : List Nat := [1, 4, 5, 1, 1, 1, 2, 6]
def baseStart_1457501 : Nat := 118140960795 + 1457501 * 2 ^ 59
def prefixEnd_1457501 : Nat := 4983230072969 + 3 ^ 40 * 1457501 * 2
def baseEnd_1457501 : Nat := 110873861838341815456975

theorem tailTrace_1457501 : CollatzResearch.WordTrace tailWord_1457501 prefixEnd_1457501 110873861838341815456975 := by
  unfold tailWord_1457501
  simp only [CollatzResearch.WordTrace]
  refine ⟨53159428692730273198268357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35439619128486848798845571 53159428692730273198268357)
  ·
    refine ⟨9967392879886926224675317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53159428692730273198268357 9967392879886926224675317)
    ·
      refine ⟨934443082489399333563311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9967392879886926224675317 934443082489399333563311)
      ·
        refine ⟨1401664623734099000344967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934443082489399333563311 1401664623734099000344967)
        ·
          refine ⟨2102496935601148500517451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401664623734099000344967 2102496935601148500517451)
          ·
            refine ⟨3153745403401722750776177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2102496935601148500517451 3153745403401722750776177)
            ·
              refine ⟨2365309052551292063082133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153745403401722750776177 2365309052551292063082133)
              ·
                refine ⟨110873861838341815456975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2365309052551292063082133 110873861838341815456975)
                ·
                  rfl

theorem cell21_1457501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 6].length) (baseStart_1457501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457501 prefixEnd_1457501 := by exact prefixLift 1457501
  have htrace : WordTrace (prefixWord ++ tailWord_1457501) baseStart_1457501 baseEnd_1457501 := by
    simpa [prefixWord, tailWord_1457501, baseEnd_1457501] using wordTrace_append hprefix tailTrace_1457501
  have hstable : (prefixWord ++ tailWord_1457501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457501).length < 2 ^ (prefixWord ++ tailWord_1457501).sum := by decide
  have hdescent : baseEnd_1457501 < baseStart_1457501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457560 : List Nat := [2, 1, 2, 5, 3, 1, 1, 6]
def baseStart_1457560 : Nat := 118140960795 + 1457560 * 2 ^ 59
def prefixEnd_1457560 : Nat := 4983230072969 + 3 ^ 40 * 1457560 * 2
def baseEnd_1457560 : Nat := 110878350039618151629157

theorem tailTrace_1457560 : CollatzResearch.WordTrace tailWord_1457560 prefixEnd_1457560 110878350039618151629157 := by
  unfold tailWord_1457560
  simp only [CollatzResearch.WordTrace]
  refine ⟨26580790299758263137333067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35441053733011017516444089 26580790299758263137333067)
  ·
    refine ⟨39871185449637394705999601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26580790299758263137333067 39871185449637394705999601)
    ·
      refine ⟨29903389087228046029499701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39871185449637394705999601 29903389087228046029499701)
      ·
        refine ⟨2803442726927629315265597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29903389087228046029499701 2803442726927629315265597)
        ·
          refine ⟨1051291022597860993224599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2803442726927629315265597 1051291022597860993224599)
          ·
            refine ⟨1576936533896791489836899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051291022597860993224599 1576936533896791489836899)
            ·
              refine ⟨2365404800845187234755349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576936533896791489836899 2365404800845187234755349)
              ·
                refine ⟨110878350039618151629157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2365404800845187234755349 110878350039618151629157)
                ·
                  rfl

theorem cell21_1457560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 6].length) (baseStart_1457560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457560 prefixEnd_1457560 := by exact prefixLift 1457560
  have htrace : WordTrace (prefixWord ++ tailWord_1457560) baseStart_1457560 baseEnd_1457560 := by
    simpa [prefixWord, tailWord_1457560, baseEnd_1457560] using wordTrace_append hprefix tailTrace_1457560
  have hstable : (prefixWord ++ tailWord_1457560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457560).length < 2 ^ (prefixWord ++ tailWord_1457560).sum := by decide
  have hdescent : baseEnd_1457560 < baseStart_1457560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457571 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 4]
def baseStart_1457571 : Nat := 118140960795 + 1457571 * 2 ^ 59
def prefixEnd_1457571 : Nat := 4983230072969 + 3 ^ 40 * 1457571 * 2
def baseEnd_1457571 : Nat := 332637560468720880204115

theorem tailTrace_1457571 : CollatzResearch.WordTrace tailWord_1457571 prefixEnd_1457571 332637560468720880204115 := by
  unfold tailWord_1457571
  simp only [CollatzResearch.WordTrace]
  refine ⟨53161981802476675153316567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35441321201651116768877711 53161981802476675153316567)
  ·
    refine ⟨79742972703715012729974851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53161981802476675153316567 79742972703715012729974851)
    ·
      refine ⟨119614459055572519094962277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79742972703715012729974851 119614459055572519094962277)
      ·
        refine ⟨22427711072919847330305427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119614459055572519094962277 22427711072919847330305427)
        ·
          refine ⟨33641566609379770995458141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22427711072919847330305427 33641566609379770995458141)
          ·
            refine ⟨12615587478517414123296803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33641566609379770995458141 12615587478517414123296803)
            ·
              refine ⟨18923381217776121184945205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12615587478517414123296803 18923381217776121184945205)
              ·
                refine ⟨1774066989166511361088613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18923381217776121184945205 1774066989166511361088613)
                ·
                  refine ⟨332637560468720880204115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774066989166511361088613 332637560468720880204115)
                  ·
                    rfl

theorem cell21_1457571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 4].length) (baseStart_1457571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457571 prefixEnd_1457571 := by exact prefixLift 1457571
  have htrace : WordTrace (prefixWord ++ tailWord_1457571) baseStart_1457571 baseEnd_1457571 := by
    simpa [prefixWord, tailWord_1457571, baseEnd_1457571] using wordTrace_append hprefix tailTrace_1457571
  have hstable : (prefixWord ++ tailWord_1457571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457571).length < 2 ^ (prefixWord ++ tailWord_1457571).sum := by decide
  have hdescent : baseEnd_1457571 < baseStart_1457571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457622 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_1457622 : Nat := 118140960795 + 1457622 * 2 ^ 59
def prefixEnd_1457622 : Nat := 4983230072969 + 3 ^ 40 * 1457622 * 2
def baseEnd_1457622 : Nat := 332649199363556124854011

theorem tailTrace_1457622 : CollatzResearch.WordTrace tailWord_1457622 prefixEnd_1457622 332649199363556124854011 := by
  unfold tailWord_1457622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3322740120330744428963945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35442561283527940575615413 3322740120330744428963945)
  ·
    refine ⟨2492055090248058321722959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3322740120330744428963945 2492055090248058321722959)
    ·
      refine ⟨3738082635372087482584439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2492055090248058321722959 3738082635372087482584439)
      ·
        refine ⟨5607123953058131223876659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3738082635372087482584439 5607123953058131223876659)
        ·
          refine ⟨8410685929587196835814989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5607123953058131223876659 8410685929587196835814989)
          ·
            refine ⟨3154007223595198813430621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8410685929587196835814989 3154007223595198813430621)
            ·
              refine ⟨1182752708848199555036483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3154007223595198813430621 1182752708848199555036483)
              ·
                refine ⟨1774129063272299332554725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182752708848199555036483 1774129063272299332554725)
                ·
                  refine ⟨332649199363556124854011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774129063272299332554725 332649199363556124854011)
                  ·
                    rfl

theorem cell21_1457622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_1457622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457622 prefixEnd_1457622 := by exact prefixLift 1457622
  have htrace : WordTrace (prefixWord ++ tailWord_1457622) baseStart_1457622 baseEnd_1457622 := by
    simpa [prefixWord, tailWord_1457622, baseEnd_1457622] using wordTrace_append hprefix tailTrace_1457622
  have hstable : (prefixWord ++ tailWord_1457622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457622).length < 2 ^ (prefixWord ++ tailWord_1457622).sum := by decide
  have hdescent : baseEnd_1457622 < baseStart_1457622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457661 : List Nat := [1, 4, 1, 1, 1, 4, 9]
def baseStart_1457661 : Nat := 118140960795 + 1457661 * 2 ^ 59
def prefixEnd_1457661 : Nat := 4983230072969 + 3 ^ 40 * 1457661 * 2
def baseEnd_1457661 : Nat := 36962011077211191522659

theorem tailTrace_1457661 : CollatzResearch.WordTrace tailWord_1457661 prefixEnd_1457661 36962011077211191522659 := by
  unfold tailWord_1457661
  simp only [CollatzResearch.WordTrace]
  refine ⟨53165264372150620524092837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35443509581433747016061891 53165264372150620524092837)
  ·
    refine ⟨9968487069778241348267407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53165264372150620524092837 9968487069778241348267407)
    ·
      refine ⟨14952730604667362022401111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968487069778241348267407 14952730604667362022401111)
      ·
        refine ⟨22429095907001043033601667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14952730604667362022401111 22429095907001043033601667)
        ·
          refine ⟨33643643860501564550402501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22429095907001043033601667 33643643860501564550402501)
          ·
            refine ⟨6308183223844043353200469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33643643860501564550402501 6308183223844043353200469)
            ·
              refine ⟨36962011077211191522659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6308183223844043353200469 36962011077211191522659)
              ·
                rfl

theorem cell21_1457661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 9].length) (baseStart_1457661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457661 prefixEnd_1457661 := by exact prefixLift 1457661
  have htrace : WordTrace (prefixWord ++ tailWord_1457661) baseStart_1457661 baseEnd_1457661 := by
    simpa [prefixWord, tailWord_1457661, baseEnd_1457661] using wordTrace_append hprefix tailTrace_1457661
  have hstable : (prefixWord ++ tailWord_1457661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457661).length < 2 ^ (prefixWord ++ tailWord_1457661).sum := by decide
  have hdescent : baseEnd_1457661 < baseStart_1457661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457692 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_1457692 : Nat := 118140960795 + 1457692 * 2 ^ 59
def prefixEnd_1457692 : Nat := 4983230072969 + 3 ^ 40 * 1457692 * 2
def baseEnd_1457692 : Nat := 332665174317251558687201

theorem tailTrace_1457692 : CollatzResearch.WordTrace tailWord_1457692 prefixEnd_1457692 332665174317251558687201 := by
  unfold tailWord_1457692
  simp only [CollatzResearch.WordTrace]
  refine ⟨26583197517519156409235665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35444263356692208545647553 26583197517519156409235665)
  ·
    refine ⟨19937398138139367306926749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26583197517519156409235665 19937398138139367306926749)
    ·
      refine ⟨7476524301802262740097531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19937398138139367306926749 7476524301802262740097531)
      ·
        refine ⟨11214786452703394110146297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7476524301802262740097531 11214786452703394110146297)
        ·
          refine ⟨8411089839527545582609723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11214786452703394110146297 8411089839527545582609723)
          ·
            refine ⟨12616634759291318373914585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411089839527545582609723 12616634759291318373914585)
            ·
              refine ⟨9462476069468488780435939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12616634759291318373914585 9462476069468488780435939)
              ·
                refine ⟨14193714104202733170653909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9462476069468488780435939 14193714104202733170653909)
                ·
                  refine ⟨332665174317251558687201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14193714104202733170653909 332665174317251558687201)
                  ·
                    rfl

theorem cell21_1457692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_1457692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457692 prefixEnd_1457692 := by exact prefixLift 1457692
  have htrace : WordTrace (prefixWord ++ tailWord_1457692) baseStart_1457692 baseEnd_1457692 := by
    simpa [prefixWord, tailWord_1457692, baseEnd_1457692] using wordTrace_append hprefix tailTrace_1457692
  have hstable : (prefixWord ++ tailWord_1457692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457692).length < 2 ^ (prefixWord ++ tailWord_1457692).sum := by decide
  have hdescent : baseEnd_1457692 < baseStart_1457692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457774 : List Nat := [4, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_1457774 : Nat := 118140960795 + 1457774 * 2 ^ 59
def prefixEnd_1457774 : Nat := 4983230072969 + 3 ^ 40 * 1457774 * 2
def baseEnd_1457774 : Nat := 332683887834437638320367

theorem tailTrace_1457774 : CollatzResearch.WordTrace tailWord_1457774 prefixEnd_1457774 332683887834437638320367 := by
  unfold tailWord_1457774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646173227592655102869547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35446257213827493881970917 6646173227592655102869547)
  ·
    refine ⟨9969259841388982654304321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6646173227592655102869547 9969259841388982654304321)
    ·
      refine ⟨7476944881041736990728241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9969259841388982654304321 7476944881041736990728241)
      ·
        refine ⟨5607708660781302743046181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7476944881041736990728241 5607708660781302743046181)
        ·
          refine ⟨1051445373896494264321159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5607708660781302743046181 1051445373896494264321159)
          ·
            refine ⟨1577168060844741396481739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051445373896494264321159 1577168060844741396481739)
            ·
              refine ⟨2365752091267112094722609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577168060844741396481739 2365752091267112094722609)
              ·
                refine ⟨1774314068450334071041957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2365752091267112094722609 1774314068450334071041957)
                ·
                  refine ⟨332683887834437638320367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774314068450334071041957 332683887834437638320367)
                  ·
                    rfl

theorem cell21_1457774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_1457774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457774 prefixEnd_1457774 := by exact prefixLift 1457774
  have htrace : WordTrace (prefixWord ++ tailWord_1457774) baseStart_1457774 baseEnd_1457774 := by
    simpa [prefixWord, tailWord_1457774, baseEnd_1457774] using wordTrace_append hprefix tailTrace_1457774
  have hstable : (prefixWord ++ tailWord_1457774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457774).length < 2 ^ (prefixWord ++ tailWord_1457774).sum := by decide
  have hdescent : baseEnd_1457774 < baseStart_1457774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457785 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 3]
def baseStart_1457785 : Nat := 118140960795 + 1457785 * 2 ^ 59
def prefixEnd_1457785 : Nat := 4983230072969 + 3 ^ 40 * 1457785 * 2
def baseEnd_1457785 : Nat := 332686398184304063637011

theorem tailTrace_1457785 : CollatzResearch.WordTrace tailWord_1457785 prefixEnd_1457785 332686398184304063637011 := by
  unfold tailWord_1457785
  simp only [CollatzResearch.WordTrace]
  refine ⟨53169787023701389701606809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35446524682467593134404539 53169787023701389701606809)
  ·
    refine ⟨39877340267776042276205107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53169787023701389701606809 39877340267776042276205107)
    ·
      refine ⟨59816010401664063414307661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39877340267776042276205107 59816010401664063414307661)
      ·
        refine ⟨22431003900624023780365373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59816010401664063414307661 22431003900624023780365373)
        ·
          refine ⟨8411626462734008917637015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22431003900624023780365373 8411626462734008917637015)
          ·
            refine ⟨12617439694101013376455523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8411626462734008917637015 12617439694101013376455523)
            ·
              refine ⟨18926159541151520064683285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12617439694101013376455523 18926159541151520064683285)
              ·
                refine ⟨887163728491477503032029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18926159541151520064683285 887163728491477503032029)
                ·
                  refine ⟨332686398184304063637011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887163728491477503032029 332686398184304063637011)
                  ·
                    rfl

theorem cell21_1457785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 3].length) (baseStart_1457785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457785 prefixEnd_1457785 := by exact prefixLift 1457785
  have htrace : WordTrace (prefixWord ++ tailWord_1457785) baseStart_1457785 baseEnd_1457785 := by
    simpa [prefixWord, tailWord_1457785, baseEnd_1457785] using wordTrace_append hprefix tailTrace_1457785
  have hstable : (prefixWord ++ tailWord_1457785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457785).length < 2 ^ (prefixWord ++ tailWord_1457785).sum := by decide
  have hdescent : baseEnd_1457785 < baseStart_1457785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457889 : List Nat := [1, 2, 3, 1, 5, 9]
def baseStart_1457889 : Nat := 118140960795 + 1457889 * 2 ^ 59
def prefixEnd_1457889 : Nat := 4983230072969 + 3 ^ 40 * 1457889 * 2
def baseEnd_1457889 : Nat := 12322597496341592366795

theorem tailTrace_1457889 : CollatzResearch.WordTrace tailWord_1457889 prefixEnd_1457889 12322597496341592366795 := by
  unfold tailWord_1457889
  simp only [CollatzResearch.WordTrace]
  refine ⟨53173580215324615463392721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35449053476883076975595147 53173580215324615463392721)
  ·
    refine ⟨39880185161493461597544541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53173580215324615463392721 39880185161493461597544541)
    ·
      refine ⟨14955069435560048099079203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39880185161493461597544541 14955069435560048099079203)
      ·
        refine ⟨22432604153340072148618805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14955069435560048099079203 22432604153340072148618805)
        ·
          refine ⟨2103056639375631763933013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22432604153340072148618805 2103056639375631763933013)
          ·
            refine ⟨12322597496341592366795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2103056639375631763933013 12322597496341592366795)
            ·
              rfl

theorem cell21_1457889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 9].length) (baseStart_1457889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457889 prefixEnd_1457889 := by exact prefixLift 1457889
  have htrace : WordTrace (prefixWord ++ tailWord_1457889) baseStart_1457889 baseEnd_1457889 := by
    simpa [prefixWord, tailWord_1457889, baseEnd_1457889] using wordTrace_append hprefix tailTrace_1457889
  have hstable : (prefixWord ++ tailWord_1457889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457889).length < 2 ^ (prefixWord ++ tailWord_1457889).sum := by decide
  have hdescent : baseEnd_1457889 < baseStart_1457889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457895 : List Nat := [1, 1, 5, 4, 1, 1, 1, 4, 3]
def baseStart_1457895 : Nat := 118140960795 + 1457895 * 2 ^ 59
def prefixEnd_1457895 : Nat := 4983230072969 + 3 ^ 40 * 1457895 * 2
def baseEnd_1457895 : Nat := 332711501682968316803453

theorem tailTrace_1457895 : CollatzResearch.WordTrace tailWord_1457895 prefixEnd_1457895 332711501682968316803453 := by
  unfold tailWord_1457895
  simp only [CollatzResearch.WordTrace]
  refine ⟨53173799053302878488111139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35449199368868585658740759 53173799053302878488111139)
  ·
    refine ⟨79760698579954317732166709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53173799053302878488111139 79760698579954317732166709)
    ·
      refine ⟨7477565491870717287390629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79760698579954317732166709 7477565491870717287390629)
      ·
        refine ⟨1402043529725759491385743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7477565491870717287390629 1402043529725759491385743)
        ·
          refine ⟨2103065294588639237078615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402043529725759491385743 2103065294588639237078615)
          ·
            refine ⟨3154597941882958855617923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103065294588639237078615 3154597941882958855617923)
            ·
              refine ⟨4731896912824438283426885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154597941882958855617923 4731896912824438283426885)
              ·
                refine ⟨887230671154582178142541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4731896912824438283426885 887230671154582178142541)
                ·
                  refine ⟨332711501682968316803453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887230671154582178142541 332711501682968316803453)
                  ·
                    rfl

theorem cell21_1457895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 4, 3].length) (baseStart_1457895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457895 prefixEnd_1457895 := by exact prefixLift 1457895
  have htrace : WordTrace (prefixWord ++ tailWord_1457895) baseStart_1457895 baseEnd_1457895 := by
    simpa [prefixWord, tailWord_1457895, baseEnd_1457895] using wordTrace_append hprefix tailTrace_1457895
  have hstable : (prefixWord ++ tailWord_1457895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457895).length < 2 ^ (prefixWord ++ tailWord_1457895).sum := by decide
  have hdescent : baseEnd_1457895 < baseStart_1457895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457940 : List Nat := [2, 4, 4, 1, 1, 1, 8]
def baseStart_1457940 : Nat := 118140960795 + 1457940 * 2 ^ 59
def prefixEnd_1457940 : Nat := 4983230072969 + 3 ^ 40 * 1457940 * 2
def baseEnd_1457940 : Nat := 36969085699562026505929

theorem tailTrace_1457940 : CollatzResearch.WordTrace tailWord_1457940 prefixEnd_1457940 36969085699562026505929 := by
  unfold tailWord_1457940
  simp only [CollatzResearch.WordTrace]
  refine ⟨26587720169069925586749637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35450293558759900782332849 26587720169069925586749637)
  ·
    refine ⟨4985197531700611047515557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26587720169069925586749637 4985197531700611047515557)
    ·
      refine ⟨934724537193864571409167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4985197531700611047515557 934724537193864571409167)
      ·
        refine ⟨1402086805790796857113751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934724537193864571409167 1402086805790796857113751)
        ·
          refine ⟨2103130208686195285670627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402086805790796857113751 2103130208686195285670627)
          ·
            refine ⟨3154695313029292928505941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103130208686195285670627 3154695313029292928505941)
            ·
              refine ⟨36969085699562026505929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3154695313029292928505941 36969085699562026505929)
              ·
                rfl

theorem cell21_1457940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 8].length) (baseStart_1457940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457940 prefixEnd_1457940 := by exact prefixLift 1457940
  have htrace : WordTrace (prefixWord ++ tailWord_1457940) baseStart_1457940 baseEnd_1457940 := by
    simpa [prefixWord, tailWord_1457940, baseEnd_1457940] using wordTrace_append hprefix tailTrace_1457940
  have hstable : (prefixWord ++ tailWord_1457940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457940).length < 2 ^ (prefixWord ++ tailWord_1457940).sum := by decide
  have hdescent : baseEnd_1457940 < baseStart_1457940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457982 : List Nat := [4, 2, 1, 2, 2, 2, 1, 7]
def baseStart_1457982 : Nat := 118140960795 + 1457982 * 2 ^ 59
def prefixEnd_1457982 : Nat := 4983230072969 + 3 ^ 40 * 1457982 * 2
def baseEnd_1457982 : Nat := 110910452089425166284425

theorem tailTrace_1457982 : CollatzResearch.WordTrace tailWord_1457982 prefixEnd_1457982 110910452089425166284425 := by
  unfold tailWord_1457982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647121525498461543316025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35451314802658461564352133 6647121525498461543316025)
  ·
    refine ⟨4985341144123846157487019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6647121525498461543316025 4985341144123846157487019)
    ·
      refine ⟨7478011716185769236230529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4985341144123846157487019 7478011716185769236230529)
      ·
        refine ⟨5608508787139326927172897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7478011716185769236230529 5608508787139326927172897)
        ·
          refine ⟨4206381590354495195379673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5608508787139326927172897 4206381590354495195379673)
          ·
            refine ⟨3154786192765871396534755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4206381590354495195379673 3154786192765871396534755)
            ·
              refine ⟨4732179289148807094802133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154786192765871396534755 4732179289148807094802133)
              ·
                refine ⟨110910452089425166284425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4732179289148807094802133 110910452089425166284425)
                ·
                  rfl

theorem cell21_1457982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_1457982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1457982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1457982 prefixEnd_1457982 := by exact prefixLift 1457982
  have htrace : WordTrace (prefixWord ++ tailWord_1457982) baseStart_1457982 baseEnd_1457982 := by
    simpa [prefixWord, tailWord_1457982, baseEnd_1457982] using wordTrace_append hprefix tailTrace_1457982
  have hstable : (prefixWord ++ tailWord_1457982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457982).length < 2 ^ (prefixWord ++ tailWord_1457982).sum := by decide
  have hdescent : baseEnd_1457982 < baseStart_1457982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458010 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_1458010 : Nat := 118140960795 + 1458010 * 2 ^ 59
def prefixEnd_1458010 : Nat := 4983230072969 + 3 ^ 40 * 1458010 * 2
def baseEnd_1458010 : Nat := 332737746249753672386551

theorem tailTrace_1458010 : CollatzResearch.WordTrace tailWord_1458010 prefixEnd_1458010 332737746249753672386551 := by
  unfold tailWord_1458010
  simp only [CollatzResearch.WordTrace]
  refine ⟨13294498361971563282136871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35451995631924168752364989 13294498361971563282136871)
  ·
    refine ⟨19941747542957344923205307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13294498361971563282136871 19941747542957344923205307)
    ·
      refine ⟨29912621314436017384807961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19941747542957344923205307 29912621314436017384807961)
      ·
        refine ⟨22434465985827013038605971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29912621314436017384807961 22434465985827013038605971)
        ·
          refine ⟨33651698978740519557908957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22434465985827013038605971 33651698978740519557908957)
          ·
            refine ⟨12619387117027694834215859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33651698978740519557908957 12619387117027694834215859)
            ·
              refine ⟨18929080675541542251323789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12619387117027694834215859 18929080675541542251323789)
              ·
                refine ⟨7098405253328078344246421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18929080675541542251323789 7098405253328078344246421)
                ·
                  refine ⟨332737746249753672386551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7098405253328078344246421 332737746249753672386551)
                  ·
                    rfl

theorem cell21_1458010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_1458010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458010 prefixEnd_1458010 := by exact prefixLift 1458010
  have htrace : WordTrace (prefixWord ++ tailWord_1458010) baseStart_1458010 baseEnd_1458010 := by
    simpa [prefixWord, tailWord_1458010, baseEnd_1458010] using wordTrace_append hprefix tailTrace_1458010
  have hstable : (prefixWord ++ tailWord_1458010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458010).length < 2 ^ (prefixWord ++ tailWord_1458010).sum := by decide
  have hdescent : baseEnd_1458010 < baseStart_1458010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458058 : List Nat := [3, 1, 2, 4, 3, 8]
def baseStart_1458058 : Nat := 118140960795 + 1458058 * 2 ^ 59
def prefixEnd_1458058 : Nat := 4983230072969 + 3 ^ 40 * 1458058 * 2
def baseEnd_1458058 : Nat := 12324025944582083540239

theorem tailTrace_1458058 : CollatzResearch.WordTrace tailWord_1458058 prefixEnd_1458058 12324025944582083540239 := by
  unfold tailWord_1458058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13294936037928089331573707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35453162767808238217529885 13294936037928089331573707)
  ·
    refine ⟨19942404056892133997360561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13294936037928089331573707 19942404056892133997360561)
    ·
      refine ⟨14956803042669100498020421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19942404056892133997360561 14956803042669100498020421)
      ·
        refine ⟨2804400570500456343378829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14956803042669100498020421 2804400570500456343378829)
        ·
          refine ⟨1051650213937671128767061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2804400570500456343378829 1051650213937671128767061)
          ·
            refine ⟨12324025944582083540239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1051650213937671128767061 12324025944582083540239)
            ·
              rfl

theorem cell21_1458058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 8].length) (baseStart_1458058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458058 prefixEnd_1458058 := by exact prefixLift 1458058
  have htrace : WordTrace (prefixWord ++ tailWord_1458058) baseStart_1458058 baseEnd_1458058 := by
    simpa [prefixWord, tailWord_1458058, baseEnd_1458058] using wordTrace_append hprefix tailTrace_1458058
  have hstable : (prefixWord ++ tailWord_1458058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458058).length < 2 ^ (prefixWord ++ tailWord_1458058).sum := by decide
  have hdescent : baseEnd_1458058 < baseStart_1458058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458120 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_1458120 : Nat := 118140960795 + 1458120 * 2 ^ 59
def prefixEnd_1458120 : Nat := 4983230072969 + 3 ^ 40 * 1458120 * 2
def baseEnd_1458120 : Nat := 332762849748417925552993

theorem tailTrace_1458120 : CollatzResearch.WordTrace tailWord_1458120 prefixEnd_1458120 332762849748417925552993 := by
  unfold tailWord_1458120
  simp only [CollatzResearch.WordTrace]
  refine ⟨26591002738743870957525907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35454670318325161276701209 26591002738743870957525907)
  ·
    refine ⟨39886504108115806436288861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26591002738743870957525907 39886504108115806436288861)
    ·
      refine ⟨14957439040543427413608323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39886504108115806436288861 14957439040543427413608323)
      ·
        refine ⟨22436158560815141120412485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14957439040543427413608323 22436158560815141120412485)
        ·
          refine ⟨4206779730152838960077341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22436158560815141120412485 4206779730152838960077341)
          ·
            refine ⟨1577542398807314610029003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4206779730152838960077341 1577542398807314610029003)
            ·
              refine ⟨2366313598210971915043505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577542398807314610029003 2366313598210971915043505)
              ·
                refine ⟨1774735198658228936282629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366313598210971915043505 1774735198658228936282629)
                ·
                  refine ⟨332762849748417925552993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1774735198658228936282629 332762849748417925552993)
                  ·
                    rfl

theorem cell21_1458120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_1458120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458120 prefixEnd_1458120 := by exact prefixLift 1458120
  have htrace : WordTrace (prefixWord ++ tailWord_1458120) baseStart_1458120 baseEnd_1458120 := by
    simpa [prefixWord, tailWord_1458120, baseEnd_1458120] using wordTrace_append hprefix tailTrace_1458120
  have hstable : (prefixWord ++ tailWord_1458120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458120).length < 2 ^ (prefixWord ++ tailWord_1458120).sum := by decide
  have hdescent : baseEnd_1458120 < baseStart_1458120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458151 : List Nat := [1, 1, 5, 2, 3, 2, 2, 5]
def baseStart_1458151 : Nat := 118140960795 + 1458151 * 2 ^ 59
def prefixEnd_1458151 : Nat := 4983230072969 + 3 ^ 40 * 1458151 * 2
def baseEnd_1458151 : Nat := 110923308123589586845421

theorem tailTrace_1458151 : CollatzResearch.WordTrace tailWord_1458151 prefixEnd_1458151 110923308123589586845421 := by
  unfold tailWord_1458151
  simp only [CollatzResearch.WordTrace]
  refine ⟨53183136140375434209430307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35455424093583622806286871 53183136140375434209430307)
  ·
    refine ⟨79774704210563151314145461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53183136140375434209430307 79774704210563151314145461)
    ·
      refine ⟨7478878519740295435701137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79774704210563151314145461 7478878519740295435701137)
      ·
        refine ⟨5609158889805221576775853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7478878519740295435701137 5609158889805221576775853)
        ·
          refine ⟨2103434583676958091290945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5609158889805221576775853 2103434583676958091290945)
          ·
            refine ⟨1577575937757718568468209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2103434583676958091290945 1577575937757718568468209)
            ·
              refine ⟨1183181953318288926351157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577575937757718568468209 1183181953318288926351157)
              ·
                refine ⟨110923308123589586845421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1183181953318288926351157 110923308123589586845421)
                ·
                  rfl

theorem cell21_1458151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 2, 5].length) (baseStart_1458151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458151 prefixEnd_1458151 := by exact prefixLift 1458151
  have htrace : WordTrace (prefixWord ++ tailWord_1458151) baseStart_1458151 baseEnd_1458151 := by
    simpa [prefixWord, tailWord_1458151, baseEnd_1458151] using wordTrace_append hprefix tailTrace_1458151
  have hstable : (prefixWord ++ tailWord_1458151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458151).length < 2 ^ (prefixWord ++ tailWord_1458151).sum := by decide
  have hdescent : baseEnd_1458151 < baseStart_1458151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458207 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 7]
def baseStart_1458207 : Nat := 118140960795 + 1458207 * 2 ^ 59
def prefixEnd_1458207 : Nat := 4983230072969 + 3 ^ 40 * 1458207 * 2
def baseEnd_1458207 : Nat := 332782704333725107602815

theorem tailTrace_1458207 : CollatzResearch.WordTrace tailWord_1458207 prefixEnd_1458207 332782704333725107602815 := by
  unfold tailWord_1458207
  simp only [CollatzResearch.WordTrace]
  refine ⟨53185178628172555773468875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35456785752115037182312583 53185178628172555773468875)
  ·
    refine ⟨79777767942258833660203313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53185178628172555773468875 79777767942258833660203313)
    ·
      refine ⟨59833325956694125245152485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79777767942258833660203313 59833325956694125245152485)
      ·
        refine ⟨11218748616880148483466091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59833325956694125245152485 11218748616880148483466091)
        ·
          refine ⟨16828122925320222725199137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11218748616880148483466091 16828122925320222725199137)
          ·
            refine ⟨12621092193990167043899353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16828122925320222725199137 12621092193990167043899353)
            ·
              refine ⟨9465819145492625282924515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12621092193990167043899353 9465819145492625282924515)
              ·
                refine ⟨14198728718238937924386773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9465819145492625282924515 14198728718238937924386773)
                ·
                  refine ⟨332782704333725107602815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14198728718238937924386773 332782704333725107602815)
                  ·
                    rfl

theorem cell21_1458207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 7].length) (baseStart_1458207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458207 prefixEnd_1458207 := by exact prefixLift 1458207
  have htrace : WordTrace (prefixWord ++ tailWord_1458207) baseStart_1458207 baseEnd_1458207 := by
    simpa [prefixWord, tailWord_1458207, baseEnd_1458207] using wordTrace_append hprefix tailTrace_1458207
  have hstable : (prefixWord ++ tailWord_1458207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458207).length < 2 ^ (prefixWord ++ tailWord_1458207).sum := by decide
  have hdescent : baseEnd_1458207 < baseStart_1458207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458300 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_1458300 : Nat := 118140960795 + 1458300 * 2 ^ 59
def prefixEnd_1458300 : Nat := 4983230072969 + 3 ^ 40 * 1458300 * 2
def baseEnd_1458300 : Nat := 332803928200777612552625

theorem tailTrace_1458300 : CollatzResearch.WordTrace tailWord_1458300 prefixEnd_1458300 332803928200777612552625 := by
  unfold tailWord_1458300
  simp only [CollatzResearch.WordTrace]
  refine ⟨26594285308417816328302177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35459047077890421771069569 26594285308417816328302177)
  ·
    refine ⟨19945713981313362246226633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26594285308417816328302177 19945713981313362246226633)
    ·
      refine ⟨14959285485985021684669975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19945713981313362246226633 14959285485985021684669975)
      ·
        refine ⟨22438928228977532527004963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14959285485985021684669975 22438928228977532527004963)
        ·
          refine ⟨33658392343466298790507445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22438928228977532527004963 33658392343466298790507445)
          ·
            refine ⟨3155474282199965511610073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33658392343466298790507445 3155474282199965511610073)
            ·
              refine ⟨2366605711649974133707555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155474282199965511610073 2366605711649974133707555)
              ·
                refine ⟨3549908567474961200561333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2366605711649974133707555 3549908567474961200561333)
                ·
                  refine ⟨332803928200777612552625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3549908567474961200561333 332803928200777612552625)
                  ·
                    rfl

theorem cell21_1458300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_1458300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458300 prefixEnd_1458300 := by exact prefixLift 1458300
  have htrace : WordTrace (prefixWord ++ tailWord_1458300) baseStart_1458300 baseEnd_1458300 := by
    simpa [prefixWord, tailWord_1458300, baseEnd_1458300] using wordTrace_append hprefix tailTrace_1458300
  have hstable : (prefixWord ++ tailWord_1458300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458300).length < 2 ^ (prefixWord ++ tailWord_1458300).sum := by decide
  have hdescent : baseEnd_1458300 < baseStart_1458300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458326 : List Nat := [5, 3, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1458326 : Nat := 118140960795 + 1458326 * 2 ^ 59
def prefixEnd_1458326 : Nat := 4983230072969 + 3 ^ 40 * 1458326 * 2
def baseEnd_1458326 : Nat := 332809861755007345119239

theorem tailTrace_1458326 : CollatzResearch.WordTrace tailWord_1458326 prefixEnd_1458326 332809861755007345119239 := by
  unfold tailWord_1458326
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324344932171339943565677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35459679276494292731367221 3324344932171339943565677)
  ·
    refine ⟨1246629349564252478837129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3324344932171339943565677 1246629349564252478837129)
    ·
      refine ⟨934972012173189359127847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1246629349564252478837129 934972012173189359127847)
      ·
        refine ⟨1402458018259784038691771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934972012173189359127847 1402458018259784038691771)
        ·
          refine ⟨2103687027389676058037657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402458018259784038691771 2103687027389676058037657)
          ·
            refine ⟨1577765270542257043528243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2103687027389676058037657 1577765270542257043528243)
            ·
              refine ⟨2366647905813385565292365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577765270542257043528243 2366647905813385565292365)
              ·
                refine ⟨887492964680019586984637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2366647905813385565292365 887492964680019586984637)
                ·
                  refine ⟨332809861755007345119239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887492964680019586984637 332809861755007345119239)
                  ·
                    rfl

theorem cell21_1458326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1458326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458326 prefixEnd_1458326 := by exact prefixLift 1458326
  have htrace : WordTrace (prefixWord ++ tailWord_1458326) baseStart_1458326 baseEnd_1458326 := by
    simpa [prefixWord, tailWord_1458326, baseEnd_1458326] using wordTrace_append hprefix tailTrace_1458326
  have hstable : (prefixWord ++ tailWord_1458326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458326).length < 2 ^ (prefixWord ++ tailWord_1458326).sum := by decide
  have hdescent : baseEnd_1458326 < baseStart_1458326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458402 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_1458402 : Nat := 118140960795 + 1458402 * 2 ^ 59
def prefixEnd_1458402 : Nat := 4983230072969 + 3 ^ 40 * 1458402 * 2
def baseEnd_1458402 : Nat := 332827205990448101852417

theorem tailTrace_1458402 : CollatzResearch.WordTrace tailWord_1458402 prefixEnd_1458402 332827205990448101852417 := by
  unfold tailWord_1458402
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298072715616526019204365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35461527241644069384544973 13298072715616526019204365)
  ·
    refine ⟨4986777268356197257201637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13298072715616526019204365 4986777268356197257201637)
    ·
      refine ⟨935020737816786985725307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4986777268356197257201637 935020737816786985725307)
      ·
        refine ⟨1402531106725180478587961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935020737816786985725307 1402531106725180478587961)
        ·
          refine ⟨1051898330043885358940971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402531106725180478587961 1051898330043885358940971)
          ·
            refine ⟨1577847495065828038411457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051898330043885358940971 1577847495065828038411457)
            ·
              refine ⟨1183385621299371028808593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1577847495065828038411457 1183385621299371028808593)
              ·
                refine ⟨887539215974528271606445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183385621299371028808593 887539215974528271606445)
                ·
                  refine ⟨332827205990448101852417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887539215974528271606445 332827205990448101852417)
                  ·
                    rfl

theorem cell21_1458402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_1458402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458402 prefixEnd_1458402 := by exact prefixLift 1458402
  have htrace : WordTrace (prefixWord ++ tailWord_1458402) baseStart_1458402 baseEnd_1458402 := by
    simpa [prefixWord, tailWord_1458402, baseEnd_1458402] using wordTrace_append hprefix tailTrace_1458402
  have hstable : (prefixWord ++ tailWord_1458402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458402).length < 2 ^ (prefixWord ++ tailWord_1458402).sum := by decide
  have hdescent : baseEnd_1458402 < baseStart_1458402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458407 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 4]
def baseStart_1458407 : Nat := 118140960795 + 1458407 * 2 ^ 59
def prefixEnd_1458407 : Nat := 4983230072969 + 3 ^ 40 * 1458407 * 2
def baseEnd_1458407 : Nat := 332828347058569204269073

theorem tailTrace_1458407 : CollatzResearch.WordTrace tailWord_1458407 prefixEnd_1458407 332828347058569204269073 := by
  unfold tailWord_1458407
  simp only [CollatzResearch.WordTrace]
  refine ⟨53192473227447989930749475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35461648818298659953832983 53192473227447989930749475)
  ·
    refine ⟨79788709841171984896124213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53192473227447989930749475 79788709841171984896124213)
    ·
      refine ⟨7480191547609873584011645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79788709841171984896124213 7480191547609873584011645)
      ·
        refine ⟨2805071830353702594004367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7480191547609873584011645 2805071830353702594004367)
        ·
          refine ⟨4207607745530553891006551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805071830353702594004367 4207607745530553891006551)
          ·
            refine ⟨6311411618295830836509827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4207607745530553891006551 6311411618295830836509827)
            ·
              refine ⟨9467117427443746254764741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6311411618295830836509827 9467117427443746254764741)
              ·
                refine ⟨1775084517645702422768389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9467117427443746254764741 1775084517645702422768389)
                ·
                  refine ⟨332828347058569204269073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775084517645702422768389 332828347058569204269073)
                  ·
                    rfl

theorem cell21_1458407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 4].length) (baseStart_1458407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458407 prefixEnd_1458407 := by exact prefixLift 1458407
  have htrace : WordTrace (prefixWord ++ tailWord_1458407) baseStart_1458407 baseEnd_1458407 := by
    simpa [prefixWord, tailWord_1458407, baseEnd_1458407] using wordTrace_append hprefix tailTrace_1458407
  have hstable : (prefixWord ++ tailWord_1458407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458407).length < 2 ^ (prefixWord ++ tailWord_1458407).sum := by decide
  have hdescent : baseEnd_1458407 < baseStart_1458407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458435 : List Nat := [1, 1, 1, 3, 2, 3, 3, 2, 5]
def baseStart_1458435 : Nat := 118140960795 + 1458435 * 2 ^ 59
def prefixEnd_1458435 : Nat := 4983230072969 + 3 ^ 40 * 1458435 * 2
def baseEnd_1458435 : Nat := 332834737040047377802349

theorem tailTrace_1458435 : CollatzResearch.WordTrace tailWord_1458435 prefixEnd_1458435 332834737040047377802349 := by
  unfold tailWord_1458435
  simp only [CollatzResearch.WordTrace]
  refine ⟨53193494471346550712768759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35462329647564367141845839 53193494471346550712768759)
  ·
    refine ⟨79790241707019826069153139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53193494471346550712768759 79790241707019826069153139)
    ·
      refine ⟨119685362560529739103729709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79790241707019826069153139 119685362560529739103729709)
      ·
        refine ⟨44882010960198652163898641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119685362560529739103729709 44882010960198652163898641)
        ·
          refine ⟨33661508220148989122923981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44882010960198652163898641 33661508220148989122923981)
          ·
            refine ⟨12623065582555870921096493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33661508220148989122923981 12623065582555870921096493)
            ·
              refine ⟨4733649593458451595411185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12623065582555870921096493 4733649593458451595411185)
              ·
                refine ⟨3550237195093838696558389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733649593458451595411185 3550237195093838696558389)
                ·
                  refine ⟨332834737040047377802349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550237195093838696558389 332834737040047377802349)
                  ·
                    rfl

theorem cell21_1458435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 2, 5].length) (baseStart_1458435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458435 prefixEnd_1458435 := by exact prefixLift 1458435
  have htrace : WordTrace (prefixWord ++ tailWord_1458435) baseStart_1458435 baseEnd_1458435 := by
    simpa [prefixWord, tailWord_1458435, baseEnd_1458435] using wordTrace_append hprefix tailTrace_1458435
  have hstable : (prefixWord ++ tailWord_1458435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458435).length < 2 ^ (prefixWord ++ tailWord_1458435).sum := by decide
  have hdescent : baseEnd_1458435 < baseStart_1458435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458483 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 4]
def baseStart_1458483 : Nat := 118140960795 + 1458483 * 2 ^ 59
def prefixEnd_1458483 : Nat := 4983230072969 + 3 ^ 40 * 1458483 * 2
def baseEnd_1458483 : Nat := 332845691294009961002251

theorem tailTrace_1458483 : CollatzResearch.WordTrace tailWord_1458483 prefixEnd_1458483 332845691294009961002251 := by
  unfold tailWord_1458483
  simp only [CollatzResearch.WordTrace]
  refine ⟨53195245175172654910516103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35463496783448436607010735 53195245175172654910516103)
  ·
    refine ⟨79792867762758982365774155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53195245175172654910516103 79792867762758982365774155)
    ·
      refine ⟨119689301644138473548661233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79792867762758982365774155 119689301644138473548661233)
      ·
        refine ⟨89766976233103855161495925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119689301644138473548661233 89766976233103855161495925)
        ·
          refine ⟨8415654021853486421390243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 89766976233103855161495925 8415654021853486421390243)
          ·
            refine ⟨12623481032780229632085365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8415654021853486421390243 12623481032780229632085365)
            ·
              refine ⟨1183451346823146528008003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12623481032780229632085365 1183451346823146528008003)
              ·
                refine ⟨1775177020234719792012005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183451346823146528008003 1775177020234719792012005)
                ·
                  refine ⟨332845691294009961002251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775177020234719792012005 332845691294009961002251)
                  ·
                    rfl

theorem cell21_1458483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 4].length) (baseStart_1458483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458483 prefixEnd_1458483 := by exact prefixLift 1458483
  have htrace : WordTrace (prefixWord ++ tailWord_1458483) baseStart_1458483 baseEnd_1458483 := by
    simpa [prefixWord, tailWord_1458483, baseEnd_1458483] using wordTrace_append hprefix tailTrace_1458483
  have hstable : (prefixWord ++ tailWord_1458483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458483).length < 2 ^ (prefixWord ++ tailWord_1458483).sum := by decide
  have hdescent : baseEnd_1458483 < baseStart_1458483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458590 : List Nat := [4, 3, 1, 2, 1, 1, 3, 6]
def baseStart_1458590 : Nat := 118140960795 + 1458590 * 2 ^ 59
def prefixEnd_1458590 : Nat := 4983230072969 + 3 ^ 40 * 1458590 * 2
def baseEnd_1458590 : Nat := 110956703383933850906233

theorem tailTrace_1458590 : CollatzResearch.WordTrace tailWord_1458590 prefixEnd_1458590 110956703383933850906233 := by
  unfold tailWord_1458590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6649893473223126523082653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35466098523856674789774149 6649893473223126523082653)
  ·
    refine ⟨2493710052458672446155995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6649893473223126523082653 2493710052458672446155995)
    ·
      refine ⟨3740565078688008669233993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2493710052458672446155995 3740565078688008669233993)
      ·
        refine ⟨2805423809016006501925495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3740565078688008669233993 2805423809016006501925495)
        ·
          refine ⟨4208135713524009752888243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805423809016006501925495 4208135713524009752888243)
          ·
            refine ⟨6312203570286014629332365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208135713524009752888243 6312203570286014629332365)
            ·
              refine ⟨2367076338857255485999637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6312203570286014629332365 2367076338857255485999637)
              ·
                refine ⟨110956703383933850906233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2367076338857255485999637 110956703383933850906233)
                ·
                  rfl

theorem cell21_1458590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 6].length) (baseStart_1458590 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458590 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458590 prefixEnd_1458590 := by exact prefixLift 1458590
  have htrace : WordTrace (prefixWord ++ tailWord_1458590) baseStart_1458590 baseEnd_1458590 := by
    simpa [prefixWord, tailWord_1458590, baseEnd_1458590] using wordTrace_append hprefix tailTrace_1458590
  have hstable : (prefixWord ++ tailWord_1458590).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458590).length < 2 ^ (prefixWord ++ tailWord_1458590).sum := by decide
  have hdescent : baseEnd_1458590 < baseStart_1458590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458621 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 3]
def baseStart_1458621 : Nat := 118140960795 + 1458621 * 2 ^ 59
def prefixEnd_1458621 : Nat := 4983230072969 + 3 ^ 40 * 1458621 * 2
def baseEnd_1458621 : Nat := 332877184774152387701969

theorem tailTrace_1458621 : CollatzResearch.WordTrace tailWord_1458621 prefixEnd_1458621 332877184774152387701969 := by
  unfold tailWord_1458621
  simp only [CollatzResearch.WordTrace]
  refine ⟨53200278448672704479039717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35466852299115136319359811 53200278448672704479039717)
  ·
    refine ⟨9975052209126132089819947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53200278448672704479039717 9975052209126132089819947)
    ·
      refine ⟨14962578313689198134729921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975052209126132089819947 14962578313689198134729921)
      ·
        refine ⟨11221933735266898601047441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14962578313689198134729921 11221933735266898601047441)
        ·
          refine ⟨8416450301450173950785581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11221933735266898601047441 8416450301450173950785581)
          ·
            refine ⟨3156168863043815231544593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8416450301450173950785581 3156168863043815231544593)
            ·
              refine ⟨2367126647282861423658445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3156168863043815231544593 2367126647282861423658445)
              ·
                refine ⟨887672492731073033871917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2367126647282861423658445 887672492731073033871917)
                ·
                  refine ⟨332877184774152387701969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887672492731073033871917 332877184774152387701969)
                  ·
                    rfl

theorem cell21_1458621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_1458621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458621 prefixEnd_1458621 := by exact prefixLift 1458621
  have htrace : WordTrace (prefixWord ++ tailWord_1458621) baseStart_1458621 baseEnd_1458621 := by
    simpa [prefixWord, tailWord_1458621, baseEnd_1458621] using wordTrace_append hprefix tailTrace_1458621
  have hstable : (prefixWord ++ tailWord_1458621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458621).length < 2 ^ (prefixWord ++ tailWord_1458621).sum := by decide
  have hdescent : baseEnd_1458621 < baseStart_1458621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458632 : List Nat := [2, 1, 3, 1, 3, 3, 8]
def baseStart_1458632 : Nat := 118140960795 + 1458632 * 2 ^ 59
def prefixEnd_1458632 : Nat := 4983230072969 + 3 ^ 40 * 1458632 * 2
def baseEnd_1458632 : Nat := 36986632791557645890957

theorem tailTrace_1458632 : CollatzResearch.WordTrace tailWord_1458632 prefixEnd_1458632 36986632791557645890957 := by
  unfold tailWord_1458632
  simp only [CollatzResearch.WordTrace]
  refine ⟨26600339825816426678845075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35467119767755235571793433 26600339825816426678845075)
  ·
    refine ⟨39900509738724640018267613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26600339825816426678845075 39900509738724640018267613)
    ·
      refine ⟨14962691152021740006850355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39900509738724640018267613 14962691152021740006850355)
      ·
        refine ⟨22444036728032610010275533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14962691152021740006850355 22444036728032610010275533)
        ·
          refine ⟨8416513773012228753853325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22444036728032610010275533 8416513773012228753853325)
          ·
            refine ⟨3156192664879585782694997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8416513773012228753853325 3156192664879585782694997)
            ·
              refine ⟨36986632791557645890957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3156192664879585782694997 36986632791557645890957)
              ·
                rfl

theorem cell21_1458632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 8].length) (baseStart_1458632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458632 prefixEnd_1458632 := by exact prefixLift 1458632
  have htrace : WordTrace (prefixWord ++ tailWord_1458632) baseStart_1458632 baseEnd_1458632 := by
    simpa [prefixWord, tailWord_1458632, baseEnd_1458632] using wordTrace_append hprefix tailTrace_1458632
  have hstable : (prefixWord ++ tailWord_1458632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458632).length < 2 ^ (prefixWord ++ tailWord_1458632).sum := by decide
  have hdescent : baseEnd_1458632 < baseStart_1458632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458663 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 5]
def baseStart_1458663 : Nat := 118140960795 + 1458663 * 2 ^ 59
def prefixEnd_1458663 : Nat := 4983230072969 + 3 ^ 40 * 1458663 * 2
def baseEnd_1458663 : Nat := 332886769746369648001883

theorem tailTrace_1458663 : CollatzResearch.WordTrace tailWord_1458663 prefixEnd_1458663 332886769746369648001883 := by
  unfold tailWord_1458663
  simp only [CollatzResearch.WordTrace]
  refine ⟨53201810314520545652068643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35467873543013697101379095 53201810314520545652068643)
  ·
    refine ⟨79802715471780818478102965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53201810314520545652068643 79802715471780818478102965)
    ·
      refine ⟨7481504575479451732322153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79802715471780818478102965 7481504575479451732322153)
      ·
        refine ⟨5611128431609588799241615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7481504575479451732322153 5611128431609588799241615)
        ·
          refine ⟨8416692647414383198862423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611128431609588799241615 8416692647414383198862423)
          ·
            refine ⟨12625038971121574798293635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416692647414383198862423 12625038971121574798293635)
            ·
              refine ⟨18937558456682362197440453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12625038971121574798293635 18937558456682362197440453)
              ·
                refine ⟨3550792210627942912020085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18937558456682362197440453 3550792210627942912020085)
                ·
                  refine ⟨332886769746369648001883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3550792210627942912020085 332886769746369648001883)
                  ·
                    rfl

theorem cell21_1458663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 5].length) (baseStart_1458663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458663 prefixEnd_1458663 := by exact prefixLift 1458663
  have htrace : WordTrace (prefixWord ++ tailWord_1458663) baseStart_1458663 baseEnd_1458663 := by
    simpa [prefixWord, tailWord_1458663, baseEnd_1458663] using wordTrace_append hprefix tailTrace_1458663
  have hstable : (prefixWord ++ tailWord_1458663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458663).length < 2 ^ (prefixWord ++ tailWord_1458663).sum := by decide
  have hdescent : baseEnd_1458663 < baseStart_1458663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458666 : List Nat := [3, 1, 3, 1, 3, 3, 2, 5]
def baseStart_1458666 : Nat := 118140960795 + 1458666 * 2 ^ 59
def prefixEnd_1458666 : Nat := 4983230072969 + 3 ^ 40 * 1458666 * 2
def baseEnd_1458666 : Nat := 110962484795747436483959

theorem tailTrace_1458666 : CollatzResearch.WordTrace tailWord_1458666 prefixEnd_1458666 110962484795747436483959 := by
  unfold tailWord_1458666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13300479933377419291106963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35467946489006451442951901 13300479933377419291106963)
  ·
    refine ⟨19950719900066128936660445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13300479933377419291106963 19950719900066128936660445)
    ·
      refine ⟨7481519962524798351247667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19950719900066128936660445 7481519962524798351247667)
      ·
        refine ⟨11222279943787197526871501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7481519962524798351247667 11222279943787197526871501)
        ·
          refine ⟨4208354978920199072576813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11222279943787197526871501 4208354978920199072576813)
          ·
            refine ⟨1578133117095074652216305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4208354978920199072576813 1578133117095074652216305)
            ·
              refine ⟨1183599837821305989162229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1578133117095074652216305 1183599837821305989162229)
              ·
                refine ⟨110962484795747436483959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1183599837821305989162229 110962484795747436483959)
                ·
                  rfl

theorem cell21_1458666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_1458666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458666 prefixEnd_1458666 := by exact prefixLift 1458666
  have htrace : WordTrace (prefixWord ++ tailWord_1458666) baseStart_1458666 baseEnd_1458666 := by
    simpa [prefixWord, tailWord_1458666, baseEnd_1458666] using wordTrace_append hprefix tailTrace_1458666
  have hstable : (prefixWord ++ tailWord_1458666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458666).length < 2 ^ (prefixWord ++ tailWord_1458666).sum := by decide
  have hdescent : baseEnd_1458666 < baseStart_1458666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458770 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1458770 : Nat := 118140960795 + 1458770 * 2 ^ 59
def prefixEnd_1458770 : Nat := 4983230072969 + 3 ^ 40 * 1458770 * 2
def baseEnd_1458770 : Nat := 332911188604161239718331

theorem tailTrace_1458770 : CollatzResearch.WordTrace tailWord_1458770 prefixEnd_1458770 332911188604161239718331 := by
  unfold tailWord_1458770
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301428231283225731553441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35470475283421935284142509 13301428231283225731553441)
  ·
    refine ⟨9976071173462419298665081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13301428231283225731553441 9976071173462419298665081)
    ·
      refine ⟨7482053380096814473998811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9976071173462419298665081 7482053380096814473998811)
      ·
        refine ⟨11223080070145221710998217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7482053380096814473998811 11223080070145221710998217)
        ·
          refine ⟨8417310052608916283248663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11223080070145221710998217 8417310052608916283248663)
          ·
            refine ⟨12625965078913374424872995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8417310052608916283248663 12625965078913374424872995)
            ·
              refine ⟨18938947618370061637309493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12625965078913374424872995 18938947618370061637309493)
              ·
                refine ⟨1775526339222193278497765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18938947618370061637309493 1775526339222193278497765)
                ·
                  refine ⟨332911188604161239718331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775526339222193278497765 332911188604161239718331)
                  ·
                    rfl

theorem cell21_1458770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1458770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458770 prefixEnd_1458770 := by exact prefixLift 1458770
  have htrace : WordTrace (prefixWord ++ tailWord_1458770) baseStart_1458770 baseEnd_1458770 := by
    simpa [prefixWord, tailWord_1458770, baseEnd_1458770] using wordTrace_append hprefix tailTrace_1458770
  have hstable : (prefixWord ++ tailWord_1458770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458770).length < 2 ^ (prefixWord ++ tailWord_1458770).sum := by decide
  have hdescent : baseEnd_1458770 < baseStart_1458770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458846 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_1458846 : Nat := 118140960795 + 1458846 * 2 ^ 59
def prefixEnd_1458846 : Nat := 4983230072969 + 3 ^ 40 * 1458846 * 2
def baseEnd_1458846 : Nat := 332928532839601996451509

theorem tailTrace_1458846 : CollatzResearch.WordTrace tailWord_1458846 prefixEnd_1458846 332928532839601996451509 := by
  unfold tailWord_1458846
  simp only [CollatzResearch.WordTrace]
  refine ⟨6651060609107195988247549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35472323248571711937320261 6651060609107195988247549)
  ·
    refine ⟨2494147728415198495592831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6651060609107195988247549 2494147728415198495592831)
    ·
      refine ⟨3741221592622797743389247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2494147728415198495592831 3741221592622797743389247)
      ·
        refine ⟨5611832388934196615083871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741221592622797743389247 5611832388934196615083871)
        ·
          refine ⟨8417748583401294922625807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5611832388934196615083871 8417748583401294922625807)
          ·
            refine ⟨12626622875101942383938711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8417748583401294922625807 12626622875101942383938711)
            ·
              refine ⟨18939934312652913575908067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12626622875101942383938711 18939934312652913575908067)
              ·
                refine ⟨28409901468979370363862101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18939934312652913575908067 28409901468979370363862101)
                ·
                  refine ⟨332928532839601996451509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28409901468979370363862101 332928532839601996451509)
                  ·
                    rfl

theorem cell21_1458846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_1458846 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458846 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458846 prefixEnd_1458846 := by exact prefixLift 1458846
  have htrace : WordTrace (prefixWord ++ tailWord_1458846) baseStart_1458846 baseEnd_1458846 := by
    simpa [prefixWord, tailWord_1458846, baseEnd_1458846] using wordTrace_append hprefix tailTrace_1458846
  have hstable : (prefixWord ++ tailWord_1458846).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458846).length < 2 ^ (prefixWord ++ tailWord_1458846).sum := by decide
  have hdescent : baseEnd_1458846 < baseStart_1458846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458919 : List Nat := [1, 1, 5, 14]
def baseStart_1458919 : Nat := 118140960795 + 1458919 * 2 ^ 59
def prefixEnd_1458919 : Nat := 4983230072969 + 3 ^ 40 * 1458919 * 2
def baseEnd_1458919 : Nat := 1370144824831975686151

theorem tailTrace_1458919 : CollatzResearch.WordTrace tailWord_1458919 prefixEnd_1458919 1370144824831975686151 := by
  unfold tailWord_1458919
  simp only [CollatzResearch.WordTrace]
  refine ⟨53211147401593101373387811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35474098267728734248925207 53211147401593101373387811)
  ·
    refine ⟨79816721102389652060081717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53211147401593101373387811 79816721102389652060081717)
    ·
      refine ⟨7482817603349029880632661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79816721102389652060081717 7482817603349029880632661)
      ·
        refine ⟨1370144824831975686151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 7482817603349029880632661 1370144824831975686151)
        ·
          rfl

theorem cell21_1458919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 14].length) (baseStart_1458919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458919 prefixEnd_1458919 := by exact prefixLift 1458919
  have htrace : WordTrace (prefixWord ++ tailWord_1458919) baseStart_1458919 baseEnd_1458919 := by
    simpa [prefixWord, tailWord_1458919, baseEnd_1458919] using wordTrace_append hprefix tailTrace_1458919
  have hstable : (prefixWord ++ tailWord_1458919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458919).length < 2 ^ (prefixWord ++ tailWord_1458919).sum := by decide
  have hdescent : baseEnd_1458919 < baseStart_1458919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458973 : List Nat := [1, 4, 2, 4, 2, 1, 1, 2, 4]
def baseStart_1458973 : Nat := 118140960795 + 1458973 * 2 ^ 59
def prefixEnd_1458973 : Nat := 4983230072969 + 3 ^ 40 * 1458973 * 2
def baseEnd_1458973 : Nat := 332957515969877997834583

theorem tailTrace_1458973 : CollatzResearch.WordTrace tailWord_1458973 prefixEnd_1458973 332957515969877997834583 := by
  unfold tailWord_1458973
  simp only [CollatzResearch.WordTrace]
  refine ⟨53213116943397468595853573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35475411295598312397235715 53213116943397468595853573)
  ·
    refine ⟨9977459426887025361722545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53213116943397468595853573 9977459426887025361722545)
    ·
      refine ⟨7483094570165269021291909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9977459426887025361722545 7483094570165269021291909)
      ·
        refine ⟨1403080231905987941492233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7483094570165269021291909 1403080231905987941492233)
        ·
          refine ⟨1052310173929490956119175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1403080231905987941492233 1052310173929490956119175)
          ·
            refine ⟨1578465260894236434178763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052310173929490956119175 1578465260894236434178763)
            ·
              refine ⟨2367697891341354651268145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578465260894236434178763 2367697891341354651268145)
              ·
                refine ⟨1775773418506015988451109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367697891341354651268145 1775773418506015988451109)
                ·
                  refine ⟨332957515969877997834583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775773418506015988451109 332957515969877997834583)
                  ·
                    rfl

theorem cell21_1458973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 4].length) (baseStart_1458973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458973 prefixEnd_1458973 := by exact prefixLift 1458973
  have htrace : WordTrace (prefixWord ++ tailWord_1458973) baseStart_1458973 baseEnd_1458973 := by
    simpa [prefixWord, tailWord_1458973, baseEnd_1458973] using wordTrace_append hprefix tailTrace_1458973
  have hstable : (prefixWord ++ tailWord_1458973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458973).length < 2 ^ (prefixWord ++ tailWord_1458973).sum := by decide
  have hdescent : baseEnd_1458973 < baseStart_1458973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458981 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 6]
def baseStart_1458981 : Nat := 118140960795 + 1458981 * 2 ^ 59
def prefixEnd_1458981 : Nat := 4983230072969 + 3 ^ 40 * 1458981 * 2
def baseEnd_1458981 : Nat := 332959341678871761701233

theorem tailTrace_1458981 : CollatzResearch.WordTrace tailWord_1458981 prefixEnd_1458981 332959341678871761701233 := by
  unfold tailWord_1458981
  simp only [CollatzResearch.WordTrace]
  refine ⟨53213408727368485962144797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35475605818245657308096531 53213408727368485962144797)
  ·
    refine ⟨19955028272763182235804299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53213408727368485962144797 19955028272763182235804299)
    ·
      refine ⟨29932542409144773353706449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19955028272763182235804299 29932542409144773353706449)
      ·
        refine ⟨22449406806858580015279837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29932542409144773353706449 22449406806858580015279837)
        ·
          refine ⟨8418527552571967505729939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22449406806858580015279837 8418527552571967505729939)
          ·
            refine ⟨12627791328857951258594909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418527552571967505729939 12627791328857951258594909)
            ·
              refine ⟨4735421748321731721973091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12627791328857951258594909 4735421748321731721973091)
              ·
                refine ⟨7103132622482597582959637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4735421748321731721973091 7103132622482597582959637)
                ·
                  refine ⟨332959341678871761701233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7103132622482597582959637 332959341678871761701233)
                  ·
                    rfl

theorem cell21_1458981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_1458981 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458981 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458981 prefixEnd_1458981 := by exact prefixLift 1458981
  have htrace : WordTrace (prefixWord ++ tailWord_1458981) baseStart_1458981 baseEnd_1458981 := by
    simpa [prefixWord, tailWord_1458981, baseEnd_1458981] using wordTrace_append hprefix tailTrace_1458981
  have hstable : (prefixWord ++ tailWord_1458981).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458981).length < 2 ^ (prefixWord ++ tailWord_1458981).sum := by decide
  have hdescent : baseEnd_1458981 < baseStart_1458981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458984 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 3]
def baseStart_1458984 : Nat := 118140960795 + 1458984 * 2 ^ 59
def prefixEnd_1458984 : Nat := 4983230072969 + 3 ^ 40 * 1458984 * 2
def baseEnd_1458984 : Nat := 332960026319744423151227

theorem tailTrace_1458984 : CollatzResearch.WordTrace tailWord_1458984 prefixEnd_1458984 332960026319744423151227 := by
  unfold tailWord_1458984
  simp only [CollatzResearch.WordTrace]
  refine ⟨26606759073178808737252003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35475678764238411649669337 26606759073178808737252003)
  ·
    refine ⟨39910138609768213105878005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26606759073178808737252003 39910138609768213105878005)
    ·
      refine ⟨3741575494665769978676063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39910138609768213105878005 3741575494665769978676063)
      ·
        refine ⟨5612363241998654968014095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741575494665769978676063 5612363241998654968014095)
        ·
          refine ⟨8418544862997982452021143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5612363241998654968014095 8418544862997982452021143)
          ·
            refine ⟨12627817294496973678031715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8418544862997982452021143 12627817294496973678031715)
            ·
              refine ⟨18941725941745460517047573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12627817294496973678031715 18941725941745460517047573)
              ·
                refine ⟨887893403519318461736605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18941725941745460517047573 887893403519318461736605)
                ·
                  refine ⟨332960026319744423151227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887893403519318461736605 332960026319744423151227)
                  ·
                    rfl

theorem cell21_1458984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 3].length) (baseStart_1458984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1458984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1458984 prefixEnd_1458984 := by exact prefixLift 1458984
  have htrace : WordTrace (prefixWord ++ tailWord_1458984) baseStart_1458984 baseEnd_1458984 := by
    simpa [prefixWord, tailWord_1458984, baseEnd_1458984] using wordTrace_append hprefix tailTrace_1458984
  have hstable : (prefixWord ++ tailWord_1458984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458984).length < 2 ^ (prefixWord ++ tailWord_1458984).sum := by decide
  have hdescent : baseEnd_1458984 < baseStart_1458984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459043 : List Nat := [1, 1, 1, 5, 3, 1, 3, 1, 5]
def baseStart_1459043 : Nat := 118140960795 + 1459043 * 2 ^ 59
def prefixEnd_1459043 : Nat := 4983230072969 + 3 ^ 40 * 1459043 * 2
def baseEnd_1459043 : Nat := 332973490923573431667773

theorem tailTrace_1459043 : CollatzResearch.WordTrace tailWord_1459043 prefixEnd_1459043 332973490923573431667773 := by
  unfold tailWord_1459043
  simp only [CollatzResearch.WordTrace]
  refine ⟨53215670053143870550901783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35477113368762580367267855 53215670053143870550901783)
  ·
    refine ⟨79823505079715805826352675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53215670053143870550901783 79823505079715805826352675)
    ·
      refine ⟨119735257619573708739529013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79823505079715805826352675 119735257619573708739529013)
      ·
        refine ⟨11225180401835035194330845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119735257619573708739529013 11225180401835035194330845)
        ·
          refine ⟨4209442650688138197874067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11225180401835035194330845 4209442650688138197874067)
          ·
            refine ⟨6314163976032207296811101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209442650688138197874067 6314163976032207296811101)
            ·
              refine ⟨2367811491012077736304163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6314163976032207296811101 2367811491012077736304163)
              ·
                refine ⟨3551717236518116604456245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367811491012077736304163 3551717236518116604456245)
                ·
                  refine ⟨332973490923573431667773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3551717236518116604456245 332973490923573431667773)
                  ·
                    rfl

theorem cell21_1459043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 3, 1, 5].length) (baseStart_1459043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459043 prefixEnd_1459043 := by exact prefixLift 1459043
  have htrace : WordTrace (prefixWord ++ tailWord_1459043) baseStart_1459043 baseEnd_1459043 := by
    simpa [prefixWord, tailWord_1459043, baseEnd_1459043] using wordTrace_append hprefix tailTrace_1459043
  have hstable : (prefixWord ++ tailWord_1459043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459043).length < 2 ^ (prefixWord ++ tailWord_1459043).sum := by decide
  have hdescent : baseEnd_1459043 < baseStart_1459043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459071 : List Nat := [1, 1, 2, 2, 1, 1, 6, 7]
def baseStart_1459071 : Nat := 118140960795 + 1459071 * 2 ^ 59
def prefixEnd_1459071 : Nat := 4983230072969 + 3 ^ 40 * 1459071 * 2
def baseEnd_1459071 : Nat := 110993293635017201733683

theorem tailTrace_1459071 : CollatzResearch.WordTrace tailWord_1459071 prefixEnd_1459071 110993293635017201733683 := by
  unfold tailWord_1459071
  simp only [CollatzResearch.WordTrace]
  refine ⟨53216691297042431332921067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35477794198028287555280711 53216691297042431332921067)
  ·
    refine ⟨79825036945563646999381601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53216691297042431332921067 79825036945563646999381601)
    ·
      refine ⟨59868777709172735249536201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79825036945563646999381601 59868777709172735249536201)
      ·
        refine ⟨44901583281879551437152151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59868777709172735249536201 44901583281879551437152151)
        ·
          refine ⟨67352374922819327155728227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44901583281879551437152151 67352374922819327155728227)
          ·
            refine ⟨101028562384228990733592341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67352374922819327155728227 101028562384228990733592341)
            ·
              refine ⟨4735713861760733940637141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101028562384228990733592341 4735713861760733940637141)
              ·
                refine ⟨110993293635017201733683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4735713861760733940637141 110993293635017201733683)
                ·
                  rfl

theorem cell21_1459071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 7].length) (baseStart_1459071 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459071 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459071 prefixEnd_1459071 := by exact prefixLift 1459071
  have htrace : WordTrace (prefixWord ++ tailWord_1459071) baseStart_1459071 baseEnd_1459071 := by
    simpa [prefixWord, tailWord_1459071, baseEnd_1459071] using wordTrace_append hprefix tailTrace_1459071
  have hstable : (prefixWord ++ tailWord_1459071).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459071).length < 2 ^ (prefixWord ++ tailWord_1459071).sum := by decide
  have hdescent : baseEnd_1459071 < baseStart_1459071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459105 : List Nat := [1, 2, 3, 4, 1, 3, 1, 6]
def baseStart_1459105 : Nat := 118140960795 + 1459105 * 2 ^ 59
def prefixEnd_1459105 : Nat := 4983230072969 + 3 ^ 40 * 1459105 * 2
def baseEnd_1459105 : Nat := 110995880056091700544771

theorem tailTrace_1459105 : CollatzResearch.WordTrace tailWord_1459105 prefixEnd_1459105 110995880056091700544771 := by
  unfold tailWord_1459105
  simp only [CollatzResearch.WordTrace]
  refine ⟨53217931378919255139658769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35478620919279503426439179 53217931378919255139658769)
  ·
    refine ⟨39913448534189441354744077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53217931378919255139658769 39913448534189441354744077)
    ·
      refine ⟨14967543200321040508029029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39913448534189441354744077 14967543200321040508029029)
      ·
        refine ⟨2806414350060195095255443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14967543200321040508029029 2806414350060195095255443)
        ·
          refine ⟨4209621525090292642883165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2806414350060195095255443 4209621525090292642883165)
          ·
            refine ⟨1578608071908859741081187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4209621525090292642883165 1578608071908859741081187)
            ·
              refine ⟨2367912107863289611621781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578608071908859741081187 2367912107863289611621781)
              ·
                refine ⟨110995880056091700544771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2367912107863289611621781 110995880056091700544771)
                ·
                  rfl

theorem cell21_1459105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 6].length) (baseStart_1459105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459105 prefixEnd_1459105 := by exact prefixLift 1459105
  have htrace : WordTrace (prefixWord ++ tailWord_1459105) baseStart_1459105 baseEnd_1459105 := by
    simpa [prefixWord, tailWord_1459105, baseEnd_1459105] using wordTrace_append hprefix tailTrace_1459105
  have hstable : (prefixWord ++ tailWord_1459105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459105).length < 2 ^ (prefixWord ++ tailWord_1459105).sum := by decide
  have hdescent : baseEnd_1459105 < baseStart_1459105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459136 : List Nat := [2, 1, 1, 2, 3, 4, 2, 3, 3]
def baseStart_1459136 : Nat := 118140960795 + 1459136 * 2 ^ 59
def prefixEnd_1459136 : Nat := 4983230072969 + 3 ^ 40 * 1459136 * 2
def baseEnd_1459136 : Nat := 332994714790625936617583

theorem tailTrace_1459136 : CollatzResearch.WordTrace tailWord_1459136 prefixEnd_1459136 332994714790625936617583 := by
  unfold tailWord_1459136
  simp only [CollatzResearch.WordTrace]
  refine ⟨26609531020903473717018631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35479374694537964956024841 26609531020903473717018631)
  ·
    refine ⟨39914296531355210575527947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26609531020903473717018631 39914296531355210575527947)
    ·
      refine ⟨59871444797032815863291921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39914296531355210575527947 59871444797032815863291921)
      ·
        refine ⟨44903583597774611897468941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59871444797032815863291921 44903583597774611897468941)
        ·
          refine ⟨16838843849165479461550853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44903583597774611897468941 16838843849165479461550853)
          ·
            refine ⟨3157283221718527399040785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16838843849165479461550853 3157283221718527399040785)
            ·
              refine ⟨2367962416288895549280589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157283221718527399040785 2367962416288895549280589)
              ·
                refine ⟨887985906108335830980221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2367962416288895549280589 887985906108335830980221)
                ·
                  refine ⟨332994714790625936617583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887985906108335830980221 332994714790625936617583)
                  ·
                    rfl

theorem cell21_1459136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 3, 3].length) (baseStart_1459136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459136 prefixEnd_1459136 := by exact prefixLift 1459136
  have htrace : WordTrace (prefixWord ++ tailWord_1459136) baseStart_1459136 baseEnd_1459136 := by
    simpa [prefixWord, tailWord_1459136, baseEnd_1459136] using wordTrace_append hprefix tailTrace_1459136
  have hstable : (prefixWord ++ tailWord_1459136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459136).length < 2 ^ (prefixWord ++ tailWord_1459136).sum := by decide
  have hdescent : baseEnd_1459136 < baseStart_1459136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459147 : List Nat := [1, 1, 1, 1, 3, 6, 8]
def baseStart_1459147 : Nat := 118140960795 + 1459147 * 2 ^ 59
def prefixEnd_1459147 : Nat := 4983230072969 + 3 ^ 40 * 1459147 * 2
def baseEnd_1459147 : Nat := 36999691682276929103803

theorem tailTrace_1459147 : CollatzResearch.WordTrace tailWord_1459147 prefixEnd_1459147 36999691682276929103803 := by
  unfold tailWord_1459147
  simp only [CollatzResearch.WordTrace]
  refine ⟨53219463244767096312687695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35479642163178064208458463 53219463244767096312687695)
  ·
    refine ⟨79829194867150644469031543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53219463244767096312687695 79829194867150644469031543)
    ·
      refine ⟨119743792300725966703547315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79829194867150644469031543 119743792300725966703547315)
      ·
        refine ⟨179615688451088950055320973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119743792300725966703547315 179615688451088950055320973)
        ·
          refine ⟨67355883169158356270745365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179615688451088950055320973 67355883169158356270745365)
          ·
            refine ⟨3157307023554297950191189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67355883169158356270745365 3157307023554297950191189)
            ·
              refine ⟨36999691682276929103803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3157307023554297950191189 36999691682276929103803)
              ·
                rfl

theorem cell21_1459147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 8].length) (baseStart_1459147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459147 prefixEnd_1459147 := by exact prefixLift 1459147
  have htrace : WordTrace (prefixWord ++ tailWord_1459147) baseStart_1459147 baseEnd_1459147 := by
    simpa [prefixWord, tailWord_1459147, baseEnd_1459147] using wordTrace_append hprefix tailTrace_1459147
  have hstable : (prefixWord ++ tailWord_1459147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459147).length < 2 ^ (prefixWord ++ tailWord_1459147).sum := by decide
  have hdescent : baseEnd_1459147 < baseStart_1459147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459150 : List Nat := [4, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_1459150 : Nat := 118140960795 + 1459150 * 2 ^ 59
def prefixEnd_1459150 : Nat := 4983230072969 + 3 ^ 40 * 1459150 * 2
def baseEnd_1459150 : Nat := 332997909781365023384221

theorem tailTrace_1459150 : CollatzResearch.WordTrace tailWord_1459150 prefixEnd_1459150 332997909781365023384221 := by
  unfold tailWord_1459150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652446582969528478130863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35479715109170818550031269 6652446582969528478130863)
  ·
    refine ⟨9978669874454292717196295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6652446582969528478130863 9978669874454292717196295)
    ·
      refine ⟨14968004811681439075794443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9978669874454292717196295 14968004811681439075794443)
      ·
        refine ⟨22452007217522158613691665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14968004811681439075794443 22452007217522158613691665)
        ·
          refine ⟨16839005413141618960268749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22452007217522158613691665 16839005413141618960268749)
          ·
            refine ⟨6314627029928107110100781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16839005413141618960268749 6314627029928107110100781)
            ·
              refine ⟨2367985136223040166287793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6314627029928107110100781 2367985136223040166287793)
              ·
                refine ⟨1775988852167280124715845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367985136223040166287793 1775988852167280124715845)
                ·
                  refine ⟨332997909781365023384221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1775988852167280124715845 332997909781365023384221)
                  ·
                    rfl

theorem cell21_1459150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_1459150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459150 prefixEnd_1459150 := by exact prefixLift 1459150
  have htrace : WordTrace (prefixWord ++ tailWord_1459150) baseStart_1459150 baseEnd_1459150 := by
    simpa [prefixWord, tailWord_1459150, baseEnd_1459150] using wordTrace_append hprefix tailTrace_1459150
  have hstable : (prefixWord ++ tailWord_1459150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459150).length < 2 ^ (prefixWord ++ tailWord_1459150).sum := by decide
  have hdescent : baseEnd_1459150 < baseStart_1459150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459167 : List Nat := [1, 1, 2, 3, 5, 1, 3, 1, 4]
def baseStart_1459167 : Nat := 118140960795 + 1459167 * 2 ^ 59
def prefixEnd_1459167 : Nat := 4983230072969 + 3 ^ 40 * 1459167 * 2
def baseEnd_1459167 : Nat := 333001789412976771600853

theorem tailTrace_1459167 : CollatzResearch.WordTrace tailWord_1459167 prefixEnd_1459167 333001789412976771600853 := by
  unfold tailWord_1459167
  simp only [CollatzResearch.WordTrace]
  refine ⟨53220192704694639728415755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35480128469796426485610503 53220192704694639728415755)
  ·
    refine ⟨79830289057041959592623633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53220192704694639728415755 79830289057041959592623633)
    ·
      refine ⟨59872716792781469694467725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79830289057041959592623633 59872716792781469694467725)
      ·
        refine ⟨22452268797293051135425397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59872716792781469694467725 22452268797293051135425397)
        ·
          refine ⟨2104900199746223543946131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22452268797293051135425397 2104900199746223543946131)
          ·
            refine ⟨3157350299619335315919197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104900199746223543946131 3157350299619335315919197)
            ·
              refine ⟨1184006362357250743469699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3157350299619335315919197 1184006362357250743469699)
              ·
                refine ⟨1776009543535876115204549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184006362357250743469699 1776009543535876115204549)
                ·
                  refine ⟨333001789412976771600853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776009543535876115204549 333001789412976771600853)
                  ·
                    rfl

theorem cell21_1459167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 1, 4].length) (baseStart_1459167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459167 prefixEnd_1459167 := by exact prefixLift 1459167
  have htrace : WordTrace (prefixWord ++ tailWord_1459167) baseStart_1459167 baseEnd_1459167 := by
    simpa [prefixWord, tailWord_1459167, baseEnd_1459167] using wordTrace_append hprefix tailTrace_1459167
  have hstable : (prefixWord ++ tailWord_1459167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459167).length < 2 ^ (prefixWord ++ tailWord_1459167).sum := by decide
  have hdescent : baseEnd_1459167 < baseStart_1459167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459198 : List Nat := [4, 2, 2, 2, 3, 1, 7]
def baseStart_1459198 : Nat := 118140960795 + 1459198 * 2 ^ 59
def prefixEnd_1459198 : Nat := 4983230072969 + 3 ^ 40 * 1459198 * 2
def baseEnd_1459198 : Nat := 37000984892814178509347

theorem tailTrace_1459198 : CollatzResearch.WordTrace tailWord_1459198 prefixEnd_1459198 37000984892814178509347 := by
  unfold tailWord_1459198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652665420947791502849281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35480882245054888015196165 6652665420947791502849281)
  ·
    refine ⟨4989499065710843627136961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6652665420947791502849281 4989499065710843627136961)
    ·
      refine ⟨3742124299283132720352721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4989499065710843627136961 3742124299283132720352721)
      ·
        refine ⟨2806593224462349540264541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3742124299283132720352721 2806593224462349540264541)
        ·
          refine ⟨1052472459173381077599203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2806593224462349540264541 1052472459173381077599203)
          ·
            refine ⟨1578708688760071616398805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052472459173381077599203 1578708688760071616398805)
            ·
              refine ⟨37000984892814178509347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1578708688760071616398805 37000984892814178509347)
              ·
                rfl

theorem cell21_1459198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 7].length) (baseStart_1459198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459198 prefixEnd_1459198 := by exact prefixLift 1459198
  have htrace : WordTrace (prefixWord ++ tailWord_1459198) baseStart_1459198 baseEnd_1459198 := by
    simpa [prefixWord, tailWord_1459198, baseEnd_1459198] using wordTrace_append hprefix tailTrace_1459198
  have hstable : (prefixWord ++ tailWord_1459198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459198).length < 2 ^ (prefixWord ++ tailWord_1459198).sum := by decide
  have hdescent : baseEnd_1459198 < baseStart_1459198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459218 : List Nat := [3, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_1459218 : Nat := 118140960795 + 1459218 * 2 ^ 59
def prefixEnd_1459218 : Nat := 4983230072969 + 3 ^ 40 * 1459218 * 2
def baseEnd_1459218 : Nat := 333013428307812016250749

theorem tailTrace_1459218 : CollatzResearch.WordTrace tailWord_1459218 prefixEnd_1459218 333013428307812016250749 := by
  unfold tailWord_1459218
  simp only [CollatzResearch.WordTrace]
  refine ⟨13305513206877468859630577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35481368551673250292348205 13305513206877468859630577)
  ·
    refine ⟨9979134905158101644722933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13305513206877468859630577 9979134905158101644722933)
    ·
      refine ⟨935543897358572029192775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9979134905158101644722933 935543897358572029192775)
      ·
        refine ⟨1403315846037858043789163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935543897358572029192775 1403315846037858043789163)
        ·
          refine ⟨2104973769056787065683745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403315846037858043789163 2104973769056787065683745)
          ·
            refine ⟨1578730326792590299262809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2104973769056787065683745 1578730326792590299262809)
            ·
              refine ⟨1184047745094442724447107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1578730326792590299262809 1184047745094442724447107)
              ·
                refine ⟨1776071617641664086670661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184047745094442724447107 1776071617641664086670661)
                ·
                  refine ⟨333013428307812016250749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776071617641664086670661 333013428307812016250749)
                  ·
                    rfl

theorem cell21_1459218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_1459218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459218 prefixEnd_1459218 := by exact prefixLift 1459218
  have htrace : WordTrace (prefixWord ++ tailWord_1459218) baseStart_1459218 baseEnd_1459218 := by
    simpa [prefixWord, tailWord_1459218, baseEnd_1459218] using wordTrace_append hprefix tailTrace_1459218
  have hstable : (prefixWord ++ tailWord_1459218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459218).length < 2 ^ (prefixWord ++ tailWord_1459218).sum := by decide
  have hdescent : baseEnd_1459218 < baseStart_1459218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459285 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 4]
def baseStart_1459285 : Nat := 118140960795 + 1459285 * 2 ^ 59
def prefixEnd_1459285 : Nat := 4983230072969 + 3 ^ 40 * 1459285 * 2
def baseEnd_1459285 : Nat := 333028718620634788633945

theorem tailTrace_1459285 : CollatzResearch.WordTrace tailWord_1459285 prefixEnd_1459285 333028718620634788633945 := by
  unfold tailWord_1459285
  simp only [CollatzResearch.WordTrace]
  refine ⟨53224496518267145881211309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35482997678844763920807539 53224496518267145881211309)
  ·
    refine ⟨19959186194350179705454241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53224496518267145881211309 19959186194350179705454241)
    ·
      refine ⟨14969389645762634779090681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19959186194350179705454241 14969389645762634779090681)
      ·
        refine ⟨11227042234321976084318011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14969389645762634779090681 11227042234321976084318011)
        ·
          refine ⟨16840563351482964126477017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11227042234321976084318011 16840563351482964126477017)
          ·
            refine ⟨12630422513612223094857763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16840563351482964126477017 12630422513612223094857763)
            ·
              refine ⟨18945633770418334642286645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12630422513612223094857763 18945633770418334642286645)
              ·
                refine ⟨1776153165976718872714373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18945633770418334642286645 1776153165976718872714373)
                ·
                  refine ⟨333028718620634788633945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776153165976718872714373 333028718620634788633945)
                  ·
                    rfl

theorem cell21_1459285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_1459285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459285 prefixEnd_1459285 := by exact prefixLift 1459285
  have htrace : WordTrace (prefixWord ++ tailWord_1459285) baseStart_1459285 baseEnd_1459285 := by
    simpa [prefixWord, tailWord_1459285, baseEnd_1459285] using wordTrace_append hprefix tailTrace_1459285
  have hstable : (prefixWord ++ tailWord_1459285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459285).length < 2 ^ (prefixWord ++ tailWord_1459285).sum := by decide
  have hdescent : baseEnd_1459285 < baseStart_1459285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459364 : List Nat := [2, 3, 1, 2, 3, 1, 3, 3, 3]
def baseStart_1459364 : Nat := 118140960795 + 1459364 * 2 ^ 59
def prefixEnd_1459364 : Nat := 4983230072969 + 3 ^ 40 * 1459364 * 2
def baseEnd_1459364 : Nat := 333046747496948206817117

theorem tailTrace_1459364 : CollatzResearch.WordTrace tailWord_1459364 prefixEnd_1459364 333046747496948206817117 := by
  unfold tailWord_1459364
  simp only [CollatzResearch.WordTrace]
  refine ⟨26613688942490471186668573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35484918589987294915558097 26613688942490471186668573)
  ·
    refine ⟨9980133353433926695000715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26613688942490471186668573 9980133353433926695000715)
    ·
      refine ⟨14970200030150890042501073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980133353433926695000715 14970200030150890042501073)
      ·
        refine ⟨11227650022613167531875805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14970200030150890042501073 11227650022613167531875805)
        ·
          refine ⟨4210368758479937824453427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11227650022613167531875805 4210368758479937824453427)
          ·
            refine ⟨6315553137719906736680141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210368758479937824453427 6315553137719906736680141)
            ·
              refine ⟨2368332426644965026255053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6315553137719906736680141 2368332426644965026255053)
              ·
                refine ⟨888124659991861884845645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2368332426644965026255053 888124659991861884845645)
                ·
                  refine ⟨333046747496948206817117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888124659991861884845645 333046747496948206817117)
                  ·
                    rfl

theorem cell21_1459364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_1459364 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459364 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459364 prefixEnd_1459364 := by exact prefixLift 1459364
  have htrace : WordTrace (prefixWord ++ tailWord_1459364) baseStart_1459364 baseEnd_1459364 := by
    simpa [prefixWord, tailWord_1459364, baseEnd_1459364] using wordTrace_append hprefix tailTrace_1459364
  have hstable : (prefixWord ++ tailWord_1459364).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459364).length < 2 ^ (prefixWord ++ tailWord_1459364).sum := by decide
  have hdescent : baseEnd_1459364 < baseStart_1459364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459392 : List Nat := [2, 1, 1, 2, 6, 1, 2, 6]
def baseStart_1459392 : Nat := 118140960795 + 1459392 * 2 ^ 59
def prefixEnd_1459392 : Nat := 4983230072969 + 3 ^ 40 * 1459392 * 2
def baseEnd_1459392 : Nat := 111017712492808793450131

theorem tailTrace_1459392 : CollatzResearch.WordTrace tailWord_1459392 prefixEnd_1459392 111017712492808793450131 := by
  unfold tailWord_1459392
  simp only [CollatzResearch.WordTrace]
  refine ⟨26614199564439751577678215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35485599419253002103570953 26614199564439751577678215)
  ·
    refine ⟨39921299346659627366517323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26614199564439751577678215 39921299346659627366517323)
    ·
      refine ⟨59881949019989441049775985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39921299346659627366517323 59881949019989441049775985)
      ·
        refine ⟨44911461764992080787331989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59881949019989441049775985 44911461764992080787331989)
        ·
          refine ⟨2105224770234003786906187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44911461764992080787331989 2105224770234003786906187)
          ·
            refine ⟨3157837155351005680359281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105224770234003786906187 3157837155351005680359281)
            ·
              refine ⟨2368377866513254260269461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157837155351005680359281 2368377866513254260269461)
              ·
                refine ⟨111017712492808793450131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2368377866513254260269461 111017712492808793450131)
                ·
                  rfl

theorem cell21_1459392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_1459392 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459392 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459392 prefixEnd_1459392 := by exact prefixLift 1459392
  have htrace : WordTrace (prefixWord ++ tailWord_1459392) baseStart_1459392 baseEnd_1459392 := by
    simpa [prefixWord, tailWord_1459392, baseEnd_1459392] using wordTrace_append hprefix tailTrace_1459392
  have hstable : (prefixWord ++ tailWord_1459392).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459392).length < 2 ^ (prefixWord ++ tailWord_1459392).sum := by decide
  have hdescent : baseEnd_1459392 < baseStart_1459392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459454 : List Nat := [4, 2, 2, 1, 1, 2, 2, 3, 4]
def baseStart_1459454 : Nat := 118140960795 + 1459454 * 2 ^ 59
def prefixEnd_1459454 : Nat := 4983230072969 + 3 ^ 40 * 1459454 * 2
def baseEnd_1459454 : Nat := 333067286723128050316933

theorem tailTrace_1459454 : CollatzResearch.WordTrace tailWord_1459454 prefixEnd_1459454 333067286723128050316933 := by
  unfold tailWord_1459454
  simp only [CollatzResearch.WordTrace]
  refine ⟨6653832556831860968014177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35487106969769925162742277 6653832556831860968014177)
  ·
    refine ⟨4990374417623895726010633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6653832556831860968014177 4990374417623895726010633)
    ·
      refine ⟨3742780813217921794507975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4990374417623895726010633 3742780813217921794507975)
      ·
        refine ⟨5614171219826882691761963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3742780813217921794507975 5614171219826882691761963)
        ·
          refine ⟨8421256829740324037642945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5614171219826882691761963 8421256829740324037642945)
          ·
            refine ⟨6315942622305243028232209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8421256829740324037642945 6315942622305243028232209)
            ·
              refine ⟨4736956966728932271174157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315942622305243028232209 4736956966728932271174157)
              ·
                refine ⟨1776358862523349601690309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4736956966728932271174157 1776358862523349601690309)
                ·
                  refine ⟨333067286723128050316933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1776358862523349601690309 333067286723128050316933)
                  ·
                    rfl

theorem cell21_1459454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_1459454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459454 prefixEnd_1459454 := by exact prefixLift 1459454
  have htrace : WordTrace (prefixWord ++ tailWord_1459454) baseStart_1459454 baseEnd_1459454 := by
    simpa [prefixWord, tailWord_1459454, baseEnd_1459454] using wordTrace_append hprefix tailTrace_1459454
  have hstable : (prefixWord ++ tailWord_1459454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459454).length < 2 ^ (prefixWord ++ tailWord_1459454).sum := by decide
  have hdescent : baseEnd_1459454 < baseStart_1459454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459468 : List Nat := [2, 2, 1, 2, 2, 4, 3, 5]
def baseStart_1459468 : Nat := 118140960795 + 1459468 * 2 ^ 59
def prefixEnd_1459468 : Nat := 4983230072969 + 3 ^ 40 * 1459468 * 2
def baseEnd_1459468 : Nat := 111023493904622379027857

theorem tailTrace_1459468 : CollatzResearch.WordTrace tailWord_1459468 prefixEnd_1459468 111023493904622379027857 := by
  unfold tailWord_1459468
  simp only [CollatzResearch.WordTrace]
  refine ⟨26615585538302084067561529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35487447384402778756748705 26615585538302084067561529)
  ·
    refine ⟨19961689153726563050671147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26615585538302084067561529 19961689153726563050671147)
    ·
      refine ⟨29942533730589844576006721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19961689153726563050671147 29942533730589844576006721)
      ·
        refine ⟨22456900297942383432005041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29942533730589844576006721 22456900297942383432005041)
        ·
          refine ⟨16842675223456787574003781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22456900297942383432005041 16842675223456787574003781)
          ·
            refine ⟨3158001604398147670125709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16842675223456787574003781 3158001604398147670125709)
            ·
              refine ⟨1184250601649305376297141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3158001604398147670125709 1184250601649305376297141)
              ·
                refine ⟨111023493904622379027857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1184250601649305376297141 111023493904622379027857)
                ·
                  rfl

theorem cell21_1459468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_1459468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459468 prefixEnd_1459468 := by exact prefixLift 1459468
  have htrace : WordTrace (prefixWord ++ tailWord_1459468) baseStart_1459468 baseEnd_1459468 := by
    simpa [prefixWord, tailWord_1459468, baseEnd_1459468] using wordTrace_append hprefix tailTrace_1459468
  have hstable : (prefixWord ++ tailWord_1459468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459468).length < 2 ^ (prefixWord ++ tailWord_1459468).sum := by decide
  have hdescent : baseEnd_1459468 < baseStart_1459468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459474 : List Nat := [3, 2, 4, 2, 1, 1, 2, 3, 3]
def baseStart_1459474 : Nat := 118140960795 + 1459474 * 2 ^ 59
def prefixEnd_1459474 : Nat := 4983230072969 + 3 ^ 40 * 1459474 * 2
def baseEnd_1459474 : Nat := 333071850995612459983559

theorem tailTrace_1459474 : CollatzResearch.WordTrace tailWord_1459474 prefixEnd_1459474 333071850995612459983559 := by
  unfold tailWord_1459474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307847478645607789960369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35487593276388287439894317 13307847478645607789960369)
  ·
    refine ⟨9980885608984205842470277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13307847478645607789960369 9980885608984205842470277)
    ·
      refine ⟨1871416051684538595463177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9980885608984205842470277 1871416051684538595463177)
      ·
        refine ⟨1403562038763403946597383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1871416051684538595463177 1403562038763403946597383)
        ·
          refine ⟨2105343058145105919896075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403562038763403946597383 2105343058145105919896075)
          ·
            refine ⟨3158014587217658879844113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105343058145105919896075 3158014587217658879844113)
            ·
              refine ⟨2368510940413244159883085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3158014587217658879844113 2368510940413244159883085)
              ·
                refine ⟨888191602654966559956157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2368510940413244159883085 888191602654966559956157)
                ·
                  refine ⟨333071850995612459983559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 888191602654966559956157 333071850995612459983559)
                  ·
                    rfl

theorem cell21_1459474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_1459474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1459474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1459474 prefixEnd_1459474 := by exact prefixLift 1459474
  have htrace : WordTrace (prefixWord ++ tailWord_1459474) baseStart_1459474 baseEnd_1459474 := by
    simpa [prefixWord, tailWord_1459474, baseEnd_1459474] using wordTrace_append hprefix tailTrace_1459474
  have hstable : (prefixWord ++ tailWord_1459474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459474).length < 2 ^ (prefixWord ++ tailWord_1459474).sum := by decide
  have hdescent : baseEnd_1459474 < baseStart_1459474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
