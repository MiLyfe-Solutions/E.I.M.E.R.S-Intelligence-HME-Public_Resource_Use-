import V185TrunkScan23Chunk0538

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3186591 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 1, 5]
def baseStart_3186591 : Nat := 118140960795 + 3186591 * 2 ^ 59
def prefixEnd_3186591 : Nat := 4983230072969 + 3 ^ 40 * 3186591 * 2
def baseEnd_3186591 : Nat := 545417610763815727252547

theorem tailTrace_3186591 : CollatzResearch.WordTrace tailWord_3186591 prefixEnd_3186591 545417610763815727252547 := by
  unfold tailWord_3186591
  simp only [CollatzResearch.WordTrace]
  refine ⟨116224521998532508259831627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77483014665688338839887751 116224521998532508259831627)
  ·
    refine ⟨174336782997798762389747441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116224521998532508259831627 174336782997798762389747441)
    ·
      refine ⟨130752587248349071792310581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174336782997798762389747441 130752587248349071792310581)
      ·
        refine ⟨12258055054532725480529117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130752587248349071792310581 12258055054532725480529117)
        ·
          refine ⟨4596770645449772055198419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12258055054532725480529117 4596770645449772055198419)
          ·
            refine ⟨6895155968174658082797629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4596770645449772055198419 6895155968174658082797629)
            ·
              refine ⟨2585683488065496781049111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6895155968174658082797629 2585683488065496781049111)
              ·
                refine ⟨3878525232098245171573667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2585683488065496781049111 3878525232098245171573667)
                ·
                  refine ⟨5817787848147367757360501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3878525232098245171573667 5817787848147367757360501)
                  ·
                    refine ⟨545417610763815727252547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5817787848147367757360501 545417610763815727252547)
                    ·
                      rfl

theorem cell23_3186591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 1, 5].length) (baseStart_3186591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186591 prefixEnd_3186591 := by exact prefixLift 3186591
  have htrace : WordTrace (prefixWord ++ tailWord_3186591) baseStart_3186591 baseEnd_3186591 := by
    simpa [prefixWord, tailWord_3186591, baseEnd_3186591] using wordTrace_append hprefix tailTrace_3186591
  have hstable : (prefixWord ++ tailWord_3186591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186591).length < 2 ^ (prefixWord ++ tailWord_3186591).sum := by decide
  have hdescent : baseEnd_3186591 < baseStart_3186591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186644 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3186644 : Nat := 118140960795 + 3186644 * 2 ^ 59
def prefixEnd_3186644 : Nat := 4983230072969 + 3 ^ 40 * 3186644 * 2
def baseEnd_3186644 : Nat := 1636280046766135474394897

theorem tailTrace_3186644 : CollatzResearch.WordTrace tailWord_3186644 prefixEnd_3186644 1636280046766135474394897 := by
  unfold tailWord_3186644
  simp only [CollatzResearch.WordTrace]
  refine ⟨58113227533670249155755493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77484303378226998874340657 58113227533670249155755493)
  ·
    refine ⟨10896230162563171716704155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58113227533670249155755493 10896230162563171716704155)
    ·
      refine ⟨16344345243844757575056233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896230162563171716704155 16344345243844757575056233)
      ·
        refine ⟨12258258932883568181292175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16344345243844757575056233 12258258932883568181292175)
        ·
          refine ⟨18387388399325352271938263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12258258932883568181292175 18387388399325352271938263)
          ·
            refine ⟨27581082598988028407907395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18387388399325352271938263 27581082598988028407907395)
            ·
              refine ⟨41371623898482042611861093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27581082598988028407907395 41371623898482042611861093)
              ·
                refine ⟨7757179480965382989723955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41371623898482042611861093 7757179480965382989723955)
                ·
                  refine ⟨11635769221448074484585933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757179480965382989723955 11635769221448074484585933)
                  ·
                    refine ⟨4363413458043027931719725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11635769221448074484585933 4363413458043027931719725)
                    ·
                      refine ⟨1636280046766135474394897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4363413458043027931719725 1636280046766135474394897)
                      ·
                        rfl

theorem cell23_3186644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3186644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186644 prefixEnd_3186644 := by exact prefixLift 3186644
  have htrace : WordTrace (prefixWord ++ tailWord_3186644) baseStart_3186644 baseEnd_3186644 := by
    simpa [prefixWord, tailWord_3186644, baseEnd_3186644] using wordTrace_append hprefix tailTrace_3186644
  have hstable : (prefixWord ++ tailWord_3186644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186644).length < 2 ^ (prefixWord ++ tailWord_3186644).sum := by decide
  have hdescent : baseEnd_3186644 < baseStart_3186644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186645 : List Nat := [1, 3, 2, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_3186645 : Nat := 118140960795 + 3186645 * 2 ^ 59
def prefixEnd_3186645 : Nat := 4983230072969 + 3 ^ 40 * 3186645 * 2
def baseEnd_3186645 : Nat := 1636280560246789970482393

theorem tailTrace_3186645 : CollatzResearch.WordTrace tailWord_3186645 prefixEnd_3186645 1636280560246789970482393 := by
  unfold tailWord_3186645
  simp only [CollatzResearch.WordTrace]
  refine ⟨116226491540336875482297389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77484327693557916988198259 116226491540336875482297389)
  ·
    refine ⟨43584934327626328305861521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116226491540336875482297389 43584934327626328305861521)
    ·
      refine ⟨32688700745719746229396141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43584934327626328305861521 32688700745719746229396141)
      ·
        refine ⟨12258262779644904836023553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32688700745719746229396141 12258262779644904836023553)
        ·
          refine ⟨9193697084733678627017665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12258262779644904836023553 9193697084733678627017665)
          ·
            refine ⟨6895272813550258970263249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9193697084733678627017665 6895272813550258970263249)
            ·
              refine ⟨5171454610162694227697437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6895272813550258970263249 5171454610162694227697437)
              ·
                refine ⟨1939295478811010335386539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5171454610162694227697437 1939295478811010335386539)
                ·
                  refine ⟨2908943218216515503079809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939295478811010335386539 2908943218216515503079809)
                  ·
                    refine ⟨2181707413662386627309857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2908943218216515503079809 2181707413662386627309857)
                    ·
                      refine ⟨1636280560246789970482393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181707413662386627309857 1636280560246789970482393)
                      ·
                        rfl

theorem cell23_3186645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_3186645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186645 prefixEnd_3186645 := by exact prefixLift 3186645
  have htrace : WordTrace (prefixWord ++ tailWord_3186645) baseStart_3186645 baseEnd_3186645 := by
    simpa [prefixWord, tailWord_3186645, baseEnd_3186645] using wordTrace_append hprefix tailTrace_3186645
  have hstable : (prefixWord ++ tailWord_3186645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186645).length < 2 ^ (prefixWord ++ tailWord_3186645).sum := by decide
  have hdescent : baseEnd_3186645 < baseStart_3186645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186678 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3186678 : Nat := 118140960795 + 3186678 * 2 ^ 59
def prefixEnd_3186678 : Nat := 4983230072969 + 3 ^ 40 * 3186678 * 2
def baseEnd_3186678 : Nat := 1636297505108388341369741

theorem tailTrace_3186678 : CollatzResearch.WordTrace tailWord_3186678 prefixEnd_3186678 1636297505108388341369741 := by
  unfold tailWord_3186678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264230946826082632390543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77485130099478214745499125 7264230946826082632390543)
  ·
    refine ⟨10896346420239123948585815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264230946826082632390543 10896346420239123948585815)
    ·
      refine ⟨16344519630358685922878723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10896346420239123948585815 16344519630358685922878723)
      ·
        refine ⟨24516779445538028884318085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16344519630358685922878723 24516779445538028884318085)
        ·
          refine ⟨4596896146038380415809641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24516779445538028884318085 4596896146038380415809641)
          ·
            refine ⟨3447672109528785311857231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4596896146038380415809641 3447672109528785311857231)
            ·
              refine ⟨5171508164293177967785847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447672109528785311857231 5171508164293177967785847)
              ·
                refine ⟨7757262246439766951678771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171508164293177967785847 7757262246439766951678771)
                ·
                  refine ⟨11635893369659650427518157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757262246439766951678771 11635893369659650427518157)
                  ·
                    refine ⟨4363460013622368910319309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11635893369659650427518157 4363460013622368910319309)
                    ·
                      refine ⟨1636297505108388341369741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4363460013622368910319309 1636297505108388341369741)
                      ·
                        rfl

theorem cell23_3186678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3186678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186678 prefixEnd_3186678 := by exact prefixLift 3186678
  have htrace : WordTrace (prefixWord ++ tailWord_3186678) baseStart_3186678 baseEnd_3186678 := by
    simpa [prefixWord, tailWord_3186678, baseEnd_3186678] using wordTrace_append hprefix tailTrace_3186678
  have hstable : (prefixWord ++ tailWord_3186678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186678).length < 2 ^ (prefixWord ++ tailWord_3186678).sum := by decide
  have hdescent : baseEnd_3186678 < baseStart_3186678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186687 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 3]
def baseStart_3186687 : Nat := 118140960795 + 3186687 * 2 ^ 59
def prefixEnd_3186687 : Nat := 4983230072969 + 3 ^ 40 * 3186687 * 2
def baseEnd_3186687 : Nat := 1636302126434278806157199

theorem tailTrace_3186687 : CollatzResearch.WordTrace tailWord_3186687 prefixEnd_3186687 1636302126434278806157199 := by
  unfold tailWord_3186687
  simp only [CollatzResearch.WordTrace]
  refine ⟨116228023406184716655326315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77485348937456477770217543 116228023406184716655326315)
  ·
    refine ⟨174342035109277074982989473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116228023406184716655326315 174342035109277074982989473)
    ·
      refine ⟨130756526331957806237242105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174342035109277074982989473 130756526331957806237242105)
      ·
        refine ⟨98067394748968354677931579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130756526331957806237242105 98067394748968354677931579)
        ·
          refine ⟨147101092123452532016897369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98067394748968354677931579 147101092123452532016897369)
          ·
            refine ⟨110325819092589399012673027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147101092123452532016897369 110325819092589399012673027)
            ·
              refine ⟨165488728638884098519009541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110325819092589399012673027 165488728638884098519009541)
              ·
                refine ⟨31029136619790768472314289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165488728638884098519009541 31029136619790768472314289)
                ·
                  refine ⟨23271852464843076354235717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31029136619790768472314289 23271852464843076354235717)
                  ·
                    refine ⟨4363472337158076816419197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23271852464843076354235717 4363472337158076816419197)
                    ·
                      refine ⟨1636302126434278806157199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4363472337158076816419197 1636302126434278806157199)
                      ·
                        rfl

theorem cell23_3186687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 4, 3].length) (baseStart_3186687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186687 prefixEnd_3186687 := by exact prefixLift 3186687
  have htrace : WordTrace (prefixWord ++ tailWord_3186687) baseStart_3186687 baseEnd_3186687 := by
    simpa [prefixWord, tailWord_3186687, baseEnd_3186687] using wordTrace_append hprefix tailTrace_3186687
  have hstable : (prefixWord ++ tailWord_3186687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186687).length < 2 ^ (prefixWord ++ tailWord_3186687).sum := by decide
  have hdescent : baseEnd_3186687 < baseStart_3186687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186758 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 5]
def baseStart_3186758 : Nat := 118140960795 + 3186758 * 2 ^ 59
def prefixEnd_3186758 : Nat := 4983230072969 + 3 ^ 40 * 3186758 * 2
def baseEnd_3186758 : Nat := 181815398173416447596597

theorem tailTrace_3186758 : CollatzResearch.WordTrace tailWord_3186758 prefixEnd_3186758 181815398173416447596597 := by
  unfold tailWord_3186758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632206655903984243161279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77487075325951663854107285 3632206655903984243161279)
  ·
    refine ⟨5448309983855976364741919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3632206655903984243161279 5448309983855976364741919)
    ·
      refine ⟨8172464975783964547112879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5448309983855976364741919 8172464975783964547112879)
      ·
        refine ⟨12258697463675946820669319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8172464975783964547112879 12258697463675946820669319)
        ·
          refine ⟨18388046195513920231003979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12258697463675946820669319 18388046195513920231003979)
          ·
            refine ⟨27582069293270880346505969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18388046195513920231003979 27582069293270880346505969)
            ·
              refine ⟨20686551969953160259879477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27582069293270880346505969 20686551969953160259879477)
              ·
                refine ⟨1939364247183108774363701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20686551969953160259879477 1939364247183108774363701)
                ·
                  refine ⟨181815398173416447596597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1939364247183108774363701 181815398173416447596597)
                  ·
                    rfl

theorem cell23_3186758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_3186758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186758 prefixEnd_3186758 := by exact prefixLift 3186758
  have htrace : WordTrace (prefixWord ++ tailWord_3186758) baseStart_3186758 baseEnd_3186758 := by
    simpa [prefixWord, tailWord_3186758, baseEnd_3186758] using wordTrace_append hprefix tailTrace_3186758
  have hstable : (prefixWord ++ tailWord_3186758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186758).length < 2 ^ (prefixWord ++ tailWord_3186758).sum := by decide
  have hdescent : baseEnd_3186758 < baseStart_3186758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186777 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 5]
def baseStart_3186777 : Nat := 118140960795 + 3186777 * 2 ^ 59
def prefixEnd_3186777 : Nat := 4983230072969 + 3 ^ 40 * 3186777 * 2
def baseEnd_3186777 : Nat := 1636348339693183454031785

theorem tailTrace_3186777 : CollatzResearch.WordTrace tailWord_3186777 prefixEnd_3186777 1636348339693183454031785 := by
  unfold tailWord_3186777
  simp only [CollatzResearch.WordTrace]
  refine ⟨116231305975858662026102585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77487537317239108017401723 116231305975858662026102585)
  ·
    refine ⟨87173479481893996519576939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116231305975858662026102585 87173479481893996519576939)
    ·
      refine ⟨130760219222840994779365409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87173479481893996519576939 130760219222840994779365409)
      ·
        refine ⟨98070164417130746084524057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130760219222840994779365409 98070164417130746084524057)
        ·
          refine ⟨73552623312848059563393043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98070164417130746084524057 73552623312848059563393043)
          ·
            refine ⟨110328934969272089345089565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73552623312848059563393043 110328934969272089345089565)
            ·
              refine ⟨41373350613477033504408587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110328934969272089345089565 41373350613477033504408587)
              ·
                refine ⟨62060025920215550256612881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41373350613477033504408587 62060025920215550256612881)
                ·
                  refine ⟨46545019440161662692459661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62060025920215550256612881 46545019440161662692459661)
                  ·
                    refine ⟨17454382290060623509672373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46545019440161662692459661 17454382290060623509672373)
                    ·
                      refine ⟨1636348339693183454031785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17454382290060623509672373 1636348339693183454031785)
                      ·
                        rfl

theorem cell23_3186777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 3, 5].length) (baseStart_3186777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186777 prefixEnd_3186777 := by exact prefixLift 3186777
  have htrace : WordTrace (prefixWord ++ tailWord_3186777) baseStart_3186777 baseEnd_3186777 := by
    simpa [prefixWord, tailWord_3186777, baseEnd_3186777] using wordTrace_append hprefix tailTrace_3186777
  have hstable : (prefixWord ++ tailWord_3186777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186777).length < 2 ^ (prefixWord ++ tailWord_3186777).sum := by decide
  have hdescent : baseEnd_3186777 < baseStart_3186777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186781 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_3186781 : Nat := 118140960795 + 3186781 * 2 ^ 59
def prefixEnd_3186781 : Nat := 4983230072969 + 3 ^ 40 * 3186781 * 2
def baseEnd_3186781 : Nat := 1636350393615801438381767

theorem tailTrace_3186781 : CollatzResearch.WordTrace tailWord_3186781 prefixEnd_3186781 1636350393615801438381767 := by
  unfold tailWord_3186781
  simp only [CollatzResearch.WordTrace]
  refine ⟨116231451867844170709248197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77487634578562780472832131 116231451867844170709248197)
  ·
    refine ⟨21793397225220782007984037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116231451867844170709248197 21793397225220782007984037)
    ·
      refine ⟨4086261979728896626497007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21793397225220782007984037 4086261979728896626497007)
      ·
        refine ⟨6129392969593344939745511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086261979728896626497007 6129392969593344939745511)
        ·
          refine ⟨9194089454390017409618267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6129392969593344939745511 9194089454390017409618267)
          ·
            refine ⟨13791134181585026114427401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194089454390017409618267 13791134181585026114427401)
            ·
              refine ⟨10343350636188769585820551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13791134181585026114427401 10343350636188769585820551)
              ·
                refine ⟨15515025954283154378730827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10343350636188769585820551 15515025954283154378730827)
                ·
                  refine ⟨23272538931424731568096241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15515025954283154378730827 23272538931424731568096241)
                  ·
                    refine ⟨17454404198568548676072181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23272538931424731568096241 17454404198568548676072181)
                    ·
                      refine ⟨1636350393615801438381767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17454404198568548676072181 1636350393615801438381767)
                      ·
                        rfl

theorem cell23_3186781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_3186781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186781 prefixEnd_3186781 := by exact prefixLift 3186781
  have htrace : WordTrace (prefixWord ++ tailWord_3186781) baseStart_3186781 baseEnd_3186781 := by
    simpa [prefixWord, tailWord_3186781, baseEnd_3186781] using wordTrace_append hprefix tailTrace_3186781
  have hstable : (prefixWord ++ tailWord_3186781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186781).length < 2 ^ (prefixWord ++ tailWord_3186781).sum := by decide
  have hdescent : baseEnd_3186781 < baseStart_3186781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186791 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_3186791 : Nat := 118140960795 + 3186791 * 2 ^ 59
def prefixEnd_3186791 : Nat := 4983230072969 + 3 ^ 40 * 3186791 * 2
def baseEnd_3186791 : Nat := 1636355528422346399256721

theorem tailTrace_3186791 : CollatzResearch.WordTrace tailWord_3186791 prefixEnd_3186791 1636355528422346399256721 := by
  unfold tailWord_3186791
  simp only [CollatzResearch.WordTrace]
  refine ⟨116231816597807942417112227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77487877731871961611408151 116231816597807942417112227)
  ·
    refine ⟨174347724896711913625668341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116231816597807942417112227 174347724896711913625668341)
    ·
      refine ⟨16345099209066741902406407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174347724896711913625668341 16345099209066741902406407)
      ·
        refine ⟨24517648813600112853609611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16345099209066741902406407 24517648813600112853609611)
        ·
          refine ⟨36776473220400169280414417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24517648813600112853609611 36776473220400169280414417)
          ·
            refine ⟨27582354915300126960310813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36776473220400169280414417 27582354915300126960310813)
            ·
              refine ⟨10343383093237547610116555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27582354915300126960310813 10343383093237547610116555)
              ·
                refine ⟨15515074639856321415174833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10343383093237547610116555 15515074639856321415174833)
                ·
                  refine ⟨11636305979892241061381125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15515074639856321415174833 11636305979892241061381125)
                  ·
                    refine ⟨2181807371229795199008961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11636305979892241061381125 2181807371229795199008961)
                    ·
                      refine ⟨1636355528422346399256721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181807371229795199008961 1636355528422346399256721)
                      ·
                        rfl

theorem cell23_3186791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_3186791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186791 prefixEnd_3186791 := by exact prefixLift 3186791
  have htrace : WordTrace (prefixWord ++ tailWord_3186791) baseStart_3186791 baseEnd_3186791 := by
    simpa [prefixWord, tailWord_3186791, baseEnd_3186791] using wordTrace_append hprefix tailTrace_3186791
  have hstable : (prefixWord ++ tailWord_3186791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186791).length < 2 ^ (prefixWord ++ tailWord_3186791).sum := by decide
  have hdescent : baseEnd_3186791 < baseStart_3186791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186834 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_3186834 : Nat := 118140960795 + 3186834 * 2 ^ 59
def prefixEnd_3186834 : Nat := 4983230072969 + 3 ^ 40 * 3186834 * 2
def baseEnd_3186834 : Nat := 1636377608090489731019023

theorem tailTrace_3186834 : CollatzResearch.WordTrace tailWord_3186834 prefixEnd_3186834 1636377608090489731019023 := by
  unfold tailWord_3186834
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058346234163040190231889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77488923291101440507285037 29058346234163040190231889)
  ·
    refine ⟨21793759675622280142673917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29058346234163040190231889 21793759675622280142673917)
    ·
      refine ⟨8172659878358355053502719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21793759675622280142673917 8172659878358355053502719)
      ·
        refine ⟨12258989817537532580254079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8172659878358355053502719 12258989817537532580254079)
        ·
          refine ⟨18388484726306298870381119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12258989817537532580254079 18388484726306298870381119)
          ·
            refine ⟨27582727089459448305571679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18388484726306298870381119 27582727089459448305571679)
            ·
              refine ⟨41374090634189172458357519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27582727089459448305571679 41374090634189172458357519)
              ·
                refine ⟨62061135951283758687536279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41374090634189172458357519 62061135951283758687536279)
                ·
                  refine ⟨93091703926925638031304419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62061135951283758687536279 93091703926925638031304419)
                  ·
                    refine ⟨139637555890388457046956629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93091703926925638031304419 139637555890388457046956629)
                    ·
                      refine ⟨1636377608090489731019023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 139637555890388457046956629 1636377608090489731019023)
                      ·
                        rfl

theorem cell23_3186834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_3186834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186834 prefixEnd_3186834 := by exact prefixLift 3186834
  have htrace : WordTrace (prefixWord ++ tailWord_3186834) baseStart_3186834 baseEnd_3186834 := by
    simpa [prefixWord, tailWord_3186834, baseEnd_3186834] using wordTrace_append hprefix tailTrace_3186834
  have hstable : (prefixWord ++ tailWord_3186834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186834).length < 2 ^ (prefixWord ++ tailWord_3186834).sum := by decide
  have hdescent : baseEnd_3186834 < baseStart_3186834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186869 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 1, 4]
def baseStart_3186869 : Nat := 118140960795 + 3186869 * 2 ^ 59
def prefixEnd_3186869 : Nat := 4983230072969 + 3 ^ 40 * 3186869 * 2
def baseEnd_3186869 : Nat := 545465193304465698027121

theorem tailTrace_3186869 : CollatzResearch.WordTrace tailWord_3186869 prefixEnd_3186869 545465193304465698027121 := by
  unfold tailWord_3186869
  simp only [CollatzResearch.WordTrace]
  refine ⟨116234661491525361738451661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77489774327683574492301107 116234661491525361738451661)
  ·
    refine ⟨43587998059322010651919373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116234661491525361738451661 43587998059322010651919373)
    ·
      refine ⟨16345499272245753994469765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43587998059322010651919373 16345499272245753994469765)
      ·
        refine ⟨3064781113546078873963081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16345499272245753994469765 3064781113546078873963081)
        ·
          refine ⟨2298585835159559155472311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3064781113546078873963081 2298585835159559155472311)
          ·
            refine ⟨3447878752739338733208467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2298585835159559155472311 3447878752739338733208467)
            ·
              refine ⟨5171818129109008099812701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447878752739338733208467 5171818129109008099812701)
              ·
                refine ⟨1939431798415878037429763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5171818129109008099812701 1939431798415878037429763)
                ·
                  refine ⟨2909147697623817056144645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939431798415878037429763 2909147697623817056144645)
                  ·
                    refine ⟨545465193304465698027121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2909147697623817056144645 545465193304465698027121)
                    ·
                      rfl

theorem cell23_3186869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_3186869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186869 prefixEnd_3186869 := by exact prefixLift 3186869
  have htrace : WordTrace (prefixWord ++ tailWord_3186869) baseStart_3186869 baseEnd_3186869 := by
    simpa [prefixWord, tailWord_3186869, baseEnd_3186869] using wordTrace_append hprefix tailTrace_3186869
  have hstable : (prefixWord ++ tailWord_3186869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186869).length < 2 ^ (prefixWord ++ tailWord_3186869).sum := by decide
  have hdescent : baseEnd_3186869 < baseStart_3186869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186874 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 1, 6]
def baseStart_3186874 : Nat := 118140960795 + 3186874 * 2 ^ 59
def prefixEnd_3186874 : Nat := 4983230072969 + 3 ^ 40 * 3186874 * 2
def baseEnd_3186874 : Nat := 545466049105556524839613

theorem tailTrace_3186874 : CollatzResearch.WordTrace tailWord_3186874 prefixEnd_3186874 545466049105556524839613 := by
  unfold tailWord_3186874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29058710964126811898095919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77489895904338165061589117 29058710964126811898095919)
  ·
    refine ⟨43588066446190217847143879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29058710964126811898095919 43588066446190217847143879)
    ·
      refine ⟨65382099669285326770715819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43588066446190217847143879 65382099669285326770715819)
      ·
        refine ⟨98073149503927990156073729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65382099669285326770715819 98073149503927990156073729)
        ·
          refine ⟨73554862127945992617055297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98073149503927990156073729 73554862127945992617055297)
          ·
            refine ⟨55166146595959494462791473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73554862127945992617055297 55166146595959494462791473)
            ·
              refine ⟨41374609946969620847093605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55166146595959494462791473 41374609946969620847093605)
              ·
                refine ⟨7757739365056803908830051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41374609946969620847093605 7757739365056803908830051)
                ·
                  refine ⟨11636609047585205863245077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757739365056803908830051 11636609047585205863245077)
                  ·
                    refine ⟨545466049105556524839613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11636609047585205863245077 545466049105556524839613)
                    ·
                      rfl

theorem cell23_3186874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 1, 6].length) (baseStart_3186874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186874 prefixEnd_3186874 := by exact prefixLift 3186874
  have htrace : WordTrace (prefixWord ++ tailWord_3186874) baseStart_3186874 baseEnd_3186874 := by
    simpa [prefixWord, tailWord_3186874, baseEnd_3186874] using wordTrace_append hprefix tailTrace_3186874
  have hstable : (prefixWord ++ tailWord_3186874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186874).length < 2 ^ (prefixWord ++ tailWord_3186874).sum := by decide
  have hdescent : baseEnd_3186874 < baseStart_3186874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186891 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 2, 4]
def baseStart_3186891 : Nat := 118140960795 + 3186891 * 2 ^ 59
def prefixEnd_3186891 : Nat := 4983230072969 + 3 ^ 40 * 3186891 * 2
def baseEnd_3186891 : Nat := 545468958829265336002087

theorem tailTrace_3186891 : CollatzResearch.WordTrace tailWord_3186891 prefixEnd_3186891 545468958829265336002087 := by
  unfold tailWord_3186891
  simp only [CollatzResearch.WordTrace]
  refine ⟨116235463897445659495752527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77490309264963772997168351 116235463897445659495752527)
  ·
    refine ⟨174353195846168489243628791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116235463897445659495752527 174353195846168489243628791)
    ·
      refine ⟨261529793769252733865443187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174353195846168489243628791 261529793769252733865443187)
      ·
        refine ⟨392294690653879100798164781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261529793769252733865443187 392294690653879100798164781)
        ·
          refine ⟨147110508995204662799311793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392294690653879100798164781 147110508995204662799311793)
          ·
            refine ⟨110332881746403497099483845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147110508995204662799311793 110332881746403497099483845)
            ·
              refine ⟨20687415327450655706153221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110332881746403497099483845 20687415327450655706153221)
              ·
                refine ⟨3878890373896997944903729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20687415327450655706153221 3878890373896997944903729)
                ·
                  refine ⟨2909167780422748458677797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3878890373896997944903729 2909167780422748458677797)
                  ·
                    refine ⟨545468958829265336002087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2909167780422748458677797 545468958829265336002087)
                    ·
                      rfl

theorem cell23_3186891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 4].length) (baseStart_3186891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186891 prefixEnd_3186891 := by exact prefixLift 3186891
  have htrace : WordTrace (prefixWord ++ tailWord_3186891) baseStart_3186891 baseEnd_3186891 := by
    simpa [prefixWord, tailWord_3186891, baseEnd_3186891] using wordTrace_append hprefix tailTrace_3186891
  have hstable : (prefixWord ++ tailWord_3186891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186891).length < 2 ^ (prefixWord ++ tailWord_3186891).sum := by decide
  have hdescent : baseEnd_3186891 < baseStart_3186891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186892 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3186892 : Nat := 118140960795 + 3186892 * 2 ^ 59
def prefixEnd_3186892 : Nat := 4983230072969 + 3 ^ 40 * 3186892 * 2
def baseEnd_3186892 : Nat := 1636407389968450504093757

theorem tailTrace_3186892 : CollatzResearch.WordTrace tailWord_3186892 prefixEnd_3186892 1636407389968450504093757 := by
  unfold tailWord_3186892
  simp only [CollatzResearch.WordTrace]
  refine ⟨58117750185221018333269465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77490333580294691111025953 58117750185221018333269465)
  ·
    refine ⟨43588312638915763749952099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58117750185221018333269465 43588312638915763749952099)
    ·
      refine ⟨65382468958373645624928149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43588312638915763749952099 65382468958373645624928149)
      ·
        refine ⟨3064803232423764638668507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 65382468958373645624928149 3064803232423764638668507)
        ·
          refine ⟨4597204848635646958002761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064803232423764638668507 4597204848635646958002761)
          ·
            refine ⟨3447903636476735218502071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597204848635646958002761 3447903636476735218502071)
            ·
              refine ⟨5171855454715102827753107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3447903636476735218502071 5171855454715102827753107)
              ·
                refine ⟨7757783182072654241629661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5171855454715102827753107 7757783182072654241629661)
                ·
                  refine ⟨2909168693277245340611123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7757783182072654241629661 2909168693277245340611123)
                  ·
                    refine ⟨4363753039915868010916685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909168693277245340611123 4363753039915868010916685)
                    ·
                      refine ⟨1636407389968450504093757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4363753039915868010916685 1636407389968450504093757)
                      ·
                        rfl

theorem cell23_3186892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3186892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186892 prefixEnd_3186892 := by exact prefixLift 3186892
  have htrace : WordTrace (prefixWord ++ tailWord_3186892) baseStart_3186892 baseEnd_3186892 := by
    simpa [prefixWord, tailWord_3186892, baseEnd_3186892] using wordTrace_append hprefix tailTrace_3186892
  have hstable : (prefixWord ++ tailWord_3186892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186892).length < 2 ^ (prefixWord ++ tailWord_3186892).sum := by decide
  have hdescent : baseEnd_3186892 < baseStart_3186892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186904 : List Nat := [2, 1, 2, 2, 4, 1, 1, 10]
def baseStart_3186904 : Nat := 118140960795 + 3186904 * 2 ^ 59
def prefixEnd_3186904 : Nat := 4983230072969 + 3 ^ 40 * 3186904 * 2
def baseEnd_3186904 : Nat := 60607909323566831746063

theorem tailTrace_3186904 : CollatzResearch.WordTrace tailWord_3186904 prefixEnd_3186904 60607909323566831746063 := by
  unfold tailWord_3186904
  simp only [CollatzResearch.WordTrace]
  refine ⟨58117969023199281357987883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77490625364265708477317177 58117969023199281357987883)
  ·
    refine ⟨87176953534798922036981825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58117969023199281357987883 87176953534798922036981825)
    ·
      refine ⟨65382715151099191527736369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87176953534798922036981825 65382715151099191527736369)
      ·
        refine ⟨49037036363324393645802277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65382715151099191527736369 49037036363324393645802277)
        ·
          refine ⟨9194444318123323808587927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49037036363324393645802277 9194444318123323808587927)
          ·
            refine ⟨13791666477184985712881891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9194444318123323808587927 13791666477184985712881891)
            ·
              refine ⟨20687499715777478569322837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13791666477184985712881891 20687499715777478569322837)
              ·
                refine ⟨60607909323566831746063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20687499715777478569322837 60607909323566831746063)
                ·
                  rfl

theorem cell23_3186904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 10].length) (baseStart_3186904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186904 prefixEnd_3186904 := by exact prefixLift 3186904
  have htrace : WordTrace (prefixWord ++ tailWord_3186904) baseStart_3186904 baseEnd_3186904 := by
    simpa [prefixWord, tailWord_3186904, baseEnd_3186904] using wordTrace_append hprefix tailTrace_3186904
  have hstable : (prefixWord ++ tailWord_3186904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186904).length < 2 ^ (prefixWord ++ tailWord_3186904).sum := by decide
  have hdescent : baseEnd_3186904 < baseStart_3186904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186931 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 3]
def baseStart_3186931 : Nat := 118140960795 + 3186931 * 2 ^ 59
def prefixEnd_3186931 : Nat := 4983230072969 + 3 ^ 40 * 3186931 * 2
def baseEnd_3186931 : Nat := 1636427415713975851506077

theorem tailTrace_3186931 : CollatzResearch.WordTrace tailWord_3186931 prefixEnd_3186931 1636427415713975851506077 := by
  unfold tailWord_3186931
  simp only [CollatzResearch.WordTrace]
  refine ⟨116236922817300746327208647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77491281878200497551472431 116236922817300746327208647)
  ·
    refine ⟨174355384225951119490812971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116236922817300746327208647 174355384225951119490812971)
    ·
      refine ⟨261533076338926679236219457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174355384225951119490812971 261533076338926679236219457)
      ·
        refine ⟨196149807254195009427164593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261533076338926679236219457 196149807254195009427164593)
        ·
          refine ⟨147112355440646257070373445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196149807254195009427164593 147112355440646257070373445)
          ·
            refine ⟨27583566645121173200695021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147112355440646257070373445 27583566645121173200695021)
            ·
              refine ⟨10343837491920439950260633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27583566645121173200695021 10343837491920439950260633)
              ·
                refine ⟨7757878118940329962695475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10343837491920439950260633 7757878118940329962695475)
                ·
                  refine ⟨11636817178410494944043213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7757878118940329962695475 11636817178410494944043213)
                  ·
                    refine ⟨4363806441903935604016205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11636817178410494944043213 4363806441903935604016205)
                    ·
                      refine ⟨1636427415713975851506077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4363806441903935604016205 1636427415713975851506077)
                      ·
                        rfl

theorem cell23_3186931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_3186931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186931 prefixEnd_3186931 := by exact prefixLift 3186931
  have htrace : WordTrace (prefixWord ++ tailWord_3186931) baseStart_3186931 baseEnd_3186931 := by
    simpa [prefixWord, tailWord_3186931, baseEnd_3186931] using wordTrace_append hprefix tailTrace_3186931
  have hstable : (prefixWord ++ tailWord_3186931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186931).length < 2 ^ (prefixWord ++ tailWord_3186931).sum := by decide
  have hdescent : baseEnd_3186931 < baseStart_3186931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186944 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5]
def baseStart_3186944 : Nat := 118140960795 + 3186944 * 2 ^ 59
def prefixEnd_3186944 : Nat := 4983230072969 + 3 ^ 40 * 3186944 * 2
def baseEnd_3186944 : Nat := 1636434090962484300643517

theorem tailTrace_3186944 : CollatzResearch.WordTrace tailWord_3186944 prefixEnd_3186944 1636434090962484300643517 := by
  unfold tailWord_3186944
  simp only [CollatzResearch.WordTrace]
  refine ⟨58118698483126824773715943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77491597977502433031621257 58118698483126824773715943)
  ·
    refine ⟨87178047724690237160573915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58118698483126824773715943 87178047724690237160573915)
    ·
      refine ⟨130767071587035355740860873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87178047724690237160573915 130767071587035355740860873)
      ·
        refine ⟨98075303690276516805645655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130767071587035355740860873 98075303690276516805645655)
        ·
          refine ⟨147112955535414775208468483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98075303690276516805645655 147112955535414775208468483)
          ·
            refine ⟨220669433303122162812702725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147112955535414775208468483 220669433303122162812702725)
            ·
              refine ⟨41375518744335405527381761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220669433303122162812702725 41375518744335405527381761)
              ·
                refine ⟨31031639058251554145536321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41375518744335405527381761 31031639058251554145536321)
                ·
                  refine ⟨23273729293688665609152241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31031639058251554145536321 23273729293688665609152241)
                  ·
                    refine ⟨17455296970266499206864181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23273729293688665609152241 17455296970266499206864181)
                    ·
                      refine ⟨1636434090962484300643517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17455296970266499206864181 1636434090962484300643517)
                      ·
                        rfl

theorem cell23_3186944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_3186944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186944 prefixEnd_3186944 := by exact prefixLift 3186944
  have htrace : WordTrace (prefixWord ++ tailWord_3186944) baseStart_3186944 baseEnd_3186944 := by
    simpa [prefixWord, tailWord_3186944, baseEnd_3186944] using wordTrace_append hprefix tailTrace_3186944
  have hstable : (prefixWord ++ tailWord_3186944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186944).length < 2 ^ (prefixWord ++ tailWord_3186944).sum := by decide
  have hdescent : baseEnd_3186944 < baseStart_3186944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186958 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2]
def baseStart_3186958 : Nat := 118140960795 + 3186958 * 2 ^ 59
def prefixEnd_3186958 : Nat := 4983230072969 + 3 ^ 40 * 3186958 * 2
def baseEnd_3186958 : Nat := 1636441279691647245868453

theorem tailTrace_3186958 : CollatzResearch.WordTrace tailWord_3186958 prefixEnd_3186958 1636441279691647245868453 := by
  unfold tailWord_3186958
  simp only [CollatzResearch.WordTrace]
  refine ⟨14529738448525366242305191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77491938392135286625627685 14529738448525366242305191)
  ·
    refine ⟨21794607672788049363457787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14529738448525366242305191 21794607672788049363457787)
    ·
      refine ⟨32691911509182074045186681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21794607672788049363457787 32691911509182074045186681)
      ·
        refine ⟨24518933631886555533890011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32691911509182074045186681 24518933631886555533890011)
        ·
          refine ⟨36778400447829833300835017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24518933631886555533890011 36778400447829833300835017)
          ·
            refine ⟨27583800335872374975626263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36778400447829833300835017 27583800335872374975626263)
            ·
              refine ⟨41375700503808562463439395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27583800335872374975626263 41375700503808562463439395)
              ·
                refine ⟨62063550755712843695159093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41375700503808562463439395 62063550755712843695159093)
                ·
                  refine ⟨5818457883348079096421165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62063550755712843695159093 5818457883348079096421165)
                  ·
                    refine ⟨2181921706255529661157937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5818457883348079096421165 2181921706255529661157937)
                    ·
                      refine ⟨1636441279691647245868453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181921706255529661157937 1636441279691647245868453)
                      ·
                        rfl

theorem cell23_3186958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_3186958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186958 prefixEnd_3186958 := by exact prefixLift 3186958
  have htrace : WordTrace (prefixWord ++ tailWord_3186958) baseStart_3186958 baseEnd_3186958 := by
    simpa [prefixWord, tailWord_3186958, baseEnd_3186958] using wordTrace_append hprefix tailTrace_3186958
  have hstable : (prefixWord ++ tailWord_3186958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186958).length < 2 ^ (prefixWord ++ tailWord_3186958).sum := by decide
  have hdescent : baseEnd_3186958 < baseStart_3186958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186983 : List Nat := [1, 1, 8, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_3186983 : Nat := 118140960795 + 3186983 * 2 ^ 59
def prefixEnd_3186983 : Nat := 4983230072969 + 3 ^ 40 * 3186983 * 2
def baseEnd_3186983 : Nat := 1636454116708009648055839

theorem tailTrace_3186983 : CollatzResearch.WordTrace tailWord_3186983 prefixEnd_3186983 1636454116708009648055839 := by
  unfold tailWord_3186983
  simp only [CollatzResearch.WordTrace]
  refine ⟨116238819413112359208101603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77492546275408239472067735 116238819413112359208101603)
  ·
    refine ⟨174358229119668538812152405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116238819413112359208101603 174358229119668538812152405)
    ·
      refine ⟨2043260497496115689204911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 174358229119668538812152405 2043260497496115689204911)
      ·
        refine ⟨3064890746244173533807367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043260497496115689204911 3064890746244173533807367)
        ·
          refine ⟨4597336119366260300711051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064890746244173533807367 4597336119366260300711051)
          ·
            refine ⟨6896004179049390451066577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597336119366260300711051 6896004179049390451066577)
            ·
              refine ⟨5172003134287042838299933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6896004179049390451066577 5172003134287042838299933)
              ·
                refine ⟨1939501175357641064362475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5172003134287042838299933 1939501175357641064362475)
                ·
                  refine ⟨2909251763036461596543713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939501175357641064362475 2909251763036461596543713)
                  ·
                    refine ⟨2181938822277346197407785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2909251763036461596543713 2181938822277346197407785)
                    ·
                      refine ⟨1636454116708009648055839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181938822277346197407785 1636454116708009648055839)
                      ·
                        rfl

theorem cell23_3186983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_3186983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186983 prefixEnd_3186983 := by exact prefixLift 3186983
  have htrace : WordTrace (prefixWord ++ tailWord_3186983) baseStart_3186983 baseEnd_3186983 := by
    simpa [prefixWord, tailWord_3186983, baseEnd_3186983] using wordTrace_append hprefix tailTrace_3186983
  have hstable : (prefixWord ++ tailWord_3186983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186983).length < 2 ^ (prefixWord ++ tailWord_3186983).sum := by decide
  have hdescent : baseEnd_3186983 < baseStart_3186983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3186988 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 1, 4, 2]
def baseStart_3186988 : Nat := 118140960795 + 3186988 * 2 ^ 59
def prefixEnd_3186988 : Nat := 4983230072969 + 3 ^ 40 * 3186988 * 2
def baseEnd_3186988 : Nat := 1636456684111282128493315

theorem tailTrace_3186988 : CollatzResearch.WordTrace tailWord_3186988 prefixEnd_3186988 1636456684111282128493315 := by
  unfold tailWord_3186988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58119500889047122531016809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77492667852062830041355745 58119500889047122531016809)
  ·
    refine ⟨43589625666785341898262607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58119500889047122531016809 43589625666785341898262607)
    ·
      refine ⟨65384438500178012847393911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43589625666785341898262607 65384438500178012847393911)
      ·
        refine ⟨98076657750267019271090867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65384438500178012847393911 98076657750267019271090867)
        ·
          refine ⟨147114986625400528906636301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98076657750267019271090867 147114986625400528906636301)
          ·
            refine ⟨55168119984525198339988613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147114986625400528906636301 55168119984525198339988613)
            ·
              refine ⟨10344022497098474688747865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55168119984525198339988613 10344022497098474688747865)
              ·
                refine ⟨7758016872823856016560899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10344022497098474688747865 7758016872823856016560899)
                ·
                  refine ⟨11637025309235784024841349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758016872823856016560899 11637025309235784024841349)
                  ·
                    refine ⟨2181942245481709504657753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11637025309235784024841349 2181942245481709504657753)
                    ·
                      refine ⟨1636456684111282128493315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2181942245481709504657753 1636456684111282128493315)
                      ·
                        rfl

theorem cell23_3186988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_3186988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3186988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3186988 prefixEnd_3186988 := by exact prefixLift 3186988
  have htrace : WordTrace (prefixWord ++ tailWord_3186988) baseStart_3186988 baseEnd_3186988 := by
    simpa [prefixWord, tailWord_3186988, baseEnd_3186988] using wordTrace_append hprefix tailTrace_3186988
  have hstable : (prefixWord ++ tailWord_3186988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3186988).length < 2 ^ (prefixWord ++ tailWord_3186988).sum := by decide
  have hdescent : baseEnd_3186988 < baseStart_3186988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3186988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187045 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 5]
def baseStart_3187045 : Nat := 118140960795 + 3187045 * 2 ^ 59
def prefixEnd_3187045 : Nat := 4983230072969 + 3 ^ 40 * 3187045 * 2
def baseEnd_3187045 : Nat := 181831772500954267275617

theorem tailTrace_3187045 : CollatzResearch.WordTrace tailWord_3187045 prefixEnd_3187045 181831772500954267275617 := by
  unfold tailWord_3187045
  simp only [CollatzResearch.WordTrace]
  refine ⟨116241080738887743796858589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77494053825925162531239059 116241080738887743796858589)
  ·
    refine ⟨43590405277082903923821971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116241080738887743796858589 43590405277082903923821971)
    ·
      refine ⟨65385607915624355885732957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43590405277082903923821971 65385607915624355885732957)
      ·
        refine ⟨24519602968359133457149859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65385607915624355885732957 24519602968359133457149859)
        ·
          refine ⟨36779404452538700185724789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24519602968359133457149859 36779404452538700185724789)
          ·
            refine ⟨3448069167425503142411699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36779404452538700185724789 3448069167425503142411699)
            ·
              refine ⟨5172103751138254713617549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448069167425503142411699 5172103751138254713617549)
              ·
                refine ⟨1939538906676845517606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5172103751138254713617549 1939538906676845517606581)
                ·
                  refine ⟨181831772500954267275617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1939538906676845517606581 181831772500954267275617)
                  ·
                    rfl

theorem cell23_3187045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 5].length) (baseStart_3187045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187045 prefixEnd_3187045 := by exact prefixLift 3187045
  have htrace : WordTrace (prefixWord ++ tailWord_3187045) baseStart_3187045 baseEnd_3187045 := by
    simpa [prefixWord, tailWord_3187045, baseEnd_3187045] using wordTrace_append hprefix tailTrace_3187045
  have hstable : (prefixWord ++ tailWord_3187045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187045).length < 2 ^ (prefixWord ++ tailWord_3187045).sum := by decide
  have hdescent : baseEnd_3187045 < baseStart_3187045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187058 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 2, 5]
def baseStart_3187058 : Nat := 118140960795 + 3187058 * 2 ^ 59
def prefixEnd_3187058 : Nat := 4983230072969 + 3 ^ 40 * 3187058 * 2
def baseEnd_3187058 : Nat := 545497542585698951539331

theorem tailTrace_3187058 : CollatzResearch.WordTrace tailWord_3187058 prefixEnd_3187058 545497542585698951539331 := by
  unfold tailWord_3187058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29060388721960161754270457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77494369925227098011387885 29060388721960161754270457)
  ·
    refine ⟨21795291541470121315702843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29060388721960161754270457 21795291541470121315702843)
    ·
      refine ⟨32692937312205181973554265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21795291541470121315702843 32692937312205181973554265)
      ·
        refine ⟨24519702984153886480165699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32692937312205181973554265 24519702984153886480165699)
        ·
          refine ⟨36779554476230829720248549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24519702984153886480165699 36779554476230829720248549)
          ·
            refine ⟨6896166464293280572546603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36779554476230829720248549 6896166464293280572546603)
            ·
              refine ⟨10344249696439920858819905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896166464293280572546603 10344249696439920858819905)
              ·
                refine ⟨7758187272329940644114929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10344249696439920858819905 7758187272329940644114929)
                ·
                  refine ⟨5818640454247455483086197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7758187272329940644114929 5818640454247455483086197)
                  ·
                    refine ⟨545497542585698951539331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5818640454247455483086197 545497542585698951539331)
                    ·
                      rfl

theorem cell23_3187058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_3187058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187058 prefixEnd_3187058 := by exact prefixLift 3187058
  have htrace : WordTrace (prefixWord ++ tailWord_3187058) baseStart_3187058 baseEnd_3187058 := by
    simpa [prefixWord, tailWord_3187058, baseEnd_3187058] using wordTrace_append hprefix tailTrace_3187058
  have hstable : (prefixWord ++ tailWord_3187058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187058).length < 2 ^ (prefixWord ++ tailWord_3187058).sum := by decide
  have hdescent : baseEnd_3187058 < baseStart_3187058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187062 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 7]
def baseStart_3187062 : Nat := 118140960795 + 3187062 * 2 ^ 59
def prefixEnd_3187062 : Nat := 4983230072969 + 3 ^ 40 * 3187062 * 2
def baseEnd_3187062 : Nat := 181832742408857204329775

theorem tailTrace_3187062 : CollatzResearch.WordTrace tailWord_3187062 prefixEnd_3187062 181832742408857204329775 := by
  unfold tailWord_3187062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7265106298739134731264215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77494467186550770466818293 7265106298739134731264215)
  ·
    refine ⟨10897659448108702096896323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7265106298739134731264215 10897659448108702096896323)
    ·
      refine ⟨16346489172163053145344485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10897659448108702096896323 16346489172163053145344485)
      ·
        refine ⟨3064966719780572464752091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16346489172163053145344485 3064966719780572464752091)
        ·
          refine ⟨4597450079670858697128137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064966719780572464752091 4597450079670858697128137)
          ·
            refine ⟨3448087559753144022846103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597450079670858697128137 3448087559753144022846103)
            ·
              refine ⟨5172131339629716034269155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448087559753144022846103 5172131339629716034269155)
              ·
                refine ⟨7758197009444574051403733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172131339629716034269155 7758197009444574051403733)
                ·
                  refine ⟨181832742408857204329775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7758197009444574051403733 181832742408857204329775)
                  ·
                    rfl

theorem cell23_3187062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 7].length) (baseStart_3187062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187062 prefixEnd_3187062 := by exact prefixLift 3187062
  have htrace : WordTrace (prefixWord ++ tailWord_3187062) baseStart_3187062 baseEnd_3187062 := by
    simpa [prefixWord, tailWord_3187062, baseEnd_3187062] using wordTrace_append hprefix tailTrace_3187062
  have hstable : (prefixWord ++ tailWord_3187062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187062).length < 2 ^ (prefixWord ++ tailWord_3187062).sum := by decide
  have hdescent : baseEnd_3187062 < baseStart_3187062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187165 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_3187165 : Nat := 118140960795 + 3187165 * 2 ^ 59
def prefixEnd_3187165 : Nat := 4983230072969 + 3 ^ 40 * 3187165 * 2
def baseEnd_3187165 : Nat := 545515856729042645326667

theorem tailTrace_3187165 : CollatzResearch.WordTrace tailWord_3187165 prefixEnd_3187165 545515856729042645326667 := by
  unfold tailWord_3187165
  simp only [CollatzResearch.WordTrace]
  refine ⟨116245457498453004291226949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77496971665635336194151299 116245457498453004291226949)
  ·
    refine ⟨21796023280959938304605053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116245457498453004291226949 21796023280959938304605053)
    ·
      refine ⟨8173508730359976864226895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21796023280959938304605053 8173508730359976864226895)
      ·
        refine ⟨12260263095539965296340343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173508730359976864226895 12260263095539965296340343)
        ·
          refine ⟨18390394643309947944510515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12260263095539965296340343 18390394643309947944510515)
          ·
            refine ⟨27585591964964921916765773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18390394643309947944510515 27585591964964921916765773)
            ·
              refine ⟨10344596986861845718787165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27585591964964921916765773 10344596986861845718787165)
              ·
                refine ⟨3879223870073192144545187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10344596986861845718787165 3879223870073192144545187)
                ·
                  refine ⟨5818835805109788216817781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879223870073192144545187 5818835805109788216817781)
                  ·
                    refine ⟨545515856729042645326667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5818835805109788216817781 545515856729042645326667)
                    ·
                      rfl

theorem cell23_3187165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_3187165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187165 prefixEnd_3187165 := by exact prefixLift 3187165
  have htrace : WordTrace (prefixWord ++ tailWord_3187165) baseStart_3187165 baseEnd_3187165 := by
    simpa [prefixWord, tailWord_3187165, baseEnd_3187165] using wordTrace_append hprefix tailTrace_3187165
  have hstable : (prefixWord ++ tailWord_3187165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187165).length < 2 ^ (prefixWord ++ tailWord_3187165).sum := by decide
  have hdescent : baseEnd_3187165 < baseStart_3187165 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187205 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_3187205 : Nat := 118140960795 + 3187205 * 2 ^ 59
def prefixEnd_3187205 : Nat := 4983230072969 + 3 ^ 40 * 3187205 * 2
def baseEnd_3187205 : Nat := 1636568109413307779479817

theorem tailTrace_3187205 : CollatzResearch.WordTrace tailWord_3187205 prefixEnd_3187205 1636568109413307779479817 := by
  unfold tailWord_3187205
  simp only [CollatzResearch.WordTrace]
  refine ⟨116246916418308091122683069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77497944278872060748455379 116246916418308091122683069)
  ·
    refine ⟨43592593656865534171006151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116246916418308091122683069 43592593656865534171006151)
    ·
      refine ⟨65388890485298301256509227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43592593656865534171006151 65388890485298301256509227)
      ·
        refine ⟨98083335727947451884763841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65388890485298301256509227 98083335727947451884763841)
        ·
          refine ⟨73562501795960588913572881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98083335727947451884763841 73562501795960588913572881)
          ·
            refine ⟨55171876346970441685179661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73562501795960588913572881 55171876346970441685179661)
            ·
              refine ⟨20689453630113915631942373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55171876346970441685179661 20689453630113915631942373)
              ·
                refine ⟨3879272555646359180989195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20689453630113915631942373 3879272555646359180989195)
                ·
                  refine ⟨5818908833469538771483793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879272555646359180989195 5818908833469538771483793)
                  ·
                    refine ⟨4364181625102154078612845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5818908833469538771483793 4364181625102154078612845)
                    ·
                      refine ⟨1636568109413307779479817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4364181625102154078612845 1636568109413307779479817)
                      ·
                        rfl

theorem cell23_3187205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_3187205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187205 prefixEnd_3187205 := by exact prefixLift 3187205
  have htrace : WordTrace (prefixWord ++ tailWord_3187205) baseStart_3187205 baseEnd_3187205 := by
    simpa [prefixWord, tailWord_3187205, baseEnd_3187205] using wordTrace_append hprefix tailTrace_3187205
  have hstable : (prefixWord ++ tailWord_3187205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187205).length < 2 ^ (prefixWord ++ tailWord_3187205).sum := by decide
  have hdescent : baseEnd_3187205 < baseStart_3187205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187206 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2]
def baseStart_3187206 : Nat := 118140960795 + 3187206 * 2 ^ 59
def prefixEnd_3187206 : Nat := 4983230072969 + 3 ^ 40 * 3187206 * 2
def baseEnd_3187206 : Nat := 1636568622893962275567313

theorem tailTrace_3187206 : CollatzResearch.WordTrace tailWord_3187206 prefixEnd_3187206 1636568622893962275567313 := by
  unfold tailWord_3187206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3632717277853264634170921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77497968594202978862312981 3632717277853264634170921)
  ·
    refine ⟨2724537958389948475628191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3632717277853264634170921 2724537958389948475628191)
    ·
      refine ⟨4086806937584922713442287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724537958389948475628191 4086806937584922713442287)
      ·
        refine ⟨6130210406377384070163431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086806937584922713442287 6130210406377384070163431)
        ·
          refine ⟨9195315609566076105245147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130210406377384070163431 9195315609566076105245147)
          ·
            refine ⟨13792973414349114157867721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195315609566076105245147 13792973414349114157867721)
            ·
              refine ⟨10344730060761835618400791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13792973414349114157867721 10344730060761835618400791)
              ·
                refine ⟨15517095091142753427601187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10344730060761835618400791 15517095091142753427601187)
                ·
                  refine ⟨23275642636714130141401781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15517095091142753427601187 23275642636714130141401781)
                  ·
                    refine ⟨2182091497191949700756417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23275642636714130141401781 2182091497191949700756417)
                    ·
                      refine ⟨1636568622893962275567313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182091497191949700756417 1636568622893962275567313)
                      ·
                        rfl

theorem cell23_3187206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_3187206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187206 prefixEnd_3187206 := by exact prefixLift 3187206
  have htrace : WordTrace (prefixWord ++ tailWord_3187206) baseStart_3187206 baseEnd_3187206 := by
    simpa [prefixWord, tailWord_3187206, baseEnd_3187206] using wordTrace_append hprefix tailTrace_3187206
  have hstable : (prefixWord ++ tailWord_3187206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187206).length < 2 ^ (prefixWord ++ tailWord_3187206).sum := by decide
  have hdescent : baseEnd_3187206 < baseStart_3187206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187213 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_3187213 : Nat := 118140960795 + 3187213 * 2 ^ 59
def prefixEnd_3187213 : Nat := 4983230072969 + 3 ^ 40 * 3187213 * 2
def baseEnd_3187213 : Nat := 1636572217258543748179781

theorem tailTrace_3187213 : CollatzResearch.WordTrace tailWord_3187213 prefixEnd_3187213 1636572217258543748179781 := by
  unfold tailWord_3187213
  simp only [CollatzResearch.WordTrace]
  refine ⟨116247208202279108488974293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77498138801519405659316195 116247208202279108488974293)
  ·
    refine ⟨2724543942240916605210335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 116247208202279108488974293 2724543942240916605210335)
    ·
      refine ⟨4086815913361374907815503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2724543942240916605210335 4086815913361374907815503)
      ·
        refine ⟨6130223870042062361723255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4086815913361374907815503 6130223870042062361723255)
        ·
          refine ⟨9195335805063093542584883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6130223870042062361723255 9195335805063093542584883)
          ·
            refine ⟨13793003707594640313877325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195335805063093542584883 13793003707594640313877325)
            ·
              refine ⟨5172376390347990117703997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13793003707594640313877325 5172376390347990117703997)
              ·
                refine ⟨1939641146380496294138999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5172376390347990117703997 1939641146380496294138999)
                ·
                  refine ⟨2909461719570744441208499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939641146380496294138999 2909461719570744441208499)
                  ·
                    refine ⟨4364192579356116661812749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909461719570744441208499 4364192579356116661812749)
                    ·
                      refine ⟨1636572217258543748179781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4364192579356116661812749 1636572217258543748179781)
                      ·
                        rfl

theorem cell23_3187213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_3187213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187213 prefixEnd_3187213 := by exact prefixLift 3187213
  have htrace : WordTrace (prefixWord ++ tailWord_3187213) baseStart_3187213 baseEnd_3187213 := by
    simpa [prefixWord, tailWord_3187213, baseEnd_3187213] using wordTrace_append hprefix tailTrace_3187213
  have hstable : (prefixWord ++ tailWord_3187213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187213).length < 2 ^ (prefixWord ++ tailWord_3187213).sum := by decide
  have hdescent : baseEnd_3187213 < baseStart_3187213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187246 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_3187246 : Nat := 118140960795 + 3187246 * 2 ^ 59
def prefixEnd_3187246 : Nat := 4983230072969 + 3 ^ 40 * 3187246 * 2
def baseEnd_3187246 : Nat := 545529720706714039689043

theorem tailTrace_3187246 : CollatzResearch.WordTrace tailWord_3187246 prefixEnd_3187246 545529720706714039689043 := by
  unfold tailWord_3187246
  simp only [CollatzResearch.WordTrace]
  refine ⟨14531051476394944390615699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77498941207439703416617061 14531051476394944390615699)
  ·
    refine ⟨21796577214592416585923549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14531051476394944390615699 21796577214592416585923549)
    ·
      refine ⟨8173716455472156219721331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21796577214592416585923549 8173716455472156219721331)
      ·
        refine ⟨12260574683208234329581997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8173716455472156219721331 12260574683208234329581997)
        ·
          refine ⟨4597715506203087873593249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12260574683208234329581997 4597715506203087873593249)
          ·
            refine ⟨3448286629652315905194937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4597715506203087873593249 3448286629652315905194937)
            ·
              refine ⟨2586214972239236928896203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3448286629652315905194937 2586214972239236928896203)
              ·
                refine ⟨3879322458358855393344305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2586214972239236928896203 3879322458358855393344305)
                ·
                  refine ⟨2909491843769141545008229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3879322458358855393344305 2909491843769141545008229)
                  ·
                    refine ⟨545529720706714039689043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2909491843769141545008229 545529720706714039689043)
                    ·
                      rfl

theorem cell23_3187246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_3187246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187246 prefixEnd_3187246 := by exact prefixLift 3187246
  have htrace : WordTrace (prefixWord ++ tailWord_3187246) baseStart_3187246 baseEnd_3187246 := by
    simpa [prefixWord, tailWord_3187246, baseEnd_3187246] using wordTrace_append hprefix tailTrace_3187246
  have hstable : (prefixWord ++ tailWord_3187246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187246).length < 2 ^ (prefixWord ++ tailWord_3187246).sum := by decide
  have hdescent : baseEnd_3187246 < baseStart_3187246 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187275 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 3, 4, 2]
def baseStart_3187275 : Nat := 118140960795 + 3187275 * 2 ^ 59
def prefixEnd_3187275 : Nat := 4983230072969 + 3 ^ 40 * 3187275 * 2
def baseEnd_3187275 : Nat := 1636604053059122505604495

theorem tailTrace_3187275 : CollatzResearch.WordTrace tailWord_3187275 prefixEnd_3187275 1636604053059122505604495 := by
  unfold tailWord_3187275
  simp only [CollatzResearch.WordTrace]
  refine ⟨116249469528054493077731279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77499646352036328718487519 116249469528054493077731279)
  ·
    refine ⟨174374204292081739616596919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116249469528054493077731279 174374204292081739616596919)
    ·
      refine ⟨261561306438122609424895379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174374204292081739616596919 261561306438122609424895379)
      ·
        refine ⟨392341959657183914137343069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261561306438122609424895379 392341959657183914137343069)
        ·
          refine ⟨147128234871443967801503651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392341959657183914137343069 147128234871443967801503651)
          ·
            refine ⟨220692352307165951702255477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147128234871443967801503651 220692352307165951702255477)
            ·
              refine ⟨20689908028796807972086451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220692352307165951702255477 20689908028796807972086451)
              ·
                refine ⟨31034862043195211958129677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20689908028796807972086451 31034862043195211958129677)
                ·
                  refine ⟨11638073266198204484298629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31034862043195211958129677 11638073266198204484298629)
                  ·
                    refine ⟨2182138737412163340805993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11638073266198204484298629 2182138737412163340805993)
                    ·
                      refine ⟨1636604053059122505604495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182138737412163340805993 1636604053059122505604495)
                      ·
                        rfl

theorem cell23_3187275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 4, 2].length) (baseStart_3187275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187275 prefixEnd_3187275 := by exact prefixLift 3187275
  have htrace : WordTrace (prefixWord ++ tailWord_3187275) baseStart_3187275 baseEnd_3187275 := by
    simpa [prefixWord, tailWord_3187275, baseEnd_3187275] using wordTrace_append hprefix tailTrace_3187275
  have hstable : (prefixWord ++ tailWord_3187275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187275).length < 2 ^ (prefixWord ++ tailWord_3187275).sum := by decide
  have hdescent : baseEnd_3187275 < baseStart_3187275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187309 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 1, 4, 2]
def baseStart_3187309 : Nat := 118140960795 + 3187309 * 2 ^ 59
def prefixEnd_3187309 : Nat := 4983230072969 + 3 ^ 40 * 3187309 * 2
def baseEnd_3187309 : Nat := 1636621511401375372579339

theorem tailTrace_3187309 : CollatzResearch.WordTrace tailWord_3187309 prefixEnd_3187309 1636621511401375372579339 := by
  unfold tailWord_3187309
  simp only [CollatzResearch.WordTrace]
  refine ⟨116250709609931316884468981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77500473073287544589645987 116250709609931316884468981)
  ·
    refine ⟨10898504025931060957918967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116250709609931316884468981 10898504025931060957918967)
    ·
      refine ⟨16347756038896591436878451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10898504025931060957918967 16347756038896591436878451)
      ·
        refine ⟨24521634058344887155317677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16347756038896591436878451 24521634058344887155317677)
        ·
          refine ⟨9195612771879332683244129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24521634058344887155317677 9195612771879332683244129)
          ·
            refine ⟨6896709578909499512433097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9195612771879332683244129 6896709578909499512433097)
            ·
              refine ⟨5172532184182124634324823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6896709578909499512433097 5172532184182124634324823)
              ·
                refine ⟨7758798276273186951487235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172532184182124634324823 7758798276273186951487235)
                ·
                  refine ⟨11638197414409780427230853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7758798276273186951487235 11638197414409780427230853)
                  ·
                    refine ⟨2182162015201833830105785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11638197414409780427230853 2182162015201833830105785)
                    ·
                      refine ⟨1636621511401375372579339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182162015201833830105785 1636621511401375372579339)
                      ·
                        rfl

theorem cell23_3187309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_3187309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187309 prefixEnd_3187309 := by exact prefixLift 3187309
  have htrace : WordTrace (prefixWord ++ tailWord_3187309) baseStart_3187309 baseEnd_3187309 := by
    simpa [prefixWord, tailWord_3187309, baseEnd_3187309] using wordTrace_append hprefix tailTrace_3187309
  have hstable : (prefixWord ++ tailWord_3187309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187309).length < 2 ^ (prefixWord ++ tailWord_3187309).sum := by decide
  have hdescent : baseEnd_3187309 < baseStart_3187309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187330 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 1, 3, 2]
def baseStart_3187330 : Nat := 118140960795 + 3187330 * 2 ^ 59
def prefixEnd_3187330 : Nat := 4983230072969 + 3 ^ 40 * 3187330 * 2
def baseEnd_3187330 : Nat := 1636632294495119790416743

theorem tailTrace_3187330 : CollatzResearch.WordTrace tailWord_3187330 prefixEnd_3187330 1636632294495119790416743 := by
  unfold tailWord_3187330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29062868885713809367745861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77500983695236824980655629 29062868885713809367745861)
  ·
    refine ⟨5449287916071339256452349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29062868885713809367745861 5449287916071339256452349)
    ·
      refine ⟨2043482968526752221169631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5449287916071339256452349 2043482968526752221169631)
      ·
        refine ⟨3065224452790128331754447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043482968526752221169631 3065224452790128331754447)
        ·
          refine ⟨4597836679185192497631671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065224452790128331754447 4597836679185192497631671)
          ·
            refine ⟨6896755018777788746447507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4597836679185192497631671 6896755018777788746447507)
            ·
              refine ⟨10345132528166683119671261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6896755018777788746447507 10345132528166683119671261)
              ·
                refine ⟨3879424698062506169876723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10345132528166683119671261 3879424698062506169876723)
                ·
                  refine ⟨5819137047093759254815085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879424698062506169876723 5819137047093759254815085)
                  ·
                    refine ⟨2182176392660159720555657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5819137047093759254815085 2182176392660159720555657)
                    ·
                      refine ⟨1636632294495119790416743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182176392660159720555657 1636632294495119790416743)
                      ·
                        rfl

theorem cell23_3187330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_3187330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187330 prefixEnd_3187330 := by exact prefixLift 3187330
  have htrace : WordTrace (prefixWord ++ tailWord_3187330) baseStart_3187330 baseEnd_3187330 := by
    simpa [prefixWord, tailWord_3187330, baseEnd_3187330] using wordTrace_append hprefix tailTrace_3187330
  have hstable : (prefixWord ++ tailWord_3187330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187330).length < 2 ^ (prefixWord ++ tailWord_3187330).sum := by decide
  have hdescent : baseEnd_3187330 < baseStart_3187330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187332 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 5]
def baseStart_3187332 : Nat := 118140960795 + 3187332 * 2 ^ 59
def prefixEnd_3187332 : Nat := 4983230072969 + 3 ^ 40 * 3187332 * 2
def baseEnd_3187332 : Nat := 181848146828492086954637

theorem tailTrace_3187332 : CollatzResearch.WordTrace tailWord_3187332 prefixEnd_3187332 181848146828492086954637 := by
  unfold tailWord_3187332
  simp only [CollatzResearch.WordTrace]
  refine ⟨58125774244423995906278125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77501032325898661208370833 58125774244423995906278125)
  ·
    refine ⟨21797165341658998464854297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58125774244423995906278125 21797165341658998464854297)
    ·
      refine ⟨16347874006244248848640723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21797165341658998464854297 16347874006244248848640723)
      ·
        refine ⟨24521811009366373272961085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16347874006244248848640723 24521811009366373272961085)
        ·
          refine ⟨9195679128512389977360407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24521811009366373272961085 9195679128512389977360407)
          ·
            refine ⟨13793518692768584966040611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195679128512389977360407 13793518692768584966040611)
            ·
              refine ⟨20690278039152877449060917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13793518692768584966040611 20690278039152877449060917)
              ·
                refine ⟨1939713566170582260849461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20690278039152877449060917 1939713566170582260849461)
                ·
                  refine ⟨181848146828492086954637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1939713566170582260849461 181848146828492086954637)
                  ·
                    rfl

theorem cell23_3187332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_3187332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187332 prefixEnd_3187332 := by exact prefixLift 3187332
  have htrace : WordTrace (prefixWord ++ tailWord_3187332) baseStart_3187332 baseEnd_3187332 := by
    simpa [prefixWord, tailWord_3187332, baseEnd_3187332] using wordTrace_append hprefix tailTrace_3187332
  have hstable : (prefixWord ++ tailWord_3187332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187332).length < 2 ^ (prefixWord ++ tailWord_3187332).sum := by decide
  have hdescent : baseEnd_3187332 < baseStart_3187332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187402 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3]
def baseStart_3187402 : Nat := 118140960795 + 3187402 * 2 ^ 59
def prefixEnd_3187402 : Nat := 4983230072969 + 3 ^ 40 * 3187402 * 2
def baseEnd_3187402 : Nat := 1636669265102243508716411

theorem tailTrace_3187402 : CollatzResearch.WordTrace tailWord_3187402 prefixEnd_3187402 1636669265102243508716411 := by
  unfold tailWord_3187402
  simp only [CollatzResearch.WordTrace]
  refine ⟨29063525399648598441901115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77502734399062929178402973 29063525399648598441901115)
  ·
    refine ⟨43595288099472897662851673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29063525399648598441901115 43595288099472897662851673)
    ·
      refine ⟨32696466074604673247138755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43595288099472897662851673 32696466074604673247138755)
      ·
        refine ⟨49044699111907009870708133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32696466074604673247138755 49044699111907009870708133)
        ·
          refine ⟨9195881083482564350757775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49044699111907009870708133 9195881083482564350757775)
          ·
            refine ⟨13793821625223846526136663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9195881083482564350757775 13793821625223846526136663)
            ·
              refine ⟨20690732437835769789204995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13793821625223846526136663 20690732437835769789204995)
              ·
                refine ⟨31036098656753654683807493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20690732437835769789204995 31036098656753654683807493)
                ·
                  refine ⟨5819268498141310253213905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31036098656753654683807493 5819268498141310253213905)
                  ·
                    refine ⟨4364451373605982689910429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5819268498141310253213905 4364451373605982689910429)
                    ·
                      refine ⟨1636669265102243508716411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4364451373605982689910429 1636669265102243508716411)
                      ·
                        rfl

theorem cell23_3187402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 4, 2, 3].length) (baseStart_3187402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187402 prefixEnd_3187402 := by exact prefixLift 3187402
  have htrace : WordTrace (prefixWord ++ tailWord_3187402) baseStart_3187402 baseEnd_3187402 := by
    simpa [prefixWord, tailWord_3187402, baseEnd_3187402] using wordTrace_append hprefix tailTrace_3187402
  have hstable : (prefixWord ++ tailWord_3187402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187402).length < 2 ^ (prefixWord ++ tailWord_3187402).sum := by decide
  have hdescent : baseEnd_3187402 < baseStart_3187402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187466 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3]
def baseStart_3187466 : Nat := 118140960795 + 3187466 * 2 ^ 59
def prefixEnd_3187466 : Nat := 4983230072969 + 3 ^ 40 * 3187466 * 2
def baseEnd_3187466 : Nat := 1636702127864131258316117

theorem tailTrace_3187466 : CollatzResearch.WordTrace tailWord_3187466 prefixEnd_3187466 1636702127864131258316117 := by
  unfold tailWord_3187466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29064108967590633174483563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77504290580241688465289501 29064108967590633174483563)
  ·
    refine ⟨43596163451385949761725345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29064108967590633174483563 43596163451385949761725345)
    ·
      refine ⟨32697122588539462321294009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43596163451385949761725345 32697122588539462321294009)
      ·
        refine ⟨24522841941404596740970507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32697122588539462321294009 24522841941404596740970507)
        ·
          refine ⟨36784262912106895111455761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24522841941404596740970507 36784262912106895111455761)
          ·
            refine ⟨27588197184080171333591821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36784262912106895111455761 27588197184080171333591821)
            ·
              refine ⟨10345573944030064250096933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27588197184080171333591821 10345573944030064250096933)
              ·
                refine ⟨1939795114505637046893175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10345573944030064250096933 1939795114505637046893175)
                ·
                  refine ⟨2909692671758455570339763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1939795114505637046893175 2909692671758455570339763)
                  ·
                    refine ⟨4364539007637683355509645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909692671758455570339763 4364539007637683355509645)
                    ·
                      refine ⟨1636702127864131258316117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4364539007637683355509645 1636702127864131258316117)
                      ·
                        rfl

theorem cell23_3187466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 1, 1, 3].length) (baseStart_3187466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187466 prefixEnd_3187466 := by exact prefixLift 3187466
  have htrace : WordTrace (prefixWord ++ tailWord_3187466) baseStart_3187466 baseEnd_3187466 := by
    simpa [prefixWord, tailWord_3187466, baseEnd_3187466] using wordTrace_append hprefix tailTrace_3187466
  have hstable : (prefixWord ++ tailWord_3187466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187466).length < 2 ^ (prefixWord ++ tailWord_3187466).sum := by decide
  have hdescent : baseEnd_3187466 < baseStart_3187466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187475 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5]
def baseStart_3187475 : Nat := 118140960795 + 3187475 * 2 ^ 59
def prefixEnd_3187475 : Nat := 4983230072969 + 3 ^ 40 * 3187475 * 2
def baseEnd_3187475 : Nat := 1636706749190021723103575

theorem tailTrace_3187475 : CollatzResearch.WordTrace tailWord_3187475 prefixEnd_3187475 1636706749190021723103575 := by
  unfold tailWord_3187475
  simp only [CollatzResearch.WordTrace]
  refine ⟨116256764127329927235011879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77504509418219951490007919 116256764127329927235011879)
  ·
    refine ⟨174385146190994890852517819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116256764127329927235011879 174385146190994890852517819)
    ·
      refine ⟨261577719286492336278776729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174385146190994890852517819 261577719286492336278776729)
      ·
        refine ⟨196183289464869252209082547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261577719286492336278776729 196183289464869252209082547)
        ·
          refine ⟨294274934197303878313623821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196183289464869252209082547 294274934197303878313623821)
          ·
            refine ⟨110353100323988954367608933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294274934197303878313623821 110353100323988954367608933)
            ·
              refine ⟨20691206310747928943926675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110353100323988954367608933 20691206310747928943926675)
              ·
                refine ⟨31036809466121893415890013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20691206310747928943926675 31036809466121893415890013)
                ·
                  refine ⟨11638803549795710030958755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31036809466121893415890013 11638803549795710030958755)
                  ·
                    refine ⟨17458205324693565046438133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11638803549795710030958755 17458205324693565046438133)
                    ·
                      refine ⟨1636706749190021723103575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17458205324693565046438133 1636706749190021723103575)
                      ·
                        rfl

theorem cell23_3187475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_3187475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187475 prefixEnd_3187475 := by exact prefixLift 3187475
  have htrace : WordTrace (prefixWord ++ tailWord_3187475) baseStart_3187475 baseEnd_3187475 := by
    simpa [prefixWord, tailWord_3187475, baseEnd_3187475] using wordTrace_append hprefix tailTrace_3187475
  have hstable : (prefixWord ++ tailWord_3187475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187475).length < 2 ^ (prefixWord ++ tailWord_3187475).sum := by decide
  have hdescent : baseEnd_3187475 < baseStart_3187475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187482 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 1, 6]
def baseStart_3187482 : Nat := 118140960795 + 3187482 * 2 ^ 59
def prefixEnd_3187482 : Nat := 4983230072969 + 3 ^ 40 * 3187482 * 2
def baseEnd_3187482 : Nat := 545570114518201065238681

theorem tailTrace_3187482 : CollatzResearch.WordTrace tailWord_3187482 prefixEnd_3187482 545570114518201065238681 := by
  unfold tailWord_3187482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29064254859576141857629175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77504679625536378287011133 29064254859576141857629175)
  ·
    refine ⟨43596382289364212786443763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29064254859576141857629175 43596382289364212786443763)
    ·
      refine ⟨65394573434046319179665645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43596382289364212786443763 65394573434046319179665645)
      ·
        refine ⟨24522965037767369692374617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65394573434046319179665645 24522965037767369692374617)
        ·
          refine ⟨18392223778325527269280963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24522965037767369692374617 18392223778325527269280963)
          ·
            refine ⟨27588335667488290903921445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18392223778325527269280963 27588335667488290903921445)
            ·
              refine ⟨5172812937654054544485271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27588335667488290903921445 5172812937654054544485271)
              ·
                refine ⟨7759219406481081816727907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172812937654054544485271 7759219406481081816727907)
                ·
                  refine ⟨11638829109721622725091861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759219406481081816727907 11638829109721622725091861)
                  ·
                    refine ⟨545570114518201065238681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11638829109721622725091861 545570114518201065238681)
                    ·
                      rfl

theorem cell23_3187482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 1, 6].length) (baseStart_3187482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187482 prefixEnd_3187482 := by exact prefixLift 3187482
  have htrace : WordTrace (prefixWord ++ tailWord_3187482) baseStart_3187482 baseEnd_3187482 := by
    simpa [prefixWord, tailWord_3187482, baseEnd_3187482] using wordTrace_append hprefix tailTrace_3187482
  have hstable : (prefixWord ++ tailWord_3187482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187482).length < 2 ^ (prefixWord ++ tailWord_3187482).sum := by decide
  have hdescent : baseEnd_3187482 < baseStart_3187482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187525 : List Nat := [1, 3, 1, 1, 1, 2, 2, 3, 2, 7]
def baseStart_3187525 : Nat := 118140960795 + 3187525 * 2 ^ 59
def prefixEnd_3187525 : Nat := 4983230072969 + 3 ^ 40 * 3187525 * 2
def baseEnd_3187525 : Nat := 545577474407582175826115

theorem tailTrace_3187525 : CollatzResearch.WordTrace tailWord_3187525 prefixEnd_3187525 545577474407582175826115 := by
  unfold tailWord_3187525
  simp only [CollatzResearch.WordTrace]
  refine ⟨116258587777148785774332029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77505725184765857182888019 116258587777148785774332029)
  ·
    refine ⟨43596970416430794665374511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116258587777148785774332029 43596970416430794665374511)
    ·
      refine ⟨65395455624646191998061767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43596970416430794665374511 65395455624646191998061767)
      ·
        refine ⟨98093183436969287997092651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65395455624646191998061767 98093183436969287997092651)
        ·
          refine ⟨147139775155453931995638977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98093183436969287997092651 147139775155453931995638977)
          ·
            refine ⟨110354831366590448996729233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147139775155453931995638977 110354831366590448996729233)
            ·
              refine ⟨82766123524942836747546925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110354831366590448996729233 82766123524942836747546925)
              ·
                refine ⟨31037296321853563780330097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82766123524942836747546925 31037296321853563780330097)
                ·
                  refine ⟨23277972241390172835247573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31037296321853563780330097 23277972241390172835247573)
                  ·
                    refine ⟨545577474407582175826115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23277972241390172835247573 545577474407582175826115)
                    ·
                      rfl

theorem cell23_3187525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_3187525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187525 prefixEnd_3187525 := by exact prefixLift 3187525
  have htrace : WordTrace (prefixWord ++ tailWord_3187525) baseStart_3187525 baseEnd_3187525 := by
    simpa [prefixWord, tailWord_3187525, baseEnd_3187525] using wordTrace_append hprefix tailTrace_3187525
  have hstable : (prefixWord ++ tailWord_3187525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187525).length < 2 ^ (prefixWord ++ tailWord_3187525).sum := by decide
  have hdescent : baseEnd_3187525 < baseStart_3187525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187533 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_3187533 : Nat := 118140960795 + 3187533 * 2 ^ 59
def prefixEnd_3187533 : Nat := 4983230072969 + 3 ^ 40 * 3187533 * 2
def baseEnd_3187533 : Nat := 545578843689327498726103

theorem tailTrace_3187533 : CollatzResearch.WordTrace tailWord_3187533 prefixEnd_3187533 545578843689327498726103 := by
  unfold tailWord_3187533
  simp only [CollatzResearch.WordTrace]
  refine ⟨116258879561119803140623253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77505919707413202093748835 116258879561119803140623253)
  ·
    refine ⟨5449634979427490772216715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116258879561119803140623253 5449634979427490772216715)
    ·
      refine ⟨8174452469141236158325073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5449634979427490772216715 8174452469141236158325073)
      ·
        refine ⟨6130839351855927118743805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8174452469141236158325073 6130839351855927118743805)
        ·
          refine ⟨2299064756945972669528927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6130839351855927118743805 2299064756945972669528927)
          ·
            refine ⟨3448597135418959004293391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299064756945972669528927 3448597135418959004293391)
            ·
              refine ⟨5172895703128438506440087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448597135418959004293391 5172895703128438506440087)
              ·
                refine ⟨7759343554692657759660131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5172895703128438506440087 7759343554692657759660131)
                ·
                  refine ⟨11639015332038986639490197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759343554692657759660131 11639015332038986639490197)
                  ·
                    refine ⟨545578843689327498726103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11639015332038986639490197 545578843689327498726103)
                    ·
                      rfl

theorem cell23_3187533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_3187533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187533 prefixEnd_3187533 := by exact prefixLift 3187533
  have htrace : WordTrace (prefixWord ++ tailWord_3187533) baseStart_3187533 baseEnd_3187533 := by
    simpa [prefixWord, tailWord_3187533, baseEnd_3187533] using wordTrace_append hprefix tailTrace_3187533
  have hstable : (prefixWord ++ tailWord_3187533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187533).length < 2 ^ (prefixWord ++ tailWord_3187533).sum := by decide
  have hdescent : baseEnd_3187533 < baseStart_3187533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187535 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 5]
def baseStart_3187535 : Nat := 118140960795 + 3187535 * 2 ^ 59
def prefixEnd_3187535 : Nat := 4983230072969 + 3 ^ 40 * 3187535 * 2
def baseEnd_3187535 : Nat := 1636737558029291488353299

theorem tailTrace_3187535 : CollatzResearch.WordTrace tailWord_3187535 prefixEnd_3187535 1636737558029291488353299 := by
  unfold tailWord_3187535
  simp only [CollatzResearch.WordTrace]
  refine ⟨116258952507112557482196059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77505968338075038321464039 116258952507112557482196059)
  ·
    refine ⟨174388428760668836223294089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116258952507112557482196059 174388428760668836223294089)
    ·
      refine ⟨130791321570501627167470567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174388428760668836223294089 130791321570501627167470567)
      ·
        refine ⟨196186982355752440751205851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130791321570501627167470567 196186982355752440751205851)
        ·
          refine ⟨294280473533628661126808777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196186982355752440751205851 294280473533628661126808777)
          ·
            refine ⟨220710355150221495845106583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294280473533628661126808777 220710355150221495845106583)
            ·
              refine ⟨331065532725332243767659875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220710355150221495845106583 331065532725332243767659875)
              ·
                refine ⟨496598299087998365651489813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331065532725332243767659875 496598299087998365651489813)
                ·
                  refine ⟨23278045269749923389913585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 496598299087998365651489813 23278045269749923389913585)
                  ·
                    refine ⟨17458533952312442542435189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23278045269749923389913585 17458533952312442542435189)
                    ·
                      refine ⟨1636737558029291488353299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17458533952312442542435189 1636737558029291488353299)
                      ·
                        rfl

theorem cell23_3187535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 5].length) (baseStart_3187535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187535 prefixEnd_3187535 := by exact prefixLift 3187535
  have htrace : WordTrace (prefixWord ++ tailWord_3187535) baseStart_3187535 baseEnd_3187535 := by
    simpa [prefixWord, tailWord_3187535, baseEnd_3187535] using wordTrace_append hprefix tailTrace_3187535
  have hstable : (prefixWord ++ tailWord_3187535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187535).length < 2 ^ (prefixWord ++ tailWord_3187535).sum := by decide
  have hdescent : baseEnd_3187535 < baseStart_3187535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187539 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 3]
def baseStart_3187539 : Nat := 118140960795 + 3187539 * 2 ^ 59
def prefixEnd_3187539 : Nat := 4983230072969 + 3 ^ 40 * 3187539 * 2
def baseEnd_3187539 : Nat := 1636739611951909472703281

theorem tailTrace_3187539 : CollatzResearch.WordTrace tailWord_3187539 prefixEnd_3187539 1636739611951909472703281 := by
  unfold tailWord_3187539
  simp only [CollatzResearch.WordTrace]
  refine ⟨116259098399098066165341671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77506065599398710776894447 116259098399098066165341671)
  ·
    refine ⟨174388647598647099248012507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116259098399098066165341671 174388647598647099248012507)
    ·
      refine ⟨261582971397970648872018761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174388647598647099248012507 261582971397970648872018761)
      ·
        refine ⟨196187228548477986654014071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261582971397970648872018761 196187228548477986654014071)
        ·
          refine ⟨294280842822716979981021107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196187228548477986654014071 294280842822716979981021107)
          ·
            refine ⟨441421264234075469971531661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294280842822716979981021107 441421264234075469971531661)
            ·
              refine ⟨165532974087778301239324373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 441421264234075469971531661 165532974087778301239324373)
              ·
                refine ⟨3879679080182303935296665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 165532974087778301239324373 3879679080182303935296665)
                ·
                  refine ⟨2909759310136727951472499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3879679080182303935296665 2909759310136727951472499)
                  ·
                    refine ⟨4364638965205091927208749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2909759310136727951472499 4364638965205091927208749)
                    ·
                      refine ⟨1636739611951909472703281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4364638965205091927208749 1636739611951909472703281)
                      ·
                        rfl

theorem cell23_3187539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 2, 1, 3].length) (baseStart_3187539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187539 prefixEnd_3187539 := by exact prefixLift 3187539
  have htrace : WordTrace (prefixWord ++ tailWord_3187539) baseStart_3187539 baseEnd_3187539 := by
    simpa [prefixWord, tailWord_3187539, baseEnd_3187539] using wordTrace_append hprefix tailTrace_3187539
  have hstable : (prefixWord ++ tailWord_3187539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187539).length < 2 ^ (prefixWord ++ tailWord_3187539).sum := by decide
  have hdescent : baseEnd_3187539 < baseStart_3187539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187639 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 2, 5, 2]
def baseStart_3187639 : Nat := 118140960795 + 3187639 * 2 ^ 59
def prefixEnd_3187639 : Nat := 4983230072969 + 3 ^ 40 * 3187639 * 2
def baseEnd_3187639 : Nat := 1636790960017359081452821

theorem tailTrace_3187639 : CollatzResearch.WordTrace tailWord_3187639 prefixEnd_3187639 1636790960017359081452821 := by
  unfold tailWord_3187639
  simp only [CollatzResearch.WordTrace]
  refine ⟨116262745698735783243981971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77508497132490522162654647 116262745698735783243981971)
  ·
    refine ⟨174394118548103674865972957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116262745698735783243981971 174394118548103674865972957)
    ·
      refine ⟨65397794455538878074739859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174394118548103674865972957 65397794455538878074739859)
      ·
        refine ⟨98096691683308317112109789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65397794455538878074739859 98096691683308317112109789)
        ·
          refine ⟨36786259381240618917041171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98096691683308317112109789 36786259381240618917041171)
          ·
            refine ⟨55179389071860928375561757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36786259381240618917041171 55179389071860928375561757)
            ·
              refine ⟨20692270901947848140835659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55179389071860928375561757 20692270901947848140835659)
              ·
                refine ⟨31038406352921772211253489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20692270901947848140835659 31038406352921772211253489)
                ·
                  refine ⟨23278804764691329158440117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31038406352921772211253489 23278804764691329158440117)
                  ·
                    refine ⟨2182387946689812108603761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23278804764691329158440117 2182387946689812108603761)
                    ·
                      refine ⟨1636790960017359081452821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182387946689812108603761 1636790960017359081452821)
                      ·
                        rfl

theorem cell23_3187639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_3187639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187639 prefixEnd_3187639 := by exact prefixLift 3187639
  have htrace : WordTrace (prefixWord ++ tailWord_3187639) baseStart_3187639 baseEnd_3187639 := by
    simpa [prefixWord, tailWord_3187639, baseEnd_3187639] using wordTrace_append hprefix tailTrace_3187639
  have hstable : (prefixWord ++ tailWord_3187639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187639).length < 2 ^ (prefixWord ++ tailWord_3187639).sum := by decide
  have hdescent : baseEnd_3187639 < baseStart_3187639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187642 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5]
def baseStart_3187642 : Nat := 118140960795 + 3187642 * 2 ^ 59
def prefixEnd_3187642 : Nat := 4983230072969 + 3 ^ 40 * 3187642 * 2
def baseEnd_3187642 : Nat := 1636792500459322569715307

theorem tailTrace_3187642 : CollatzResearch.WordTrace tailWord_3187642 prefixEnd_3187642 1636792500459322569715307 := by
  unfold tailWord_3187642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29065713779431228689085295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77508570078483276504227453 29065713779431228689085295)
  ·
    refine ⟨43598570669146843033627943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29065713779431228689085295 43598570669146843033627943)
    ·
      refine ⟨65397856003720264550441915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43598570669146843033627943 65397856003720264550441915)
      ·
        refine ⟨98096784005580396825662873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65397856003720264550441915 98096784005580396825662873)
        ·
          refine ⟨73572588004185297619247155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98096784005580396825662873 73572588004185297619247155)
          ·
            refine ⟨110358882006277946428870733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73572588004185297619247155 110358882006277946428870733)
            ·
              refine ⟨41384580752354229910826525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110358882006277946428870733 41384580752354229910826525)
              ·
                refine ⟨15519217782132836216559947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41384580752354229910826525 15519217782132836216559947)
                ·
                  refine ⟨23278826673199254324839921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15519217782132836216559947 23278826673199254324839921)
                  ·
                    refine ⟨17459120004899440743629941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23278826673199254324839921 17459120004899440743629941)
                    ·
                      refine ⟨1636792500459322569715307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17459120004899440743629941 1636792500459322569715307)
                      ·
                        rfl

theorem cell23_3187642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_3187642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187642 prefixEnd_3187642 := by exact prefixLift 3187642
  have htrace : WordTrace (prefixWord ++ tailWord_3187642) baseStart_3187642 baseEnd_3187642 := by
    simpa [prefixWord, tailWord_3187642, baseEnd_3187642] using wordTrace_append hprefix tailTrace_3187642
  have hstable : (prefixWord ++ tailWord_3187642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187642).length < 2 ^ (prefixWord ++ tailWord_3187642).sum := by decide
  have hdescent : baseEnd_3187642 < baseStart_3187642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187666 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 2, 5]
def baseStart_3187666 : Nat := 118140960795 + 3187666 * 2 ^ 59
def prefixEnd_3187666 : Nat := 4983230072969 + 3 ^ 40 * 3187666 * 2
def baseEnd_3187666 : Nat := 545601607998343491938399

theorem tailTrace_3187666 : CollatzResearch.WordTrace tailWord_3187666 prefixEnd_3187666 545601607998343491938399 := by
  unfold tailWord_3187666
  simp only [CollatzResearch.WordTrace]
  refine ⟨29065932617409491713803713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77509153646425311236809901 29065932617409491713803713)
  ·
    refine ⟨21799449463057118785352785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29065932617409491713803713 21799449463057118785352785)
    ·
      refine ⟨16349587097292839089014589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21799449463057118785352785 16349587097292839089014589)
      ·
        refine ⟨6131095161484814658380471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16349587097292839089014589 6131095161484814658380471)
        ·
          refine ⟨9196642742227221987570707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131095161484814658380471 9196642742227221987570707)
          ·
            refine ⟨13794964113340832981356061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9196642742227221987570707 13794964113340832981356061)
            ·
              refine ⟨5173111542502812368008523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13794964113340832981356061 5173111542502812368008523)
              ·
                refine ⟨7759667313754218552012785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173111542502812368008523 7759667313754218552012785)
                ·
                  refine ⟨5819750485315663914009589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7759667313754218552012785 5819750485315663914009589)
                  ·
                    refine ⟨545601607998343491938399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5819750485315663914009589 545601607998343491938399)
                    ·
                      rfl

theorem cell23_3187666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_3187666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187666 prefixEnd_3187666 := by exact prefixLift 3187666
  have htrace : WordTrace (prefixWord ++ tailWord_3187666) baseStart_3187666 baseEnd_3187666 := by
    simpa [prefixWord, tailWord_3187666, baseEnd_3187666] using wordTrace_append hprefix tailTrace_3187666
  have hstable : (prefixWord ++ tailWord_3187666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187666).length < 2 ^ (prefixWord ++ tailWord_3187666).sum := by decide
  have hdescent : baseEnd_3187666 < baseStart_3187666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187719 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 3]
def baseStart_3187719 : Nat := 118140960795 + 3187719 * 2 ^ 59
def prefixEnd_3187719 : Nat := 4983230072969 + 3 ^ 40 * 3187719 * 2
def baseEnd_3187719 : Nat := 1636832038469718768452453

theorem tailTrace_3187719 : CollatzResearch.WordTrace tailWord_3187719 prefixEnd_3187719 1636832038469718768452453 := by
  unfold tailWord_3187719
  simp only [CollatzResearch.WordTrace]
  refine ⟨116265663538445956906894211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77510442358963971271262807 116265663538445956906894211)
  ·
    refine ⟨174398495307668935360341317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116265663538445956906894211 174398495307668935360341317)
    ·
      refine ⟨32699717870187925380063997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174398495307668935360341317 32699717870187925380063997)
      ·
        refine ⟨12262394201320472017523999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32699717870187925380063997 12262394201320472017523999)
        ·
          refine ⟨18393591301980708026285999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12262394201320472017523999 18393591301980708026285999)
          ·
            refine ⟨27590386952971062039428999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18393591301980708026285999 27590386952971062039428999)
            ·
              refine ⟨41385580429456593059143499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27590386952971062039428999 41385580429456593059143499)
              ·
                refine ⟨62078370644184889588715249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41385580429456593059143499 62078370644184889588715249)
                ·
                  refine ⟨46558777983138667191536437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62078370644184889588715249 46558777983138667191536437)
                  ·
                    refine ⟨4364885435919250049206541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46558777983138667191536437 4364885435919250049206541)
                    ·
                      refine ⟨1636832038469718768452453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4364885435919250049206541 1636832038469718768452453)
                      ·
                        rfl

theorem cell23_3187719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_3187719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187719 prefixEnd_3187719 := by exact prefixLift 3187719
  have htrace : WordTrace (prefixWord ++ tailWord_3187719) baseStart_3187719 baseEnd_3187719 := by
    simpa [prefixWord, tailWord_3187719, baseEnd_3187719] using wordTrace_append hprefix tailTrace_3187719
  have hstable : (prefixWord ++ tailWord_3187719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187719).length < 2 ^ (prefixWord ++ tailWord_3187719).sum := by decide
  have hdescent : baseEnd_3187719 < baseStart_3187719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187773 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_3187773 : Nat := 118140960795 + 3187773 * 2 ^ 59
def prefixEnd_3187773 : Nat := 4983230072969 + 3 ^ 40 * 3187773 * 2
def baseEnd_3187773 : Nat := 545619922141687185725735

theorem tailTrace_3187773 : CollatzResearch.WordTrace tailWord_3187773 prefixEnd_3187773 545619922141687185725735 := by
  unfold tailWord_3187773
  simp only [CollatzResearch.WordTrace]
  refine ⟨116267633080250324129359973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77511755386833549419573315 116267633080250324129359973)
  ·
    refine ⟨21800181202546935774254995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116267633080250324129359973 21800181202546935774254995)
    ·
      refine ⟨32700271803820403661382493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21800181202546935774254995 32700271803820403661382493)
      ·
        refine ⟨12262601926432651373018435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32700271803820403661382493 12262601926432651373018435)
        ·
          refine ⟨18393902889648977059527653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12262601926432651373018435 18393902889648977059527653)
          ·
            refine ⟨3448856791809183198661435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18393902889648977059527653 3448856791809183198661435)
            ·
              refine ⟨5173285187713774797992153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3448856791809183198661435 5173285187713774797992153)
              ·
                refine ⟨3879963890785331098494115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5173285187713774797992153 3879963890785331098494115)
                ·
                  refine ⟨5819945836177996647741173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3879963890785331098494115 5819945836177996647741173)
                  ·
                    refine ⟨545619922141687185725735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5819945836177996647741173 545619922141687185725735)
                    ·
                      rfl

theorem cell23_3187773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_3187773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187773 prefixEnd_3187773 := by exact prefixLift 3187773
  have htrace : WordTrace (prefixWord ++ tailWord_3187773) baseStart_3187773 baseEnd_3187773 := by
    simpa [prefixWord, tailWord_3187773, baseEnd_3187773] using wordTrace_append hprefix tailTrace_3187773
  have hstable : (prefixWord ++ tailWord_3187773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187773).length < 2 ^ (prefixWord ++ tailWord_3187773).sum := by decide
  have hdescent : baseEnd_3187773 < baseStart_3187773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187796 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 1, 1, 5]
def baseStart_3187796 : Nat := 118140960795 + 3187796 * 2 ^ 59
def prefixEnd_3187796 : Nat := 4983230072969 + 3 ^ 40 * 3187796 * 2
def baseEnd_3187796 : Nat := 1636871576480114967189599

theorem tailTrace_3187796 : CollatzResearch.WordTrace tailWord_3187796 prefixEnd_3187796 1636871576480114967189599 := by
  unfold tailWord_3187796
  simp only [CollatzResearch.WordTrace]
  refine ⟨58134235979583499528723621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77512314639444666038298161 58134235979583499528723621)
  ·
    refine ⟨10900169246171906161635679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58134235979583499528723621 10900169246171906161635679)
    ·
      refine ⟨16350253869257859242453519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10900169246171906161635679 16350253869257859242453519)
      ·
        refine ⟨24525380803886788863680279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16350253869257859242453519 24525380803886788863680279)
        ·
          refine ⟨36788071205830183295520419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24525380803886788863680279 36788071205830183295520419)
          ·
            refine ⟨55182106808745274943280629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36788071205830183295520419 55182106808745274943280629)
            ·
              refine ⟨5173322513319869525932559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55182106808745274943280629 5173322513319869525932559)
              ·
                refine ⟨7759983769979804288898839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5173322513319869525932559 7759983769979804288898839)
                ·
                  refine ⟨11639975654969706433348259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7759983769979804288898839 11639975654969706433348259)
                  ·
                    refine ⟨17459963482454559650022389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11639975654969706433348259 17459963482454559650022389)
                    ·
                      refine ⟨1636871576480114967189599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17459963482454559650022389 1636871576480114967189599)
                      ·
                        rfl

theorem cell23_3187796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_3187796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187796 prefixEnd_3187796 := by exact prefixLift 3187796
  have htrace : WordTrace (prefixWord ++ tailWord_3187796) baseStart_3187796 baseEnd_3187796 := by
    simpa [prefixWord, tailWord_3187796, baseEnd_3187796] using wordTrace_append hprefix tailTrace_3187796
  have hstable : (prefixWord ++ tailWord_3187796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187796).length < 2 ^ (prefixWord ++ tailWord_3187796).sum := by decide
  have hdescent : baseEnd_3187796 < baseStart_3187796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187859 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 2, 6]
def baseStart_3187859 : Nat := 118140960795 + 3187859 * 2 ^ 59
def prefixEnd_3187859 : Nat := 4983230072969 + 3 ^ 40 * 3187859 * 2
def baseEnd_3187859 : Nat := 545634641920449406900603

theorem tailTrace_3187859 : CollatzResearch.WordTrace tailWord_3187859 prefixEnd_3187859 545634641920449406900603 := by
  unfold tailWord_3187859
  simp only [CollatzResearch.WordTrace]
  refine ⟨116270769757938760816990631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77513846505292507211327087 116270769757938760816990631)
  ·
    refine ⟨174406154636908141225485947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116270769757938760816990631 174406154636908141225485947)
    ·
      refine ⟨261609231955362211838228921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174406154636908141225485947 261609231955362211838228921)
      ·
        refine ⟨196206923966521658878671691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261609231955362211838228921 196206923966521658878671691)
        ·
          refine ⟨294310385949782488318007537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196206923966521658878671691 294310385949782488318007537)
          ·
            refine ⟨220732789462336866238505653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294310385949782488318007537 220732789462336866238505653)
            ·
              refine ⟨20693699012094081209859905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 220732789462336866238505653 20693699012094081209859905)
              ·
                refine ⟨15520274259070560907394929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20693699012094081209859905 15520274259070560907394929)
                ·
                  refine ⟨11640205694302920680546197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15520274259070560907394929 11640205694302920680546197)
                  ·
                    refine ⟨545634641920449406900603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11640205694302920680546197 545634641920449406900603)
                    ·
                      rfl

theorem cell23_3187859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 6].length) (baseStart_3187859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187859 prefixEnd_3187859 := by exact prefixLift 3187859
  have htrace : WordTrace (prefixWord ++ tailWord_3187859) baseStart_3187859 baseEnd_3187859 := by
    simpa [prefixWord, tailWord_3187859, baseEnd_3187859] using wordTrace_append hprefix tailTrace_3187859
  have hstable : (prefixWord ++ tailWord_3187859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187859).length < 2 ^ (prefixWord ++ tailWord_3187859).sum := by decide
  have hdescent : baseEnd_3187859 < baseStart_3187859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187876 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 2, 6]
def baseStart_3187876 : Nat := 118140960795 + 3187876 * 2 ^ 59
def prefixEnd_3187876 : Nat := 4983230072969 + 3 ^ 40 * 3187876 * 2
def baseEnd_3187876 : Nat := 545637551644158218063077

theorem tailTrace_3187876 : CollatzResearch.WordTrace tailWord_3187876 prefixEnd_3187876 545637551644158218063077 := by
  unfold tailWord_3187876
  simp only [CollatzResearch.WordTrace]
  refine ⟨58135694899438586360179741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77514259865918115146906321 58135694899438586360179741)
  ·
    refine ⟨21800885587289469885067403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58135694899438586360179741 21800885587289469885067403)
    ·
      refine ⟨32701328380934204827601105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21800885587289469885067403 32701328380934204827601105)
      ·
        refine ⟨24525996285700653620700829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32701328380934204827601105 24525996285700653620700829)
        ·
          refine ⟨9197248607137745107762811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24525996285700653620700829 9197248607137745107762811)
          ·
            refine ⟨13795872910706617661644217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9197248607137745107762811 13795872910706617661644217)
            ·
              refine ⟨10346904683029963246233163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13795872910706617661644217 10346904683029963246233163)
              ·
                refine ⟨15520357024544944869349745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10346904683029963246233163 15520357024544944869349745)
                ·
                  refine ⟨11640267768408708652012309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15520357024544944869349745 11640267768408708652012309)
                  ·
                    refine ⟨545637551644158218063077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11640267768408708652012309 545637551644158218063077)
                    ·
                      rfl

theorem cell23_3187876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 2, 6].length) (baseStart_3187876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187876 prefixEnd_3187876 := by exact prefixLift 3187876
  have htrace : WordTrace (prefixWord ++ tailWord_3187876) baseStart_3187876 baseEnd_3187876 := by
    simpa [prefixWord, tailWord_3187876, baseEnd_3187876] using wordTrace_append hprefix tailTrace_3187876
  have hstable : (prefixWord ++ tailWord_3187876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187876).length < 2 ^ (prefixWord ++ tailWord_3187876).sum := by decide
  have hdescent : baseEnd_3187876 < baseStart_3187876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187900 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_3187900 : Nat := 118140960795 + 3187900 * 2 ^ 59
def prefixEnd_3187900 : Nat := 4983230072969 + 3 ^ 40 * 3187900 * 2
def baseEnd_3187900 : Nat := 1636924978468182560289121

theorem tailTrace_3187900 : CollatzResearch.WordTrace tailWord_3187900 prefixEnd_3187900 1636924978468182560289121 := by
  unfold tailWord_3187900
  simp only [CollatzResearch.WordTrace]
  refine ⟨58136132575395112409616577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77514843433860149879488769 58136132575395112409616577)
  ·
    refine ⟨43602099431546334307212433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58136132575395112409616577 43602099431546334307212433)
    ·
      refine ⟨32701574573659750730409325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43602099431546334307212433 32701574573659750730409325)
      ·
        refine ⟨12263090465122406523903497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32701574573659750730409325 12263090465122406523903497)
        ·
          refine ⟨9197317848841804892927623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12263090465122406523903497 9197317848841804892927623)
          ·
            refine ⟨13795976773262707339391435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9197317848841804892927623 13795976773262707339391435)
            ·
              refine ⟨20693965159894061009087153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13795976773262707339391435 20693965159894061009087153)
              ·
                refine ⟨15520473869920545756815365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20693965159894061009087153 15520473869920545756815365)
                ·
                  refine ⟨2910088850610102329402881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15520473869920545756815365 2910088850610102329402881)
                  ·
                    refine ⟨2182566637957576747052161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910088850610102329402881 2182566637957576747052161)
                    ·
                      refine ⟨1636924978468182560289121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182566637957576747052161 1636924978468182560289121)
                      ·
                        rfl

theorem cell23_3187900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_3187900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187900 prefixEnd_3187900 := by exact prefixLift 3187900
  have htrace : WordTrace (prefixWord ++ tailWord_3187900) baseStart_3187900 baseEnd_3187900 := by
    simpa [prefixWord, tailWord_3187900, baseEnd_3187900] using wordTrace_append hprefix tailTrace_3187900
  have hstable : (prefixWord ++ tailWord_3187900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187900).length < 2 ^ (prefixWord ++ tailWord_3187900).sum := by decide
  have hdescent : baseEnd_3187900 < baseStart_3187900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187919 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 3, 7]
def baseStart_3187919 : Nat := 118140960795 + 3187919 * 2 ^ 59
def prefixEnd_3187919 : Nat := 4983230072969 + 3 ^ 40 * 3187919 * 2
def baseEnd_3187919 : Nat := 545644911533539328650511

theorem tailTrace_3187919 : CollatzResearch.WordTrace tailWord_3187919 prefixEnd_3187919 545644911533539328650511 := by
  unfold tailWord_3187919
  simp only [CollatzResearch.WordTrace]
  refine ⟨116272958137721391064174811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77515305425147594042783207 116272958137721391064174811)
  ·
    refine ⟨174409437206582086596262217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116272958137721391064174811 174409437206582086596262217)
    ·
      refine ⟨130807077904936564947196663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174409437206582086596262217 130807077904936564947196663)
      ·
        refine ⟨196210616857404847420794995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130807077904936564947196663 196210616857404847420794995)
        ·
          refine ⟨294315925286107271131192493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196210616857404847420794995 294315925286107271131192493)
          ·
            refine ⟨110368471982290226674197185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294315925286107271131192493 110368471982290226674197185)
            ·
              refine ⟨82776353986717670005647889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110368471982290226674197185 82776353986717670005647889)
              ·
                refine ⟨62082265490038252504235917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82776353986717670005647889 62082265490038252504235917)
                ·
                  refine ⟨23280849558764344689088469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62082265490038252504235917 23280849558764344689088469)
                  ·
                    refine ⟨545644911533539328650511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23280849558764344689088469 545644911533539328650511)
                    ·
                      rfl

theorem cell23_3187919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 7].length) (baseStart_3187919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187919 prefixEnd_3187919 := by exact prefixLift 3187919
  have htrace : WordTrace (prefixWord ++ tailWord_3187919) baseStart_3187919 baseEnd_3187919 := by
    simpa [prefixWord, tailWord_3187919, baseEnd_3187919] using wordTrace_append hprefix tailTrace_3187919
  have hstable : (prefixWord ++ tailWord_3187919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187919).length < 2 ^ (prefixWord ++ tailWord_3187919).sum := by decide
  have hdescent : baseEnd_3187919 < baseStart_3187919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3187973 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 2, 4, 2]
def baseStart_3187973 : Nat := 118140960795 + 3187973 * 2 ^ 59
def prefixEnd_3187973 : Nat := 4983230072969 + 3 ^ 40 * 3187973 * 2
def baseEnd_3187973 : Nat := 1636962462555960774676285

theorem tailTrace_3187973 : CollatzResearch.WordTrace tailWord_3187973 prefixEnd_3187973 1636962462555960774676285 := by
  unfold tailWord_3187973
  simp only [CollatzResearch.WordTrace]
  refine ⟨116274927679525758286640573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77516618453017172191093715 116274927679525758286640573)
  ·
    refine ⟨43603097879822159357490215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116274927679525758286640573 43603097879822159357490215)
    ·
      refine ⟨65404646819733239036235323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43603097879822159357490215 65404646819733239036235323)
      ·
        refine ⟨98106970229599858554352985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65404646819733239036235323 98106970229599858554352985)
        ·
          refine ⟨73580227672199893915764739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98106970229599858554352985 73580227672199893915764739)
          ·
            refine ⟨110370341508299840873647109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73580227672199893915764739 110370341508299840873647109)
            ·
              refine ⟨20694439032806220163808833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110370341508299840873647109 20694439032806220163808833)
              ·
                refine ⟨15520829274604665122856625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20694439032806220163808833 15520829274604665122856625)
                ·
                  refine ⟨11640621955953498842142469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15520829274604665122856625 11640621955953498842142469)
                  ·
                    refine ⟨2182616616741281032901713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11640621955953498842142469 2182616616741281032901713)
                    ·
                      refine ⟨1636962462555960774676285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182616616741281032901713 1636962462555960774676285)
                      ·
                        rfl

theorem cell23_3187973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_3187973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3187973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3187973 prefixEnd_3187973 := by exact prefixLift 3187973
  have htrace : WordTrace (prefixWord ++ tailWord_3187973) baseStart_3187973 baseEnd_3187973 := by
    simpa [prefixWord, tailWord_3187973, baseEnd_3187973] using wordTrace_append hprefix tailTrace_3187973
  have hstable : (prefixWord ++ tailWord_3187973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3187973).length < 2 ^ (prefixWord ++ tailWord_3187973).sum := by decide
  have hdescent : baseEnd_3187973 < baseStart_3187973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3187973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188000 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 3, 4]
def baseStart_3188000 : Nat := 118140960795 + 3188000 * 2 ^ 59
def prefixEnd_3188000 : Nat := 4983230072969 + 3 ^ 40 * 3188000 * 2
def baseEnd_3188000 : Nat := 545658775511210723012887

theorem tailTrace_3188000 : CollatzResearch.WordTrace tailWord_3188000 prefixEnd_3188000 545658775511210723012887 := by
  unfold tailWord_3188000
  simp only [CollatzResearch.WordTrace]
  refine ⟨58137956225213970948936727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77517274966951961265248969 58137956225213970948936727)
  ·
    refine ⟨87206934337820956423405091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58137956225213970948936727 87206934337820956423405091)
    ·
      refine ⟨130810401506731434635107637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87206934337820956423405091 130810401506731434635107637)
      ·
        refine ⟨12263475141256071997041341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130810401506731434635107637 12263475141256071997041341)
        ·
          refine ⟨4598803177971026998890503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12263475141256071997041341 4598803177971026998890503)
          ·
            refine ⟨6898204766956540498335755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4598803177971026998890503 6898204766956540498335755)
            ·
              refine ⟨10347307150434810747503633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6898204766956540498335755 10347307150434810747503633)
              ·
                refine ⟨7760480362826108060627725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10347307150434810747503633 7760480362826108060627725)
                ·
                  refine ⟨2910180136059790522735397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7760480362826108060627725 2910180136059790522735397)
                  ·
                    refine ⟨545658775511210723012887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2910180136059790522735397 545658775511210723012887)
                    ·
                      rfl

theorem cell23_3188000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 3, 4].length) (baseStart_3188000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188000 prefixEnd_3188000 := by exact prefixLift 3188000
  have htrace : WordTrace (prefixWord ++ tailWord_3188000) baseStart_3188000 baseEnd_3188000 := by
    simpa [prefixWord, tailWord_3188000, baseEnd_3188000] using wordTrace_append hprefix tailTrace_3188000
  have hstable : (prefixWord ++ tailWord_3188000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188000).length < 2 ^ (prefixWord ++ tailWord_3188000).sum := by decide
  have hdescent : baseEnd_3188000 < baseStart_3188000 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188010 : List Nat := [3, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3188010 : Nat := 118140960795 + 3188010 * 2 ^ 59
def prefixEnd_3188010 : Nat := 4983230072969 + 3 ^ 40 * 3188010 * 2
def baseEnd_3188010 : Nat := 1636981461340177129913615

theorem tailTrace_3188010 : CollatzResearch.WordTrace tailWord_3188010 prefixEnd_3188010 1636981461340177129913615 := by
  unfold tailWord_3188010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29069069295097928401434371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77517518120261142403824989 29069069295097928401434371)
  ·
    refine ⟨43603603942646892602151557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29069069295097928401434371 43603603942646892602151557)
    ·
      refine ⟨8175675739246292362903417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43603603942646892602151557 8175675739246292362903417)
      ·
        refine ⟨6131756804434719272177563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8175675739246292362903417 6131756804434719272177563)
        ·
          refine ⟨9197635206652078908266345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131756804434719272177563 9197635206652078908266345)
          ·
            refine ⟨6898226404989059181199759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9197635206652078908266345 6898226404989059181199759)
            ·
              refine ⟨10347339607483588771799639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6898226404989059181199759 10347339607483588771799639)
              ·
                refine ⟨15521009411225383157699459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10347339607483588771799639 15521009411225383157699459)
                ·
                  refine ⟨23281514116838074736549189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15521009411225383157699459 23281514116838074736549189)
                  ·
                    refine ⟨4365283896907139013102973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23281514116838074736549189 4365283896907139013102973)
                    ·
                      refine ⟨1636981461340177129913615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4365283896907139013102973 1636981461340177129913615)
                      ·
                        rfl

theorem cell23_3188010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3188010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188010 prefixEnd_3188010 := by exact prefixLift 3188010
  have htrace : WordTrace (prefixWord ++ tailWord_3188010) baseStart_3188010 baseEnd_3188010 := by
    simpa [prefixWord, tailWord_3188010, baseEnd_3188010] using wordTrace_append hprefix tailTrace_3188010
  have hstable : (prefixWord ++ tailWord_3188010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188010).length < 2 ^ (prefixWord ++ tailWord_3188010).sum := by decide
  have hdescent : baseEnd_3188010 < baseStart_3188010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188017 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 1, 4]
def baseStart_3188017 : Nat := 118140960795 + 3188017 * 2 ^ 59
def prefixEnd_3188017 : Nat := 4983230072969 + 3 ^ 40 * 3188017 * 2
def baseEnd_3188017 : Nat := 545661685234919534175361

theorem tailTrace_3188017 : CollatzResearch.WordTrace tailWord_3188017 prefixEnd_3188017 545661685234919534175361 := by
  unfold tailWord_3188017
  simp only [CollatzResearch.WordTrace]
  refine ⟨116276532491366353801242305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77517688327577569200828203 116276532491366353801242305)
  ·
    refine ⟨87207399368524765350931729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116276532491366353801242305 87207399368524765350931729)
    ·
      refine ⟨65405549526393574013198797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87207399368524765350931729 65405549526393574013198797)
      ·
        refine ⟨24527081072397590254949549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65405549526393574013198797 24527081072397590254949549)
        ·
          refine ⟨9197655402149096345606081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24527081072397590254949549 9197655402149096345606081)
          ·
            refine ⟨6898241551611822259204561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9197655402149096345606081 6898241551611822259204561)
            ·
              refine ⟨5173681163708866694403421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6898241551611822259204561 5173681163708866694403421)
              ·
                refine ⟨1940130436390825010401283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5173681163708866694403421 1940130436390825010401283)
                ·
                  refine ⟨2910195654586237515601925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940130436390825010401283 2910195654586237515601925)
                  ·
                    refine ⟨545661685234919534175361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2910195654586237515601925 545661685234919534175361)
                    ·
                      rfl

theorem cell23_3188017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 1, 4].length) (baseStart_3188017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188017 prefixEnd_3188017 := by exact prefixLift 3188017
  have htrace : WordTrace (prefixWord ++ tailWord_3188017) baseStart_3188017 baseEnd_3188017 := by
    simpa [prefixWord, tailWord_3188017, baseEnd_3188017] using wordTrace_append hprefix tailTrace_3188017
  have hstable : (prefixWord ++ tailWord_3188017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188017).length < 2 ^ (prefixWord ++ tailWord_3188017).sum := by decide
  have hdescent : baseEnd_3188017 < baseStart_3188017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188033 : List Nat := [1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3188033 : Nat := 118140960795 + 3188033 * 2 ^ 59
def prefixEnd_3188033 : Nat := 4983230072969 + 3 ^ 40 * 3188033 * 2
def baseEnd_3188033 : Nat := 1636993271395230539926009

theorem tailTrace_3188033 : CollatzResearch.WordTrace tailWord_3188033 prefixEnd_3188033 1636993271395230539926009 := by
  unfold tailWord_3188033
  simp only [CollatzResearch.WordTrace]
  refine ⟨116277116059308388533824753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77518077372872259022549835 116277116059308388533824753)
  ·
    refine ⟨87207837044481291400368565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116277116059308388533824753 87207837044481291400368565)
    ·
      refine ⟨8175734722920121068784553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87207837044481291400368565 8175734722920121068784553)
      ·
        refine ⟨6131801042190090801588415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8175734722920121068784553 6131801042190090801588415)
        ·
          refine ⟨9197701563285136202382623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6131801042190090801588415 9197701563285136202382623)
          ·
            refine ⟨13796552344927704303573935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9197701563285136202382623 13796552344927704303573935)
            ·
              refine ⟨20694828517391556455360903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13796552344927704303573935 20694828517391556455360903)
              ·
                refine ⟨31042242776087334683041355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20694828517391556455360903 31042242776087334683041355)
                ·
                  refine ⟨46563364164131002024562033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31042242776087334683041355 46563364164131002024562033)
                  ·
                    refine ⟨34922523123098251518421525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46563364164131002024562033 34922523123098251518421525)
                    ·
                      refine ⟨1636993271395230539926009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34922523123098251518421525 1636993271395230539926009)
                      ·
                        rfl

theorem cell23_3188033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3188033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188033 prefixEnd_3188033 := by exact prefixLift 3188033
  have htrace : WordTrace (prefixWord ++ tailWord_3188033) baseStart_3188033 baseEnd_3188033 := by
    simpa [prefixWord, tailWord_3188033, baseEnd_3188033] using wordTrace_append hprefix tailTrace_3188033
  have hstable : (prefixWord ++ tailWord_3188033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188033).length < 2 ^ (prefixWord ++ tailWord_3188033).sum := by decide
  have hdescent : baseEnd_3188033 < baseStart_3188033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188063 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 8, 2]
def baseStart_3188063 : Nat := 118140960795 + 3188063 * 2 ^ 59
def prefixEnd_3188063 : Nat := 4983230072969 + 3 ^ 40 * 3188063 * 2
def baseEnd_3188063 : Nat := 1637008675814865422550871

theorem tailTrace_3188063 : CollatzResearch.WordTrace tailWord_3188063 prefixEnd_3188063 1637008675814865422550871 := by
  unfold tailWord_3188063
  simp only [CollatzResearch.WordTrace]
  refine ⟨116278210249199703657416843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77518806832799802438277895 116278210249199703657416843)
  ·
    refine ⟨174417315373799555486125265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116278210249199703657416843 174417315373799555486125265)
    ·
      refine ⟨130812986530349666614593949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174417315373799555486125265 130812986530349666614593949)
      ·
        refine ⟨49054869948881124980472731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130812986530349666614593949 49054869948881124980472731)
        ·
          refine ⟨73582304923321687470709097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49054869948881124980472731 73582304923321687470709097)
          ·
            refine ⟨55186728692491265603031823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73582304923321687470709097 55186728692491265603031823)
            ·
              refine ⟨82780093038736898404547735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55186728692491265603031823 82780093038736898404547735)
              ·
                refine ⟨124170139558105347606821603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82780093038736898404547735 124170139558105347606821603)
                ·
                  refine ⟨186255209337158021410232405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124170139558105347606821603 186255209337158021410232405)
                  ·
                    refine ⟨2182678234419820563401161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 186255209337158021410232405 2182678234419820563401161)
                    ·
                      refine ⟨1637008675814865422550871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182678234419820563401161 1637008675814865422550871)
                      ·
                        rfl

theorem cell23_3188063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 8, 2].length) (baseStart_3188063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188063 prefixEnd_3188063 := by exact prefixLift 3188063
  have htrace : WordTrace (prefixWord ++ tailWord_3188063) baseStart_3188063 baseEnd_3188063 := by
    simpa [prefixWord, tailWord_3188063, baseEnd_3188063] using wordTrace_append hprefix tailTrace_3188063
  have hstable : (prefixWord ++ tailWord_3188063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188063).length < 2 ^ (prefixWord ++ tailWord_3188063).sum := by decide
  have hdescent : baseEnd_3188063 < baseStart_3188063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188103 : List Nat := [1, 1, 4, 2, 2, 3, 2, 8]
def baseStart_3188103 : Nat := 118140960795 + 3188103 * 2 ^ 59
def prefixEnd_3188103 : Nat := 4983230072969 + 3 ^ 40 * 3188103 * 2
def baseEnd_3188103 : Nat := 60630711668186861705581

theorem tailTrace_3188103 : CollatzResearch.WordTrace tailWord_3188103 prefixEnd_3188103 60630711668186861705581 := by
  unfold tailWord_3188103
  simp only [CollatzResearch.WordTrace]
  refine ⟨116279669169054790488872963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77519779446036526992581975 116279669169054790488872963)
  ·
    refine ⟨174419503753582185733309445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116279669169054790488872963 174419503753582185733309445)
    ·
      refine ⟨32703656953796659824995521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174419503753582185733309445 32703656953796659824995521)
      ·
        refine ⟨24527742715347494868746641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32703656953796659824995521 24527742715347494868746641)
        ·
          refine ⟨18395807036510621151559981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24527742715347494868746641 18395807036510621151559981)
          ·
            refine ⟨6898427638691482931834993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18395807036510621151559981 6898427638691482931834993)
            ·
              refine ⟨5173820729018612198876245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6898427638691482931834993 5173820729018612198876245)
              ·
                refine ⟨60630711668186861705581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5173820729018612198876245 60630711668186861705581)
                ·
                  rfl

theorem cell23_3188103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 8].length) (baseStart_3188103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188103 prefixEnd_3188103 := by exact prefixLift 3188103
  have htrace : WordTrace (prefixWord ++ tailWord_3188103) baseStart_3188103 baseEnd_3188103 := by
    simpa [prefixWord, tailWord_3188103, baseEnd_3188103] using wordTrace_append hprefix tailTrace_3188103
  have hstable : (prefixWord ++ tailWord_3188103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188103).length < 2 ^ (prefixWord ++ tailWord_3188103).sum := by decide
  have hdescent : baseEnd_3188103 < baseStart_3188103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188130 : List Nat := [3, 3, 1, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3188130 : Nat := 118140960795 + 3188130 * 2 ^ 59
def prefixEnd_3188130 : Nat := 4983230072969 + 3 ^ 40 * 3188130 * 2
def baseEnd_3188130 : Nat := 1637043079018716660413063

theorem tailTrace_3188130 : CollatzResearch.WordTrace tailWord_3188130 prefixEnd_3188130 1637043079018716660413063 := by
  unfold tailWord_3188130
  simp only [CollatzResearch.WordTrace]
  refine ⟨29070163484989243525026461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77520435959971316066737229 29070163484989243525026461)
  ·
    refine ⟨10901311306870966321884923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29070163484989243525026461 10901311306870966321884923)
    ·
      refine ⟨16351966960306449482827385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10901311306870966321884923 16351966960306449482827385)
      ·
        refine ⟨12263975220229837112120539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16351966960306449482827385 12263975220229837112120539)
        ·
          refine ⟨18395962830344755668180809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12263975220229837112120539 18395962830344755668180809)
          ·
            refine ⟨13796972122758566751135607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18395962830344755668180809 13796972122758566751135607)
            ·
              refine ⟨20695458184137850126703411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13796972122758566751135607 20695458184137850126703411)
              ·
                refine ⟨31043187276206775190055117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20695458184137850126703411 31043187276206775190055117)
                ·
                  refine ⟨11641195228577540696270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31043187276206775190055117 11641195228577540696270669)
                  ·
                    refine ⟨4365448210716577761101501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11641195228577540696270669 4365448210716577761101501)
                    ·
                      refine ⟨1637043079018716660413063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4365448210716577761101501 1637043079018716660413063)
                      ·
                        rfl

theorem cell23_3188130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3188130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188130 prefixEnd_3188130 := by exact prefixLift 3188130
  have htrace : WordTrace (prefixWord ++ tailWord_3188130) baseStart_3188130 baseEnd_3188130 := by
    simpa [prefixWord, tailWord_3188130, baseEnd_3188130] using wordTrace_append hprefix tailTrace_3188130
  have hstable : (prefixWord ++ tailWord_3188130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188130).length < 2 ^ (prefixWord ++ tailWord_3188130).sum := by decide
  have hdescent : baseEnd_3188130 < baseStart_3188130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188164 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 2, 1, 3]
def baseStart_3188164 : Nat := 118140960795 + 3188164 * 2 ^ 59
def prefixEnd_3188164 : Nat := 4983230072969 + 3 ^ 40 * 3188164 * 2
def baseEnd_3188164 : Nat := 1637060537360969527387907

theorem tailTrace_3188164 : CollatzResearch.WordTrace tailWord_3188164 prefixEnd_3188164 1637060537360969527387907 := by
  unfold tailWord_3188164
  simp only [CollatzResearch.WordTrace]
  refine ⟨58140947010916898953421773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77521262681222531937895697 58140947010916898953421773)
  ·
    refine ⟨21802855129093837107533165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58140947010916898953421773 21802855129093837107533165)
    ·
      refine ⟨8176070673410188915324937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21802855129093837107533165 8176070673410188915324937)
      ·
        refine ⟨6132053005057641686493703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8176070673410188915324937 6132053005057641686493703)
        ·
          refine ⟨9198079507586462529740555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6132053005057641686493703 9198079507586462529740555)
          ·
            refine ⟨13797119261379693794610833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9198079507586462529740555 13797119261379693794610833)
            ·
              refine ⟨10347839446034770345958125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13797119261379693794610833 10347839446034770345958125)
              ·
                refine ⟨3880439792263038879734297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10347839446034770345958125 3880439792263038879734297)
                ·
                  refine ⟨2910329844197279159800723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880439792263038879734297 2910329844197279159800723)
                  ·
                    refine ⟨4365494766295918739701085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2910329844197279159800723 4365494766295918739701085)
                    ·
                      refine ⟨1637060537360969527387907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4365494766295918739701085 1637060537360969527387907)
                      ·
                        rfl

theorem cell23_3188164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_3188164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188164 prefixEnd_3188164 := by exact prefixLift 3188164
  have htrace : WordTrace (prefixWord ++ tailWord_3188164) baseStart_3188164 baseEnd_3188164 := by
    simpa [prefixWord, tailWord_3188164, baseEnd_3188164] using wordTrace_append hprefix tailTrace_3188164
  have hstable : (prefixWord ++ tailWord_3188164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188164).length < 2 ^ (prefixWord ++ tailWord_3188164).sum := by decide
  have hdescent : baseEnd_3188164 < baseStart_3188164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188210 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 7]
def baseStart_3188210 : Nat := 118140960795 + 3188210 * 2 ^ 59
def prefixEnd_3188210 : Nat := 4983230072969 + 3 ^ 40 * 3188210 * 2
def baseEnd_3188210 : Nat := 181898239719008483045855

theorem tailTrace_3188210 : CollatzResearch.WordTrace tailWord_3188210 prefixEnd_3188210 181898239719008483045855 := by
  unfold tailWord_3188210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29070892944916786940754521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77522381186444765175345389 29070892944916786940754521)
  ·
    refine ⟨21803169708687590205565891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29070892944916786940754521 21803169708687590205565891)
    ·
      refine ⟨32704754563031385308348837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21803169708687590205565891 32704754563031385308348837)
      ·
        refine ⟨6132141480568384745315407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32704754563031385308348837 6132141480568384745315407)
        ·
          refine ⟨9198212220852577117973111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6132141480568384745315407 9198212220852577117973111)
          ·
            refine ⟨13797318331278865676959667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9198212220852577117973111 13797318331278865676959667)
            ·
              refine ⟨20695977496918298515439501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13797318331278865676959667 20695977496918298515439501)
              ·
                refine ⟨7760991561344361943289813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20695977496918298515439501 7760991561344361943289813)
                ·
                  refine ⟨181898239719008483045855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7760991561344361943289813 181898239719008483045855)
                  ·
                    rfl

theorem cell23_3188210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_3188210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188210 prefixEnd_3188210 := by exact prefixLift 3188210
  have htrace : WordTrace (prefixWord ++ tailWord_3188210) baseStart_3188210 baseEnd_3188210 := by
    simpa [prefixWord, tailWord_3188210, baseEnd_3188210] using wordTrace_append hprefix tailTrace_3188210
  have hstable : (prefixWord ++ tailWord_3188210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188210).length < 2 ^ (prefixWord ++ tailWord_3188210).sum := by decide
  have hdescent : baseEnd_3188210 < baseStart_3188210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188220 : List Nat := [2, 2, 2, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_3188220 : Nat := 118140960795 + 3188220 * 2 ^ 59
def prefixEnd_3188220 : Nat := 4983230072969 + 3 ^ 40 * 3188220 * 2
def baseEnd_3188220 : Nat := 1637089292277621308287649

theorem tailTrace_3188220 : CollatzResearch.WordTrace tailWord_3188220 prefixEnd_3188220 1637089292277621308287649 := by
  unfold tailWord_3188220
  simp only [CollatzResearch.WordTrace]
  refine ⟨58141968254815459735441057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77522624339753946313921409 58141968254815459735441057)
  ·
    refine ⟨43606476191111594801580793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58141968254815459735441057 43606476191111594801580793)
    ·
      refine ⟨32704857143333696101185595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43606476191111594801580793 32704857143333696101185595)
      ·
        refine ⟨49057285715000544151778393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32704857143333696101185595 49057285715000544151778393)
        ·
          refine ⟨36792964286250408113833795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49057285715000544151778393 36792964286250408113833795)
          ·
            refine ⟨55189446429375612170750693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36792964286250408113833795 55189446429375612170750693)
            ·
              refine ⟨10348021205507927282015755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55189446429375612170750693 10348021205507927282015755)
              ·
                refine ⟨15522031808261890923023633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348021205507927282015755 15522031808261890923023633)
                ·
                  refine ⟨11641523856196418192267725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15522031808261890923023633 11641523856196418192267725)
                  ·
                    refine ⟨4365571446073656822100397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11641523856196418192267725 4365571446073656822100397)
                    ·
                      refine ⟨1637089292277621308287649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4365571446073656822100397 1637089292277621308287649)
                      ·
                        rfl

theorem cell23_3188220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_3188220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188220 prefixEnd_3188220 := by exact prefixLift 3188220
  have htrace : WordTrace (prefixWord ++ tailWord_3188220) baseStart_3188220 baseEnd_3188220 := by
    simpa [prefixWord, tailWord_3188220, baseEnd_3188220] using wordTrace_append hprefix tailTrace_3188220
  have hstable : (prefixWord ++ tailWord_3188220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188220).length < 2 ^ (prefixWord ++ tailWord_3188220).sum := by decide
  have hdescent : baseEnd_3188220 < baseStart_3188220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188221 : List Nat := [1, 4, 1, 1, 1, 5, 3, 1, 2, 2, 2]
def baseStart_3188221 : Nat := 118140960795 + 3188221 * 2 ^ 59
def prefixEnd_3188221 : Nat := 4983230072969 + 3 ^ 40 * 3188221 * 2
def baseEnd_3188221 : Nat := 1637089805758275804375145

theorem tailTrace_3188221 : CollatzResearch.WordTrace tailWord_3188221 prefixEnd_3188221 1637089805758275804375145 := by
  unfold tailWord_3188221
  simp only [CollatzResearch.WordTrace]
  refine ⟨116283972982627296641668517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77522648655084864427779011 116283972982627296641668517)
  ·
    refine ⟨21803244934242618120312847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116283972982627296641668517 21803244934242618120312847)
    ·
      refine ⟨32704867401363927180469271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21803244934242618120312847 32704867401363927180469271)
      ·
        refine ⟨49057301102045890770703907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32704867401363927180469271 49057301102045890770703907)
        ·
          refine ⟨73585951653068836156055861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49057301102045890770703907 73585951653068836156055861)
          ·
            refine ⟨6898682967475203389630237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73585951653068836156055861 6898682967475203389630237)
            ·
              refine ⟨2587006112803201271111339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6898682967475203389630237 2587006112803201271111339)
              ·
                refine ⟨3880509169204801906667009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587006112803201271111339 3880509169204801906667009)
                ·
                  refine ⟨2910381876903601430000257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880509169204801906667009 2910381876903601430000257)
                  ·
                    refine ⟨2182786407677701072500193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910381876903601430000257 2182786407677701072500193)
                    ·
                      refine ⟨1637089805758275804375145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182786407677701072500193 1637089805758275804375145)
                      ·
                        rfl

theorem cell23_3188221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_3188221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188221 prefixEnd_3188221 := by exact prefixLift 3188221
  have htrace : WordTrace (prefixWord ++ tailWord_3188221) baseStart_3188221 baseEnd_3188221 := by
    simpa [prefixWord, tailWord_3188221, baseEnd_3188221] using wordTrace_append hprefix tailTrace_3188221
  have hstable : (prefixWord ++ tailWord_3188221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188221).length < 2 ^ (prefixWord ++ tailWord_3188221).sum := by decide
  have hdescent : baseEnd_3188221 < baseStart_3188221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188223 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 6, 5]
def baseStart_3188223 : Nat := 118140960795 + 3188223 * 2 ^ 59
def prefixEnd_3188223 : Nat := 4983230072969 + 3 ^ 40 * 3188223 * 2
def baseEnd_3188223 : Nat := 545696944239861598850045

theorem tailTrace_3188223 : CollatzResearch.WordTrace tailWord_3188223 prefixEnd_3188223 545696944239861598850045 := by
  unfold tailWord_3188223
  simp only [CollatzResearch.WordTrace]
  refine ⟨116284045928620050983241323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77522697285746700655494215 116284045928620050983241323)
  ·
    refine ⟨174426068892930076474861985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116284045928620050983241323 174426068892930076474861985)
    ·
      refine ⟨130819551669697557356146489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174426068892930076474861985 130819551669697557356146489)
      ·
        refine ⟨98114663752273168017109867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130819551669697557356146489 98114663752273168017109867)
        ·
          refine ⟨147171995628409752025664801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98114663752273168017109867 147171995628409752025664801)
          ·
            refine ⟨110378996721307314019248601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147171995628409752025664801 110378996721307314019248601)
            ·
              refine ⟨82784247540980485514436451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110378996721307314019248601 82784247540980485514436451)
              ·
                refine ⟨124176371311470728271654677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82784247540980485514436451 124176371311470728271654677)
                ·
                  refine ⟨5820767405225190387733813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124176371311470728271654677 5820767405225190387733813)
                  ·
                    refine ⟨545696944239861598850045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5820767405225190387733813 545696944239861598850045)
                    ·
                      rfl

theorem cell23_3188223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 5].length) (baseStart_3188223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188223 prefixEnd_3188223 := by exact prefixLift 3188223
  have htrace : WordTrace (prefixWord ++ tailWord_3188223) baseStart_3188223 baseEnd_3188223 := by
    simpa [prefixWord, tailWord_3188223, baseEnd_3188223] using wordTrace_append hprefix tailTrace_3188223
  have hstable : (prefixWord ++ tailWord_3188223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188223).length < 2 ^ (prefixWord ++ tailWord_3188223).sum := by decide
  have hdescent : baseEnd_3188223 < baseStart_3188223 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188303 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 8]
def baseStart_3188303 : Nat := 118140960795 + 3188303 * 2 ^ 59
def prefixEnd_3188303 : Nat := 4983230072969 + 3 ^ 40 * 3188303 * 2
def baseEnd_3188303 : Nat := 1637131911171944483549767

theorem tailTrace_3188303 : CollatzResearch.WordTrace tailWord_3188303 prefixEnd_3188303 1637131911171944483549767 := by
  unfold tailWord_3188303
  simp only [CollatzResearch.WordTrace]
  refine ⟨116286963768330224646153563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77524642512220149764102375 116286963768330224646153563)
  ·
    refine ⟨174430445652495336969230345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116286963768330224646153563 174430445652495336969230345)
    ·
      refine ⟨130822834239371502726922759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174430445652495336969230345 130822834239371502726922759)
      ·
        refine ⟨196234251359057254090384139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130822834239371502726922759 196234251359057254090384139)
        ·
          refine ⟨294351377038585881135576209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196234251359057254090384139 294351377038585881135576209)
          ·
            refine ⟨220763532778939410851682157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294351377038585881135576209 220763532778939410851682157)
            ·
              refine ⟨82786324792102279069380809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220763532778939410851682157 82786324792102279069380809)
              ·
                refine ⟨62089743594076709302035607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82786324792102279069380809 62089743594076709302035607)
                ·
                  refine ⟨93134615391115063953053411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62089743594076709302035607 93134615391115063953053411)
                  ·
                    refine ⟨139701923086672595929580117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93134615391115063953053411 139701923086672595929580117)
                    ·
                      refine ⟨1637131911171944483549767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 139701923086672595929580117 1637131911171944483549767)
                      ·
                        rfl

theorem cell23_3188303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 8].length) (baseStart_3188303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188303 prefixEnd_3188303 := by exact prefixLift 3188303
  have htrace : WordTrace (prefixWord ++ tailWord_3188303) baseStart_3188303 baseEnd_3188303 := by
    simpa [prefixWord, tailWord_3188303, baseEnd_3188303] using wordTrace_append hprefix tailTrace_3188303
  have hstable : (prefixWord ++ tailWord_3188303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188303).length < 2 ^ (prefixWord ++ tailWord_3188303).sum := by decide
  have hdescent : baseEnd_3188303 < baseStart_3188303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188337 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 4, 3, 2]
def baseStart_3188337 : Nat := 118140960795 + 3188337 * 2 ^ 59
def prefixEnd_3188337 : Nat := 4983230072969 + 3 ^ 40 * 3188337 * 2
def baseEnd_3188337 : Nat := 1637149369514197350524611

theorem tailTrace_3188337 : CollatzResearch.WordTrace tailWord_3188337 prefixEnd_3188337 1637149369514197350524611 := by
  unfold tailWord_3188337
  simp only [CollatzResearch.WordTrace]
  refine ⟨116288203850207048452891265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77525469233471365635260843 116288203850207048452891265)
  ·
    refine ⟨87216152887655286339668449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116288203850207048452891265 87216152887655286339668449)
    ·
      refine ⟨65412114665741464754751337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87216152887655286339668449 65412114665741464754751337)
      ·
        refine ⟨49059085999306098566063503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65412114665741464754751337 49059085999306098566063503)
        ·
          refine ⟨73588628998959147849095255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49059085999306098566063503 73588628998959147849095255)
          ·
            refine ⟨110382943498438721773642883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73588628998959147849095255 110382943498438721773642883)
            ·
              refine ⟨165574415247658082660464325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110382943498438721773642883 165574415247658082660464325)
              ·
                refine ⟨31045202858935890498837061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165574415247658082660464325 31045202858935890498837061)
                ·
                  refine ⟨5820975536050479468531949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31045202858935890498837061 5820975536050479468531949)
                  ·
                    refine ⟨2182865826018929800699481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5820975536050479468531949 2182865826018929800699481)
                    ·
                      refine ⟨1637149369514197350524611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182865826018929800699481 1637149369514197350524611)
                      ·
                        rfl

theorem cell23_3188337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 3, 2].length) (baseStart_3188337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188337 prefixEnd_3188337 := by exact prefixLift 3188337
  have htrace : WordTrace (prefixWord ++ tailWord_3188337) baseStart_3188337 baseEnd_3188337 := by
    simpa [prefixWord, tailWord_3188337, baseEnd_3188337] using wordTrace_append hprefix tailTrace_3188337
  have hstable : (prefixWord ++ tailWord_3188337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188337).length < 2 ^ (prefixWord ++ tailWord_3188337).sum := by decide
  have hdescent : baseEnd_3188337 < baseStart_3188337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188377 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 2, 4]
def baseStart_3188377 : Nat := 118140960795 + 3188377 * 2 ^ 59
def prefixEnd_3188377 : Nat := 4983230072969 + 3 ^ 40 * 3188377 * 2
def baseEnd_3188377 : Nat := 545723302913459064674809

theorem tailTrace_3188377 : CollatzResearch.WordTrace tailWord_3188377 prefixEnd_3188377 545723302913459064674809 := by
  unfold tailWord_3188377
  simp only [CollatzResearch.WordTrace]
  refine ⟨116289662770062135284347385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77526441846708090189564923 116289662770062135284347385)
  ·
    refine ⟨87217247077546601463260539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116289662770062135284347385 87217247077546601463260539)
    ·
      refine ⟨130825870616319902194890809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87217247077546601463260539 130825870616319902194890809)
      ·
        refine ⟨98119402962239926646168107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130825870616319902194890809 98119402962239926646168107)
        ·
          refine ⟨147179104443359889969252161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98119402962239926646168107 147179104443359889969252161)
          ·
            refine ⟨110384328332519917476939121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147179104443359889969252161 110384328332519917476939121)
            ·
              refine ⟨82788246249389938107704341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110384328332519917476939121 82788246249389938107704341)
              ·
                refine ⟨3880699042940153348798641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82788246249389938107704341 3880699042940153348798641)
                ·
                  refine ⟨2910524282205115011598981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880699042940153348798641 2910524282205115011598981)
                  ·
                    refine ⟨545723302913459064674809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2910524282205115011598981 545723302913459064674809)
                    ·
                      rfl

theorem cell23_3188377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 4].length) (baseStart_3188377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188377 prefixEnd_3188377 := by exact prefixLift 3188377
  have htrace : WordTrace (prefixWord ++ tailWord_3188377) baseStart_3188377 baseEnd_3188377 := by
    simpa [prefixWord, tailWord_3188377, baseEnd_3188377] using wordTrace_append hprefix tailTrace_3188377
  have hstable : (prefixWord ++ tailWord_3188377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188377).length < 2 ^ (prefixWord ++ tailWord_3188377).sum := by decide
  have hdescent : baseEnd_3188377 < baseStart_3188377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188397 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 6]
def baseStart_3188397 : Nat := 118140960795 + 3188397 * 2 ^ 59
def prefixEnd_3188397 : Nat := 4983230072969 + 3 ^ 40 * 3188397 * 2
def baseEnd_3188397 : Nat := 1637180178353467115774335

theorem tailTrace_3188397 : CollatzResearch.WordTrace tailWord_3188397 prefixEnd_3188397 1637180178353467115774335 := by
  unfold tailWord_3188397
  simp only [CollatzResearch.WordTrace]
  refine ⟨116290392229989678700075445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77526928153326452466716963 116290392229989678700075445)
  ·
    refine ⟨10902224271561532378132073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116290392229989678700075445 10902224271561532378132073)
    ·
      refine ⟨8176668203671149283599055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10902224271561532378132073 8176668203671149283599055)
      ·
        refine ⟨12265002305506723925398583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8176668203671149283599055 12265002305506723925398583)
        ·
          refine ⟨18397503458260085888097875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12265002305506723925398583 18397503458260085888097875)
          ·
            refine ⟨27596255187390128832146813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18397503458260085888097875 27596255187390128832146813)
            ·
              refine ⟨10348595695271298312055055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27596255187390128832146813 10348595695271298312055055)
              ·
                refine ⟨15522893542906947468082583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348595695271298312055055 15522893542906947468082583)
                ·
                  refine ⟨23284340314360421202123875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15522893542906947468082583 23284340314360421202123875)
                  ·
                    refine ⟨34926510471540631803185813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23284340314360421202123875 34926510471540631803185813)
                    ·
                      refine ⟨1637180178353467115774335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34926510471540631803185813 1637180178353467115774335)
                      ·
                        rfl

theorem cell23_3188397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_3188397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188397 prefixEnd_3188397 := by exact prefixLift 3188397
  have htrace : WordTrace (prefixWord ++ tailWord_3188397) baseStart_3188397 baseEnd_3188397 := by
    simpa [prefixWord, tailWord_3188397, baseEnd_3188397] using wordTrace_append hprefix tailTrace_3188397
  have hstable : (prefixWord ++ tailWord_3188397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188397).length < 2 ^ (prefixWord ++ tailWord_3188397).sum := by decide
  have hdescent : baseEnd_3188397 < baseStart_3188397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188407 : List Nat := [1, 1, 3, 1, 5, 1, 4, 7]
def baseStart_3188407 : Nat := 118140960795 + 3188407 * 2 ^ 59
def prefixEnd_3188407 : Nat := 4983230072969 + 3 ^ 40 * 3188407 * 2
def baseEnd_3188407 : Nat := 60636493080000447283307

theorem tailTrace_3188407 : CollatzResearch.WordTrace tailWord_3188407 prefixEnd_3188407 60636493080000447283307 := by
  unfold tailWord_3188407
  simp only [CollatzResearch.WordTrace]
  refine ⟨116290756959953450407939475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77527171306635633605292983 116290756959953450407939475)
  ·
    refine ⟨174436135439930175611909213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116290756959953450407939475 174436135439930175611909213)
    ·
      refine ⟨65413550789973815854465955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174436135439930175611909213 65413550789973815854465955)
      ·
        refine ⟨98120326184960723781698933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65413550789973815854465955 98120326184960723781698933)
        ·
          refine ⟨9198780579840067854534275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98120326184960723781698933 9198780579840067854534275)
          ·
            refine ⟨13798170869760101781801413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9198780579840067854534275 13798170869760101781801413)
            ·
              refine ⟨2587157038080019084087765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13798170869760101781801413 2587157038080019084087765)
              ·
                refine ⟨60636493080000447283307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2587157038080019084087765 60636493080000447283307)
                ·
                  rfl

theorem cell23_3188407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 7].length) (baseStart_3188407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188407 prefixEnd_3188407 := by exact prefixLift 3188407
  have htrace : WordTrace (prefixWord ++ tailWord_3188407) baseStart_3188407 baseEnd_3188407 := by
    simpa [prefixWord, tailWord_3188407, baseEnd_3188407] using wordTrace_append hprefix tailTrace_3188407
  have hstable : (prefixWord ++ tailWord_3188407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188407).length < 2 ^ (prefixWord ++ tailWord_3188407).sum := by decide
  have hdescent : baseEnd_3188407 < baseStart_3188407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188445 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3188445 : Nat := 118140960795 + 3188445 * 2 ^ 59
def prefixEnd_3188445 : Nat := 4983230072969 + 3 ^ 40 * 3188445 * 2
def baseEnd_3188445 : Nat := 545734941808294309324705

theorem tailTrace_3188445 : CollatzResearch.WordTrace tailWord_3188445 prefixEnd_3188445 545734941808294309324705 := by
  unfold tailWord_3188445
  simp only [CollatzResearch.WordTrace]
  refine ⟨116292142933815782897822789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77528095289210521931881859 116292142933815782897822789)
  ·
    refine ⟨21804776800090459293341773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116292142933815782897822789 21804776800090459293341773)
    ·
      refine ⟨8176791300033922235003165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21804776800090459293341773 8176791300033922235003165)
      ·
        refine ⟨3066296737512720838126187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8176791300033922235003165 3066296737512720838126187)
        ·
          refine ⟨4599445106269081257189281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3066296737512720838126187 4599445106269081257189281)
          ·
            refine ⟨3449583829701810942891961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4599445106269081257189281 3449583829701810942891961)
            ·
              refine ⟨2587187872276358207168971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3449583829701810942891961 2587187872276358207168971)
              ·
                refine ⟨3880781808414537310753457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587187872276358207168971 3880781808414537310753457)
                ·
                  refine ⟨2910586356310902983065093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880781808414537310753457 2910586356310902983065093)
                  ·
                    refine ⟨545734941808294309324705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2910586356310902983065093 545734941808294309324705)
                    ·
                      rfl

theorem cell23_3188445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3188445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188445 prefixEnd_3188445 := by exact prefixLift 3188445
  have htrace : WordTrace (prefixWord ++ tailWord_3188445) baseStart_3188445 baseEnd_3188445 := by
    simpa [prefixWord, tailWord_3188445, baseEnd_3188445] using wordTrace_append hprefix tailTrace_3188445
  have hstable : (prefixWord ++ tailWord_3188445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188445).length < 2 ^ (prefixWord ++ tailWord_3188445).sum := by decide
  have hdescent : baseEnd_3188445 < baseStart_3188445 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188455 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3188455 : Nat := 118140960795 + 3188455 * 2 ^ 59
def prefixEnd_3188455 : Nat := 4983230072969 + 3 ^ 40 * 3188455 * 2
def baseEnd_3188455 : Nat := 1637209960231427888849069

theorem tailTrace_3188455 : CollatzResearch.WordTrace tailWord_3188455 prefixEnd_3188455 1637209960231427888849069 := by
  unfold tailWord_3188455
  simp only [CollatzResearch.WordTrace]
  refine ⟨116292507663779554605686819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77528338442519703070457879 116292507663779554605686819)
  ·
    refine ⟨174438761495669331908530229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116292507663779554605686819 174438761495669331908530229)
    ·
      refine ⟨16353633890218999866424709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174438761495669331908530229 16353633890218999866424709)
      ·
        refine ⟨3066306354416062474954633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16353633890218999866424709 3066306354416062474954633)
        ·
          refine ⟨2299729765812046856215975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066306354416062474954633 2299729765812046856215975)
          ·
            refine ⟨3449594648718070284323963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2299729765812046856215975 3449594648718070284323963)
            ·
              refine ⟨5174391973077105426485945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449594648718070284323963 5174391973077105426485945)
              ·
                refine ⟨3880793979807829069864459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174391973077105426485945 3880793979807829069864459)
                ·
                  refine ⟨5821190969711743604796689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3880793979807829069864459 5821190969711743604796689)
                  ·
                    refine ⟨4365893227283807703597517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5821190969711743604796689 4365893227283807703597517)
                    ·
                      refine ⟨1637209960231427888849069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4365893227283807703597517 1637209960231427888849069)
                      ·
                        rfl

theorem cell23_3188455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3188455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188455 prefixEnd_3188455 := by exact prefixLift 3188455
  have htrace : WordTrace (prefixWord ++ tailWord_3188455) baseStart_3188455 baseEnd_3188455 := by
    simpa [prefixWord, tailWord_3188455, baseEnd_3188455] using wordTrace_append hprefix tailTrace_3188455
  have hstable : (prefixWord ++ tailWord_3188455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188455).length < 2 ^ (prefixWord ++ tailWord_3188455).sum := by decide
  have hdescent : baseEnd_3188455 < baseStart_3188455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188461 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 3, 3, 2]
def baseStart_3188461 : Nat := 118140960795 + 3188461 * 2 ^ 59
def prefixEnd_3188461 : Nat := 4983230072969 + 3 ^ 40 * 3188461 * 2
def baseEnd_3188461 : Nat := 1637213041115354865374041

theorem tailTrace_3188461 : CollatzResearch.WordTrace tailWord_3188461 prefixEnd_3188461 1637213041115354865374041 := by
  unfold tailWord_3188461
  simp only [CollatzResearch.WordTrace]
  refine ⟨116292726501757817630405237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77528484334505211753603491 116292726501757817630405237)
  ·
    refine ⟨10902443109539795402850491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116292726501757817630405237 10902443109539795402850491)
    ·
      refine ⟨16353664664309693104275737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10902443109539795402850491 16353664664309693104275737)
      ·
        refine ⟨12265248498232269828206803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16353664664309693104275737 12265248498232269828206803)
        ·
          refine ⟨18397872747348404742310205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12265248498232269828206803 18397872747348404742310205)
          ·
            refine ⟨6899202280255651778366327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18397872747348404742310205 6899202280255651778366327)
            ·
              refine ⟨10348803420383477667549491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899202280255651778366327 10348803420383477667549491)
              ·
                refine ⟨15523205130575216501324237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10348803420383477667549491 15523205130575216501324237)
                ·
                  refine ⟨5821201923965706187996589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15523205130575216501324237 5821201923965706187996589)
                  ·
                    refine ⟨2182950721487139820498721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5821201923965706187996589 2182950721487139820498721)
                    ·
                      refine ⟨1637213041115354865374041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182950721487139820498721 1637213041115354865374041)
                      ·
                        rfl

theorem cell23_3188461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_3188461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188461 prefixEnd_3188461 := by exact prefixLift 3188461
  have htrace : WordTrace (prefixWord ++ tailWord_3188461) baseStart_3188461 baseEnd_3188461 := by
    simpa [prefixWord, tailWord_3188461, baseEnd_3188461] using wordTrace_append hprefix tailTrace_3188461
  have hstable : (prefixWord ++ tailWord_3188461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188461).length < 2 ^ (prefixWord ++ tailWord_3188461).sum := by decide
  have hdescent : baseEnd_3188461 < baseStart_3188461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188468 : List Nat := [2, 6, 1, 1, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3188468 : Nat := 118140960795 + 3188468 * 2 ^ 59
def prefixEnd_3188468 : Nat := 4983230072969 + 3 ^ 40 * 3188468 * 2
def baseEnd_3188468 : Nat := 1637216635479936337986509

theorem tailTrace_3188468 : CollatzResearch.WordTrace tailWord_3188468 prefixEnd_3188468 1637216635479936337986509 := by
  unfold tailWord_3188468
  simp only [CollatzResearch.WordTrace]
  refine ⟨58146490906366228912955029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77528654541821638550606705 58146490906366228912955029)
  ·
    refine ⟨2725616761235916980294767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58146490906366228912955029 2725616761235916980294767)
    ·
      refine ⟨4088425141853875470442151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2725616761235916980294767 4088425141853875470442151)
      ·
        refine ⟨6132637712780813205663227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088425141853875470442151 6132637712780813205663227)
        ·
          refine ⟨9198956569171219808494841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6132637712780813205663227 9198956569171219808494841)
          ·
            refine ⟨6899217426878414856371131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9198956569171219808494841 6899217426878414856371131)
            ·
              refine ⟨10348826140317622284556697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899217426878414856371131 10348826140317622284556697)
              ·
                refine ⟨7761619605238216713417523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10348826140317622284556697 7761619605238216713417523)
                ·
                  refine ⟨11642429407857325070126285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7761619605238216713417523 11642429407857325070126285)
                  ·
                    refine ⟨4365911027946496901297357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11642429407857325070126285 4365911027946496901297357)
                    ·
                      refine ⟨1637216635479936337986509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4365911027946496901297357 1637216635479936337986509)
                      ·
                        rfl

theorem cell23_3188468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3188468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188468 prefixEnd_3188468 := by exact prefixLift 3188468
  have htrace : WordTrace (prefixWord ++ tailWord_3188468) baseStart_3188468 baseEnd_3188468 := by
    simpa [prefixWord, tailWord_3188468, baseEnd_3188468] using wordTrace_append hprefix tailTrace_3188468
  have hstable : (prefixWord ++ tailWord_3188468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188468).length < 2 ^ (prefixWord ++ tailWord_3188468).sum := by decide
  have hdescent : baseEnd_3188468 < baseStart_3188468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188480 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 9]
def baseStart_3188480 : Nat := 118140960795 + 3188480 * 2 ^ 59
def prefixEnd_3188480 : Nat := 4983230072969 + 3 ^ 40 * 3188480 * 2
def baseEnd_3188480 : Nat := 181913644138643365670717

theorem tailTrace_3188480 : CollatzResearch.WordTrace tailWord_3188480 prefixEnd_3188480 181913644138643365670717 := by
  unfold tailWord_3188480
  simp only [CollatzResearch.WordTrace]
  refine ⟨58146709744344491937673447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77528946325792655916897929 58146709744344491937673447)
  ·
    refine ⟨87220064616516737906510171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58146709744344491937673447 87220064616516737906510171)
    ·
      refine ⟨130830096924775106859765257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87220064616516737906510171 130830096924775106859765257)
      ·
        refine ⟨98122572693581330144823943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130830096924775106859765257 98122572693581330144823943)
        ·
          refine ⟨147183859040371995217235915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98122572693581330144823943 147183859040371995217235915)
          ·
            refine ⟨220775788560557992825853873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147183859040371995217235915 220775788560557992825853873)
            ·
              refine ⟨165581841420418494619390405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 220775788560557992825853873 165581841420418494619390405)
              ·
                refine ⟨31046595266328467741135701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 165581841420418494619390405 31046595266328467741135701)
                ·
                  refine ⟨181913644138643365670717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31046595266328467741135701 181913644138643365670717)
                  ·
                    rfl

theorem cell23_3188480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 9].length) (baseStart_3188480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188480 prefixEnd_3188480 := by exact prefixLift 3188480
  have htrace : WordTrace (prefixWord ++ tailWord_3188480) baseStart_3188480 baseEnd_3188480 := by
    simpa [prefixWord, tailWord_3188480, baseEnd_3188480] using wordTrace_append hprefix tailTrace_3188480
  have hstable : (prefixWord ++ tailWord_3188480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188480).length < 2 ^ (prefixWord ++ tailWord_3188480).sum := by decide
  have hdescent : baseEnd_3188480 < baseStart_3188480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188491 : List Nat := [1, 1, 1, 1, 5, 1, 3, 4, 2, 2, 2]
def baseStart_3188491 : Nat := 118140960795 + 3188491 * 2 ^ 59
def prefixEnd_3188491 : Nat := 4983230072969 + 3 ^ 40 * 3188491 * 2
def baseEnd_3188491 : Nat := 1637228445534989747998903

theorem tailTrace_3188491 : CollatzResearch.WordTrace tailWord_3188491 prefixEnd_3188491 1637228445534989747998903 := by
  unfold tailWord_3188491
  simp only [CollatzResearch.WordTrace]
  refine ⟨116293820691649132753997327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77529213794432755169331551 116293820691649132753997327)
  ·
    refine ⟨174440731037473699130995991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116293820691649132753997327 174440731037473699130995991)
    ·
      refine ⟨261661096556210548696493987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174440731037473699130995991 261661096556210548696493987)
      ·
        refine ⟨392491644834315823044740981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261661096556210548696493987 392491644834315823044740981)
        ·
          refine ⟨36796091703217108410444467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 392491644834315823044740981 36796091703217108410444467)
          ·
            refine ⟨55194137554825662615666701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36796091703217108410444467 55194137554825662615666701)
            ·
              refine ⟨20697801583059623480875013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55194137554825662615666701 20697801583059623480875013)
              ·
                refine ⟨3880837796823679402664065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20697801583059623480875013 3880837796823679402664065)
                ·
                  refine ⟨2910628347617759551998049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3880837796823679402664065 2910628347617759551998049)
                  ·
                    refine ⟨2182971260713319663998537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910628347617759551998049 2182971260713319663998537)
                    ·
                      refine ⟨1637228445534989747998903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2182971260713319663998537 1637228445534989747998903)
                      ·
                        rfl

theorem cell23_3188491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 4, 2, 2, 2].length) (baseStart_3188491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188491 prefixEnd_3188491 := by exact prefixLift 3188491
  have htrace : WordTrace (prefixWord ++ tailWord_3188491) baseStart_3188491 baseEnd_3188491 := by
    simpa [prefixWord, tailWord_3188491, baseEnd_3188491] using wordTrace_append hprefix tailTrace_3188491
  have hstable : (prefixWord ++ tailWord_3188491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188491).length < 2 ^ (prefixWord ++ tailWord_3188491).sum := by decide
  have hdescent : baseEnd_3188491 < baseStart_3188491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188507 : List Nat := [1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 3]
def baseStart_3188507 : Nat := 118140960795 + 3188507 * 2 ^ 59
def prefixEnd_3188507 : Nat := 4983230072969 + 3 ^ 40 * 3188507 * 2
def baseEnd_3188507 : Nat := 1637236661225461685398829

theorem tailTrace_3188507 : CollatzResearch.WordTrace tailWord_3188507 prefixEnd_3188507 1637236661225461685398829 := by
  unfold tailWord_3188507
  simp only [CollatzResearch.WordTrace]
  refine ⟨116294404259591167486579775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77529602839727444991053183 116294404259591167486579775)
  ·
    refine ⟨174441606389386751229869663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116294404259591167486579775 174441606389386751229869663)
    ·
      refine ⟨261662409584080126844804495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174441606389386751229869663 261662409584080126844804495)
      ·
        refine ⟨392493614376120190267206743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261662409584080126844804495 392493614376120190267206743)
        ·
          refine ⟨588740421564180285400810115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392493614376120190267206743 588740421564180285400810115)
          ·
            refine ⟨883110632346270428101215173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588740421564180285400810115 883110632346270428101215173)
            ·
              refine ⟨165583243564925705268977845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 883110632346270428101215173 165583243564925705268977845)
              ·
                refine ⟨15523429084211784868966673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165583243564925705268977845 15523429084211784868966673)
                ·
                  refine ⟨11642571813158838651725005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15523429084211784868966673 11642571813158838651725005)
                  ·
                    refine ⟨4365964429934564494396877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11642571813158838651725005 4365964429934564494396877)
                    ·
                      refine ⟨1637236661225461685398829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4365964429934564494396877 1637236661225461685398829)
                      ·
                        rfl

theorem cell23_3188507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 2, 3, 3].length) (baseStart_3188507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188507 prefixEnd_3188507 := by exact prefixLift 3188507
  have htrace : WordTrace (prefixWord ++ tailWord_3188507) baseStart_3188507 baseEnd_3188507 := by
    simpa [prefixWord, tailWord_3188507, baseEnd_3188507] using wordTrace_append hprefix tailTrace_3188507
  have hstable : (prefixWord ++ tailWord_3188507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188507).length < 2 ^ (prefixWord ++ tailWord_3188507).sum := by decide
  have hdescent : baseEnd_3188507 < baseStart_3188507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188531 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 5]
def baseStart_3188531 : Nat := 118140960795 + 3188531 * 2 ^ 59
def prefixEnd_3188531 : Nat := 4983230072969 + 3 ^ 40 * 3188531 * 2
def baseEnd_3188531 : Nat := 181916553862352176833191

theorem tailTrace_3188531 : CollatzResearch.WordTrace tailWord_3188531 prefixEnd_3188531 181916553862352176833191 := by
  unfold tailWord_3188531
  simp only [CollatzResearch.WordTrace]
  refine ⟨116295279611504219585453447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77530186407669479723635631 116295279611504219585453447)
  ·
    refine ⟨174442919417256329378180171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116295279611504219585453447 174442919417256329378180171)
    ·
      refine ⟨261664379125884494067270257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174442919417256329378180171 261664379125884494067270257)
      ·
        refine ⟨196248284344413370550452693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261664379125884494067270257 196248284344413370550452693)
        ·
          refine ⟨4599569164322188372276235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 196248284344413370550452693 4599569164322188372276235)
          ·
            refine ⟨6899353746483282558414353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599569164322188372276235 6899353746483282558414353)
            ·
              refine ⟨5174515309862461918810765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899353746483282558414353 5174515309862461918810765)
              ·
                refine ⟨1940443241198423219554037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5174515309862461918810765 1940443241198423219554037)
                ·
                  refine ⟨181916553862352176833191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1940443241198423219554037 181916553862352176833191)
                  ·
                    rfl

theorem cell23_3188531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 5].length) (baseStart_3188531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188531 prefixEnd_3188531 := by exact prefixLift 3188531
  have htrace : WordTrace (prefixWord ++ tailWord_3188531) baseStart_3188531 baseEnd_3188531 := by
    simpa [prefixWord, tailWord_3188531, baseEnd_3188531] using wordTrace_append hprefix tailTrace_3188531
  have hstable : (prefixWord ++ tailWord_3188531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188531).length < 2 ^ (prefixWord ++ tailWord_3188531).sum := by decide
  have hdescent : baseEnd_3188531 < baseStart_3188531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188564 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 1, 3, 4]
def baseStart_3188564 : Nat := 118140960795 + 3188564 * 2 ^ 59
def prefixEnd_3188564 : Nat := 4983230072969 + 3 ^ 40 * 3188564 * 2
def baseEnd_3188564 : Nat := 1637265929622767962386067

theorem tailTrace_3188564 : CollatzResearch.WordTrace tailWord_3188564 prefixEnd_3188564 1637265929622767962386067 := by
  unfold tailWord_3188564
  simp only [CollatzResearch.WordTrace]
  refine ⟨58148241610192333110702373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77530988813589777480936497 58148241610192333110702373)
  ·
    refine ⟨10902795301911062458256695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58148241610192333110702373 10902795301911062458256695)
    ·
      refine ⟨16354192952866593687385043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10902795301911062458256695 16354192952866593687385043)
      ·
        refine ⟨24531289429299890531077565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16354192952866593687385043 24531289429299890531077565)
        ·
          refine ⟨9199233535987458949154087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24531289429299890531077565 9199233535987458949154087)
          ·
            refine ⟨13798850303981188423731131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9199233535987458949154087 13798850303981188423731131)
            ·
              refine ⟨20698275455971782635596697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13798850303981188423731131 20698275455971782635596697)
              ·
                refine ⟨15523706591978836976697523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20698275455971782635596697 15523706591978836976697523)
                ·
                  refine ⟨23285559887968255465046285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15523706591978836976697523 23285559887968255465046285)
                  ·
                    refine ⟨8732084957988095799392357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23285559887968255465046285 8732084957988095799392357)
                    ·
                      refine ⟨1637265929622767962386067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8732084957988095799392357 1637265929622767962386067)
                      ·
                        rfl

theorem cell23_3188564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_3188564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188564 prefixEnd_3188564 := by exact prefixLift 3188564
  have htrace : WordTrace (prefixWord ++ tailWord_3188564) baseStart_3188564 baseEnd_3188564 := by
    simpa [prefixWord, tailWord_3188564, baseEnd_3188564] using wordTrace_append hprefix tailTrace_3188564
  have hstable : (prefixWord ++ tailWord_3188564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188564).length < 2 ^ (prefixWord ++ tailWord_3188564).sum := by decide
  have hdescent : baseEnd_3188564 < baseStart_3188564 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188577 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 4]
def baseStart_3188577 : Nat := 118140960795 + 3188577 * 2 ^ 59
def prefixEnd_3188577 : Nat := 4983230072969 + 3 ^ 40 * 3188577 * 2
def baseEnd_3188577 : Nat := 1637272604871276411523507

theorem tailTrace_3188577 : CollatzResearch.WordTrace tailWord_3188577 prefixEnd_3188577 1637272604871276411523507 := by
  unfold tailWord_3188577
  simp only [CollatzResearch.WordTrace]
  refine ⟨116296957369337569441627985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77531304912891712961085323 116296957369337569441627985)
  ·
    refine ⟨87222718027003177081220989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116296957369337569441627985 87222718027003177081220989)
    ·
      refine ⟨32708519260126191405457871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87222718027003177081220989 32708519260126191405457871)
      ·
        refine ⟨49062778890189287108186807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32708519260126191405457871 49062778890189287108186807)
        ·
          refine ⟨73594168335283930662280211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49062778890189287108186807 73594168335283930662280211)
          ·
            refine ⟨110391252502925895993420317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73594168335283930662280211 110391252502925895993420317)
            ·
              refine ⟨41396719688597210997532619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110391252502925895993420317 41396719688597210997532619)
              ·
                refine ⟨62095079532895816496298929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41396719688597210997532619 62095079532895816496298929)
                ·
                  refine ⟨46571309649671862372224197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62095079532895816496298929 46571309649671862372224197)
                  ·
                    refine ⟨8732120559313474194792037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46571309649671862372224197 8732120559313474194792037)
                    ·
                      refine ⟨1637272604871276411523507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8732120559313474194792037 1637272604871276411523507)
                      ·
                        rfl

theorem cell23_3188577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_3188577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188577 prefixEnd_3188577 := by exact prefixLift 3188577
  have htrace : WordTrace (prefixWord ++ tailWord_3188577) baseStart_3188577 baseEnd_3188577 := by
    simpa [prefixWord, tailWord_3188577, baseEnd_3188577] using wordTrace_append hprefix tailTrace_3188577
  have hstable : (prefixWord ++ tailWord_3188577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188577).length < 2 ^ (prefixWord ++ tailWord_3188577).sum := by decide
  have hdescent : baseEnd_3188577 < baseStart_3188577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188584 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3188584 : Nat := 118140960795 + 3188584 * 2 ^ 59
def prefixEnd_3188584 : Nat := 4983230072969 + 3 ^ 40 * 3188584 * 2
def baseEnd_3188584 : Nat := 1637276199235857884135975

theorem tailTrace_3188584 : CollatzResearch.WordTrace tailWord_3188584 prefixEnd_3188584 1637276199235857884135975 := by
  unfold tailWord_3188584
  simp only [CollatzResearch.WordTrace]
  refine ⟨58148606340156104818566403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77531475120208139758088537 58148606340156104818566403)
  ·
    refine ⟨87222909510234157227849605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58148606340156104818566403 87222909510234157227849605)
    ·
      refine ⟨16354295533168904480221801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87222909510234157227849605 16354295533168904480221801)
      ·
        refine ⟨12265721649876678360166351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16354295533168904480221801 12265721649876678360166351)
        ·
          refine ⟨18398582474815017540249527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12265721649876678360166351 18398582474815017540249527)
          ·
            refine ⟨27597873712222526310374291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18398582474815017540249527 27597873712222526310374291)
            ·
              refine ⟨41396810568333789465561437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27597873712222526310374291 41396810568333789465561437)
              ·
                refine ⟨15523803963125171049585539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41396810568333789465561437 15523803963125171049585539)
                ·
                  refine ⟨23285705944687756574378309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15523803963125171049585539 23285705944687756574378309)
                  ·
                    refine ⟨4366069864628954357695933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23285705944687756574378309 4366069864628954357695933)
                    ·
                      refine ⟨1637276199235857884135975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4366069864628954357695933 1637276199235857884135975)
                      ·
                        rfl

theorem cell23_3188584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3188584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188584 prefixEnd_3188584 := by exact prefixLift 3188584
  have htrace : WordTrace (prefixWord ++ tailWord_3188584) baseStart_3188584 baseEnd_3188584 := by
    simpa [prefixWord, tailWord_3188584, baseEnd_3188584] using wordTrace_append hprefix tailTrace_3188584
  have hstable : (prefixWord ++ tailWord_3188584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188584).length < 2 ^ (prefixWord ++ tailWord_3188584).sum := by decide
  have hdescent : baseEnd_3188584 < baseStart_3188584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188598 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3188598 : Nat := 118140960795 + 3188598 * 2 ^ 59
def prefixEnd_3188598 : Nat := 4983230072969 + 3 ^ 40 * 3188598 * 2
def baseEnd_3188598 : Nat := 1637283387965020829360911

theorem tailTrace_3188598 : CollatzResearch.WordTrace tailWord_3188598 prefixEnd_3188598 1637283387965020829360911 := by
  unfold tailWord_3188598
  simp only [CollatzResearch.WordTrace]
  refine ⟨7268607706391343126758903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77531815534840993352094965 7268607706391343126758903)
  ·
    refine ⟨10902911559587014690138355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7268607706391343126758903 10902911559587014690138355)
    ·
      refine ⟨16354367339380522035207533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10902911559587014690138355 16354367339380522035207533)
      ·
        refine ⟨6132887752267695763202825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16354367339380522035207533 6132887752267695763202825)
        ·
          refine ⟨4599665814200771822402119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6132887752267695763202825 4599665814200771822402119)
          ·
            refine ⟨6899498721301157733603179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4599665814200771822402119 6899498721301157733603179)
            ·
              refine ⟨10349248081951736600404769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6899498721301157733603179 10349248081951736600404769)
              ·
                refine ⟨7761936061463802450303577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10349248081951736600404769 7761936061463802450303577)
                ·
                  refine ⟨5821452046097851837727683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7761936061463802450303577 5821452046097851837727683)
                  ·
                    refine ⟨8732178069146777756591525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5821452046097851837727683 8732178069146777756591525)
                    ·
                      refine ⟨1637283387965020829360911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8732178069146777756591525 1637283387965020829360911)
                      ·
                        rfl

theorem cell23_3188598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3188598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188598 prefixEnd_3188598 := by exact prefixLift 3188598
  have htrace : WordTrace (prefixWord ++ tailWord_3188598) baseStart_3188598 baseEnd_3188598 := by
    simpa [prefixWord, tailWord_3188598, baseEnd_3188598] using wordTrace_append hprefix tailTrace_3188598
  have hstable : (prefixWord ++ tailWord_3188598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188598).length < 2 ^ (prefixWord ++ tailWord_3188598).sum := by decide
  have hdescent : baseEnd_3188598 < baseStart_3188598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188608 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 1, 4]
def baseStart_3188608 : Nat := 118140960795 + 3188608 * 2 ^ 59
def prefixEnd_3188608 : Nat := 4983230072969 + 3 ^ 40 * 3188608 * 2
def baseEnd_3188608 : Nat := 545762840923855263411955

theorem tailTrace_3188608 : CollatzResearch.WordTrace tailWord_3188608 prefixEnd_3188608 545762840923855263411955 := by
  unfold tailWord_3188608
  simp only [CollatzResearch.WordTrace]
  refine ⟨58149044016112630868003239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77532058688150174490670985 58149044016112630868003239)
  ·
    refine ⟨87223566024168946302004859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58149044016112630868003239 87223566024168946302004859)
    ·
      refine ⟨130835349036253419453007289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87223566024168946302004859 130835349036253419453007289)
      ·
        refine ⟨98126511777190064589755467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130835349036253419453007289 98126511777190064589755467)
        ·
          refine ⟨147189767665785096884633201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98126511777190064589755467 147189767665785096884633201)
          ·
            refine ⟨110392325749338822663474901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147189767665785096884633201 110392325749338822663474901)
            ·
              refine ⟨2587320134750128656175193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 110392325749338822663474901 2587320134750128656175193)
              ·
                refine ⟨1940490101062596492131395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2587320134750128656175193 1940490101062596492131395)
                ·
                  refine ⟨2910735151593894738197093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940490101062596492131395 2910735151593894738197093)
                  ·
                    refine ⟨545762840923855263411955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2910735151593894738197093 545762840923855263411955)
                    ·
                      rfl

theorem cell23_3188608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 1, 4].length) (baseStart_3188608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188608 prefixEnd_3188608 := by exact prefixLift 3188608
  have htrace : WordTrace (prefixWord ++ tailWord_3188608) baseStart_3188608 baseEnd_3188608 := by
    simpa [prefixWord, tailWord_3188608, baseEnd_3188608] using wordTrace_append hprefix tailTrace_3188608
  have hstable : (prefixWord ++ tailWord_3188608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188608).length < 2 ^ (prefixWord ++ tailWord_3188608).sum := by decide
  have hdescent : baseEnd_3188608 < baseStart_3188608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188677 : List Nat := [1, 3, 1, 1, 1, 1, 1, 14]
def baseStart_3188677 : Nat := 118140960795 + 3188677 * 2 ^ 59
def prefixEnd_3188677 : Nat := 4983230072969 + 3 ^ 40 * 3188677 * 2
def baseEnd_3188677 : Nat := 60641627886545408158261

theorem tailTrace_3188677 : CollatzResearch.WordTrace tailWord_3188677 prefixEnd_3188677 60641627886545408158261 := by
  unfold tailWord_3188677
  simp only [CollatzResearch.WordTrace]
  refine ⟨116300604668975286520268285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77533736445983524346845523 116300604668975286520268285)
  ·
    refine ⟨43612726750865732445100607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116300604668975286520268285 43612726750865732445100607)
    ·
      refine ⟨65419090126298598667650911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43612726750865732445100607 65419090126298598667650911)
      ·
        refine ⟨98128635189447898001476367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65419090126298598667650911 98128635189447898001476367)
        ·
          refine ⟨147192952784171847002214551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98128635189447898001476367 147192952784171847002214551)
          ·
            refine ⟨220789429176257770503321827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147192952784171847002214551 220789429176257770503321827)
            ·
              refine ⟨331184143764386655754982741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220789429176257770503321827 331184143764386655754982741)
              ·
                refine ⟨60641627886545408158261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 331184143764386655754982741 60641627886545408158261)
                ·
                  rfl

theorem cell23_3188677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 14].length) (baseStart_3188677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188677 prefixEnd_3188677 := by exact prefixLift 3188677
  have htrace : WordTrace (prefixWord ++ tailWord_3188677) baseStart_3188677 baseEnd_3188677 := by
    simpa [prefixWord, tailWord_3188677, baseEnd_3188677] using wordTrace_append hprefix tailTrace_3188677
  have hstable : (prefixWord ++ tailWord_3188677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188677).length < 2 ^ (prefixWord ++ tailWord_3188677).sum := by decide
  have hdescent : baseEnd_3188677 < baseStart_3188677 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188705 : List Nat := [1, 2, 3, 1, 2, 1, 3, 5, 1, 2, 2]
def baseStart_3188705 : Nat := 118140960795 + 3188705 * 2 ^ 59
def prefixEnd_3188705 : Nat := 4983230072969 + 3 ^ 40 * 3188705 * 2
def baseEnd_3188705 : Nat := 1637338330395051910722919

theorem tailTrace_3188705 : CollatzResearch.WordTrace tailWord_3188705 prefixEnd_3188705 1637338330395051910722919 := by
  unfold tailWord_3188705
  simp only [CollatzResearch.WordTrace]
  refine ⟨116301625912873847302287569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77534417275249231534858379 116301625912873847302287569)
  ·
    refine ⟨87226219434655385476715677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116301625912873847302287569 87226219434655385476715677)
    ·
      refine ⟨32709832287995769553768379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87226219434655385476715677 32709832287995769553768379)
      ·
        refine ⟨49064748431993654330652569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32709832287995769553768379 49064748431993654330652569)
        ·
          refine ⟨36798561323995240747989427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49064748431993654330652569 36798561323995240747989427)
          ·
            refine ⟨55197841985992861121984141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36798561323995240747989427 55197841985992861121984141)
            ·
              refine ⟨20699190744747322920744053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55197841985992861121984141 20699190744747322920744053)
              ·
                refine ⟨1940549132320061523819755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20699190744747322920744053 1940549132320061523819755)
                ·
                  refine ⟨2910823698480092285729633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940549132320061523819755 2910823698480092285729633)
                  ·
                    refine ⟨2183117773860069214297225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910823698480092285729633 2183117773860069214297225)
                    ·
                      refine ⟨1637338330395051910722919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183117773860069214297225 1637338330395051910722919)
                      ·
                        rfl

theorem cell23_3188705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 5, 1, 2, 2].length) (baseStart_3188705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188705 prefixEnd_3188705 := by exact prefixLift 3188705
  have htrace : WordTrace (prefixWord ++ tailWord_3188705) baseStart_3188705 baseEnd_3188705 := by
    simpa [prefixWord, tailWord_3188705, baseEnd_3188705] using wordTrace_append hprefix tailTrace_3188705
  have hstable : (prefixWord ++ tailWord_3188705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188705).length < 2 ^ (prefixWord ++ tailWord_3188705).sum := by decide
  have hdescent : baseEnd_3188705 < baseStart_3188705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188731 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 5, 3, 2]
def baseStart_3188731 : Nat := 118140960795 + 3188731 * 2 ^ 59
def prefixEnd_3188731 : Nat := 4983230072969 + 3 ^ 40 * 3188731 * 2
def baseEnd_3188731 : Nat := 1637351680892068808997799

theorem tailTrace_3188731 : CollatzResearch.WordTrace tailWord_3188731 prefixEnd_3188731 1637351680892068808997799 := by
  unfold tailWord_3188731
  simp only [CollatzResearch.WordTrace]
  refine ⟨116302574210779653742734047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77535049473853102495156031 116302574210779653742734047)
  ·
    refine ⟨174453861316169480614101071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116302574210779653742734047 174453861316169480614101071)
    ·
      refine ⟨261680791974254220921151607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174453861316169480614101071 261680791974254220921151607)
      ·
        refine ⟨392521187961381331381727411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261680791974254220921151607 392521187961381331381727411)
        ·
          refine ⟨588781781942071997072591117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392521187961381331381727411 588781781942071997072591117)
          ·
            refine ⟨220793168228276998902221669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 588781781942071997072591117 220793168228276998902221669)
            ·
              refine ⟨41398719042801937294166563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 220793168228276998902221669 41398719042801937294166563)
              ·
                refine ⟨62098078564202905941249845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41398719042801937294166563 62098078564202905941249845)
                ·
                  refine ⟨5821694865394022431992173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62098078564202905941249845 5821694865394022431992173)
                  ·
                    refine ⟨2183135574522758411997065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5821694865394022431992173 2183135574522758411997065)
                    ·
                      refine ⟨1637351680892068808997799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183135574522758411997065 1637351680892068808997799)
                      ·
                        rfl

theorem cell23_3188731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 3, 2].length) (baseStart_3188731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188731 prefixEnd_3188731 := by exact prefixLift 3188731
  have htrace : WordTrace (prefixWord ++ tailWord_3188731) baseStart_3188731 baseEnd_3188731 := by
    simpa [prefixWord, tailWord_3188731, baseEnd_3188731] using wordTrace_append hprefix tailTrace_3188731
  have hstable : (prefixWord ++ tailWord_3188731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188731).length < 2 ^ (prefixWord ++ tailWord_3188731).sum := by decide
  have hdescent : baseEnd_3188731 < baseStart_3188731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188761 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 3, 4, 2]
def baseStart_3188761 : Nat := 118140960795 + 3188761 * 2 ^ 59
def prefixEnd_3188761 : Nat := 4983230072969 + 3 ^ 40 * 3188761 * 2
def baseEnd_3188761 : Nat := 1637367085311703691622661

theorem tailTrace_3188761 : CollatzResearch.WordTrace tailWord_3188761 prefixEnd_3188761 1637367085311703691622661 := by
  unfold tailWord_3188761
  simp only [CollatzResearch.WordTrace]
  refine ⟨116303668400670968866326137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77535778933780645910884091 116303668400670968866326137)
  ·
    refine ⟨87227751300503226649744603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116303668400670968866326137 87227751300503226649744603)
    ·
      refine ⟨130841626950754839974616905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87227751300503226649744603 130841626950754839974616905)
      ·
        refine ⟨98131220213066129980962679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130841626950754839974616905 98131220213066129980962679)
        ·
          refine ⟨147196830319599194971444019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98131220213066129980962679 147196830319599194971444019)
          ·
            refine ⟨220795245479398792457166029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147196830319599194971444019 220795245479398792457166029)
            ·
              refine ⟨82798217054774547171437261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220795245479398792457166029 82798217054774547171437261)
              ·
                refine ⟨31049331395540455189288973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82798217054774547171437261 31049331395540455189288973)
                ·
                  refine ⟨11643499273327670695983365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31049331395540455189288973 11643499273327670695983365)
                  ·
                    refine ⟨2183156113748938255496881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11643499273327670695983365 2183156113748938255496881)
                    ·
                      refine ⟨1637367085311703691622661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183156113748938255496881 1637367085311703691622661)
                      ·
                        rfl

theorem cell23_3188761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 4, 2].length) (baseStart_3188761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188761 prefixEnd_3188761 := by exact prefixLift 3188761
  have htrace : WordTrace (prefixWord ++ tailWord_3188761) baseStart_3188761 baseEnd_3188761 := by
    simpa [prefixWord, tailWord_3188761, baseEnd_3188761] using wordTrace_append hprefix tailTrace_3188761
  have hstable : (prefixWord ++ tailWord_3188761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188761).length < 2 ^ (prefixWord ++ tailWord_3188761).sum := by decide
  have hdescent : baseEnd_3188761 < baseStart_3188761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188765 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 1, 3, 2]
def baseStart_3188765 : Nat := 118140960795 + 3188765 * 2 ^ 59
def prefixEnd_3188765 : Nat := 4983230072969 + 3 ^ 40 * 3188765 * 2
def baseEnd_3188765 : Nat := 1637369139234321675972643

theorem tailTrace_3188765 : CollatzResearch.WordTrace tailWord_3188765 prefixEnd_3188765 1637369139234321675972643 := by
  unfold tailWord_3188765
  simp only [CollatzResearch.WordTrace]
  refine ⟨116303814292656477549471749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77535876195104318366314499 116303814292656477549471749)
  ·
    refine ⟨21806965179873089540525953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116303814292656477549471749 21806965179873089540525953)
    ·
      refine ⟨16355223884904817155394465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21806965179873089540525953 16355223884904817155394465)
      ·
        refine ⟨12266417913678612866545849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16355223884904817155394465 12266417913678612866545849)
        ·
          refine ⟨9199813435258959649909387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12266417913678612866545849 9199813435258959649909387)
          ·
            refine ⟨13799720152888439474864081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9199813435258959649909387 13799720152888439474864081)
            ·
              refine ⟨10349790114666329606148061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13799720152888439474864081 10349790114666329606148061)
              ·
                refine ⟨3881171292999873602305523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10349790114666329606148061 3881171292999873602305523)
                ·
                  refine ⟨5821756939499810403458285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881171292999873602305523 5821756939499810403458285)
                  ·
                    refine ⟨2183158852312428901296857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5821756939499810403458285 2183158852312428901296857)
                    ·
                      refine ⟨1637369139234321675972643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183158852312428901296857 1637369139234321675972643)
                      ·
                        rfl

theorem cell23_3188765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_3188765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188765 prefixEnd_3188765 := by exact prefixLift 3188765
  have htrace : WordTrace (prefixWord ++ tailWord_3188765) baseStart_3188765 baseEnd_3188765 := by
    simpa [prefixWord, tailWord_3188765, baseEnd_3188765] using wordTrace_append hprefix tailTrace_3188765
  have hstable : (prefixWord ++ tailWord_3188765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188765).length < 2 ^ (prefixWord ++ tailWord_3188765).sum := by decide
  have hdescent : baseEnd_3188765 < baseStart_3188765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188829 : List Nat := [1, 4, 4, 1, 1, 2, 2, 2, 2, 2, 2]
def baseStart_3188829 : Nat := 118140960795 + 3188829 * 2 ^ 59
def prefixEnd_3188829 : Nat := 4983230072969 + 3 ^ 40 * 3188829 * 2
def baseEnd_3188829 : Nat := 1637402001996209425572349

theorem tailTrace_3188829 : CollatzResearch.WordTrace tailWord_3188829 prefixEnd_3188829 1637402001996209425572349 := by
  unfold tailWord_3188829
  simp only [CollatzResearch.WordTrace]
  refine ⟨116306148564424616479801541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77537432376283077653201027 116306148564424616479801541)
  ·
    refine ⟨21807402855829615589962789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116306148564424616479801541 21807402855829615589962789)
    ·
      refine ⟨4088888035468052923118023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21807402855829615589962789 4088888035468052923118023)
      ·
        refine ⟨6133332053202079384677035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4088888035468052923118023 6133332053202079384677035)
        ·
          refine ⟨9199998079803119077015553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133332053202079384677035 9199998079803119077015553)
          ·
            refine ⟨6899998559852339307761665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9199998079803119077015553 6899998559852339307761665)
            ·
              refine ⟨5174998919889254480821249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6899998559852339307761665 5174998919889254480821249)
              ·
                refine ⟨3881249189916940860615937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5174998919889254480821249 3881249189916940860615937)
                ·
                  refine ⟨2910936892437705645461953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3881249189916940860615937 2910936892437705645461953)
                  ·
                    refine ⟨2183202669328279234096465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2910936892437705645461953 2183202669328279234096465)
                    ·
                      refine ⟨1637402001996209425572349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183202669328279234096465 1637402001996209425572349)
                      ·
                        rfl

theorem cell23_3188829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_3188829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188829 prefixEnd_3188829 := by exact prefixLift 3188829
  have htrace : WordTrace (prefixWord ++ tailWord_3188829) baseStart_3188829 baseEnd_3188829 := by
    simpa [prefixWord, tailWord_3188829, baseEnd_3188829] using wordTrace_append hprefix tailTrace_3188829
  have hstable : (prefixWord ++ tailWord_3188829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188829).length < 2 ^ (prefixWord ++ tailWord_3188829).sum := by decide
  have hdescent : baseEnd_3188829 < baseStart_3188829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188865 : List Nat := [1, 2, 4, 2, 3, 2, 1, 1, 2, 5]
def baseStart_3188865 : Nat := 118140960795 + 3188865 * 2 ^ 59
def prefixEnd_3188865 : Nat := 4983230072969 + 3 ^ 40 * 3188865 * 2
def baseEnd_3188865 : Nat := 545806829099923761574061

theorem tailTrace_3188865 : CollatzResearch.WordTrace tailWord_3188865 prefixEnd_3188865 545806829099923761574061 := by
  unfold tailWord_3188865
  simp only [CollatzResearch.WordTrace]
  refine ⟨116307461592294194628112049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77538307728196129752074699 116307461592294194628112049)
  ·
    refine ⟨87230596194220645971084037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116307461592294194628112049 87230596194220645971084037)
    ·
      refine ⟨16355736786416371119578257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87230596194220645971084037 16355736786416371119578257)
      ·
        refine ⟨12266802589812278339683693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16355736786416371119578257 12266802589812278339683693)
        ·
          refine ⟨4600050971179604377381385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12266802589812278339683693 4600050971179604377381385)
          ·
            refine ⟨3450038228384703283036039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4600050971179604377381385 3450038228384703283036039)
            ·
              refine ⟨5175057342577054924554059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450038228384703283036039 5175057342577054924554059)
              ·
                refine ⟨7762586013865582386831089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175057342577054924554059 7762586013865582386831089)
                ·
                  refine ⟨5821939510399186790123317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7762586013865582386831089 5821939510399186790123317)
                  ·
                    refine ⟨545806829099923761574061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5821939510399186790123317 545806829099923761574061)
                    ·
                      rfl

theorem cell23_3188865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_3188865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188865 prefixEnd_3188865 := by exact prefixLift 3188865
  have htrace : WordTrace (prefixWord ++ tailWord_3188865) baseStart_3188865 baseEnd_3188865 := by
    simpa [prefixWord, tailWord_3188865, baseEnd_3188865] using wordTrace_append hprefix tailTrace_3188865
  have hstable : (prefixWord ++ tailWord_3188865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188865).length < 2 ^ (prefixWord ++ tailWord_3188865).sum := by decide
  have hdescent : baseEnd_3188865 < baseStart_3188865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188868 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 6, 2]
def baseStart_3188868 : Nat := 118140960795 + 3188868 * 2 ^ 59
def prefixEnd_3188868 : Nat := 4983230072969 + 3 ^ 40 * 3188868 * 2
def baseEnd_3188868 : Nat := 1637422027741734772984669

theorem tailTrace_3188868 : CollatzResearch.WordTrace tailWord_3188868 prefixEnd_3188868 1637422027741734772984669 := by
  unfold tailWord_3188868
  simp only [CollatzResearch.WordTrace]
  refine ⟨58153785505641663070235629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77538380674188884093647505 58153785505641663070235629)
  ·
    refine ⟨21807669564615623651338361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58153785505641663070235629 21807669564615623651338361)
    ·
      refine ⟨16355752173461717738503771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21807669564615623651338361 16355752173461717738503771)
      ·
        refine ⟨24533628260192576607755657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16355752173461717738503771 24533628260192576607755657)
        ·
          refine ⟨18400221195144432455816743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24533628260192576607755657 18400221195144432455816743)
          ·
            refine ⟨27600331792716648683725115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18400221195144432455816743 27600331792716648683725115)
            ·
              refine ⟨41400497689074973025587673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27600331792716648683725115 41400497689074973025587673)
              ·
                refine ⟨31050373266806229769190755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41400497689074973025587673 31050373266806229769190755)
                ·
                  refine ⟨46575559900209344653786133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31050373266806229769190755 46575559900209344653786133)
                  ·
                    refine ⟨2183229370322313030646225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46575559900209344653786133 2183229370322313030646225)
                    ·
                      refine ⟨1637422027741734772984669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183229370322313030646225 1637422027741734772984669)
                      ·
                        rfl

theorem cell23_3188868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_3188868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188868 prefixEnd_3188868 := by exact prefixLift 3188868
  have htrace : WordTrace (prefixWord ++ tailWord_3188868) baseStart_3188868 baseEnd_3188868 := by
    simpa [prefixWord, tailWord_3188868, baseEnd_3188868] using wordTrace_append hprefix tailTrace_3188868
  have hstable : (prefixWord ++ tailWord_3188868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188868).length < 2 ^ (prefixWord ++ tailWord_3188868).sum := by decide
  have hdescent : baseEnd_3188868 < baseStart_3188868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188895 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 3, 4]
def baseStart_3188895 : Nat := 118140960795 + 3188895 * 2 ^ 59
def prefixEnd_3188895 : Nat := 4983230072969 + 3 ^ 40 * 3188895 * 2
def baseEnd_3188895 : Nat := 545811963906468722449015

theorem tailTrace_3188895 : CollatzResearch.WordTrace tailWord_3188895 prefixEnd_3188895 545811963906468722449015 := by
  unfold tailWord_3188895
  simp only [CollatzResearch.WordTrace]
  refine ⟨116308555782185509751704139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77539037188123673167802759 116308555782185509751704139)
  ·
    refine ⟨174462833673278264627556209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116308555782185509751704139 174462833673278264627556209)
    ·
      refine ⟨130847125254958698470667157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174462833673278264627556209 130847125254958698470667157)
      ·
        refine ⟨6133458996326188990812523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 130847125254958698470667157 6133458996326188990812523)
        ·
          refine ⟨9200188494489283486218785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133458996326188990812523 9200188494489283486218785)
          ·
            refine ⟨6900141370866962614664089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9200188494489283486218785 6900141370866962614664089)
            ·
              refine ⟨5175106028150221960998067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6900141370866962614664089 5175106028150221960998067)
              ·
                refine ⟨7762659042225332941497101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175106028150221960998067 7762659042225332941497101)
                ·
                  refine ⟨2910997140834499853061413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7762659042225332941497101 2910997140834499853061413)
                  ·
                    refine ⟨545811963906468722449015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2910997140834499853061413 545811963906468722449015)
                    ·
                      rfl

theorem cell23_3188895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 3, 4].length) (baseStart_3188895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188895 prefixEnd_3188895 := by exact prefixLift 3188895
  have htrace : WordTrace (prefixWord ++ tailWord_3188895) baseStart_3188895 baseEnd_3188895 := by
    simpa [prefixWord, tailWord_3188895, baseEnd_3188895] using wordTrace_append hprefix tailTrace_3188895
  have hstable : (prefixWord ++ tailWord_3188895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188895).length < 2 ^ (prefixWord ++ tailWord_3188895).sum := by decide
  have hdescent : baseEnd_3188895 < baseStart_3188895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188938 : List Nat := [3, 1, 2, 1, 3, 1, 1, 5, 1, 5]
def baseStart_3188938 : Nat := 118140960795 + 3188938 * 2 ^ 59
def prefixEnd_3188938 : Nat := 4983230072969 + 3 ^ 40 * 3188938 * 2
def baseEnd_3188938 : Nat := 545819323795849833036449

theorem tailTrace_3188938 : CollatzResearch.WordTrace tailWord_3188938 prefixEnd_3188938 545819323795849833036449 := by
  unfold tailWord_3188938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29077531030257432023879867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77540082747353152063679645 29077531030257432023879867)
  ·
    refine ⟨43616296545386148035819801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29077531030257432023879867 43616296545386148035819801)
    ·
      refine ⟨32712222409039611026864851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43616296545386148035819801 32712222409039611026864851)
      ·
        refine ⟨49068333613559416540297277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32712222409039611026864851 49068333613559416540297277)
        ·
          refine ⟨18400625105084781202611479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49068333613559416540297277 18400625105084781202611479)
          ·
            refine ⟨27600937657627171803917219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18400625105084781202611479 27600937657627171803917219)
            ·
              refine ⟨41401406486440757705875829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27600937657627171803917219 41401406486440757705875829)
              ·
                refine ⟨3881381858103821034925859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41401406486440757705875829 3881381858103821034925859)
                ·
                  refine ⟨5822072787155731552388789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881381858103821034925859 5822072787155731552388789)
                  ·
                    refine ⟨545819323795849833036449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5822072787155731552388789 545819323795849833036449)
                    ·
                      rfl

theorem cell23_3188938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 5, 1, 5].length) (baseStart_3188938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188938 prefixEnd_3188938 := by exact prefixLift 3188938
  have htrace : WordTrace (prefixWord ++ tailWord_3188938) baseStart_3188938 baseEnd_3188938 := by
    simpa [prefixWord, tailWord_3188938, baseEnd_3188938] using wordTrace_append hprefix tailTrace_3188938
  have hstable : (prefixWord ++ tailWord_3188938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188938).length < 2 ^ (prefixWord ++ tailWord_3188938).sum := by decide
  have hdescent : baseEnd_3188938 < baseStart_3188938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188952 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 3, 1, 3]
def baseStart_3188952 : Nat := 118140960795 + 3188952 * 2 ^ 59
def prefixEnd_3188952 : Nat := 4983230072969 + 3 ^ 40 * 3188952 * 2
def baseEnd_3188952 : Nat := 1637465160116712444334283

theorem tailTrace_3188952 : CollatzResearch.WordTrace tailWord_3188952 prefixEnd_3188952 1637465160116712444334283 := by
  unfold tailWord_3188952
  simp only [CollatzResearch.WordTrace]
  refine ⟨58155317371489504243264555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77540423161986005657686073 58155317371489504243264555)
  ·
    refine ⟨87232976057234256364896833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58155317371489504243264555 87232976057234256364896833)
    ·
      refine ⟨65424732042925692273672625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87232976057234256364896833 65424732042925692273672625)
      ·
        refine ⟨49068549032194269205254469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65424732042925692273672625 49068549032194269205254469)
        ·
          refine ⟨9200352943536425475985213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49068549032194269205254469 9200352943536425475985213)
          ·
            refine ⟨3450132353826159553494455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9200352943536425475985213 3450132353826159553494455)
            ·
              refine ⟨5175198530739239330241683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450132353826159553494455 5175198530739239330241683)
              ·
                refine ⟨7762797796108858995362525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175198530739239330241683 7762797796108858995362525)
                ·
                  refine ⟨2911049173540822123260947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7762797796108858995362525 2911049173540822123260947)
                  ·
                    refine ⟨4366573760311233184891421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2911049173540822123260947 4366573760311233184891421)
                    ·
                      refine ⟨1637465160116712444334283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4366573760311233184891421 1637465160116712444334283)
                      ·
                        rfl

theorem cell23_3188952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 3, 1, 3].length) (baseStart_3188952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188952 prefixEnd_3188952 := by exact prefixLift 3188952
  have htrace : WordTrace (prefixWord ++ tailWord_3188952) baseStart_3188952 baseEnd_3188952 := by
    simpa [prefixWord, tailWord_3188952, baseEnd_3188952] using wordTrace_append hprefix tailTrace_3188952
  have hstable : (prefixWord ++ tailWord_3188952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188952).length < 2 ^ (prefixWord ++ tailWord_3188952).sum := by decide
  have hdescent : baseEnd_3188952 < baseStart_3188952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188971 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6]
def baseStart_3188971 : Nat := 118140960795 + 3188971 * 2 ^ 59
def prefixEnd_3188971 : Nat := 4983230072969 + 3 ^ 40 * 3188971 * 2
def baseEnd_3188971 : Nat := 1637474916249147869996695

theorem tailTrace_3188971 : CollatzResearch.WordTrace tailWord_3188971 prefixEnd_3188971 1637474916249147869996695 := by
  unfold tailWord_3188971
  simp only [CollatzResearch.WordTrace]
  refine ⟨116311327729910174731470767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77540885153273449820980511 116311327729910174731470767)
  ·
    refine ⟨174466991594865262097206151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116311327729910174731470767 174466991594865262097206151)
    ·
      refine ⟨261700487392297893145809227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174466991594865262097206151 261700487392297893145809227)
      ·
        refine ⟨392550731088446839718713841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261700487392297893145809227 392550731088446839718713841)
        ·
          refine ⟨294413048316335129789035381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392550731088446839718713841 294413048316335129789035381)
          ·
            refine ⟨27601223279656418417722067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 294413048316335129789035381 27601223279656418417722067)
            ·
              refine ⟨41401834919484627626583101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27601223279656418417722067 41401834919484627626583101)
              ·
                refine ⟨15525688094806735359968663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41401834919484627626583101 15525688094806735359968663)
                ·
                  refine ⟨23288532142210103039952995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15525688094806735359968663 23288532142210103039952995)
                  ·
                    refine ⟨34932798213315154559929493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23288532142210103039952995 34932798213315154559929493)
                    ·
                      refine ⟨1637474916249147869996695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34932798213315154559929493 1637474916249147869996695)
                      ·
                        rfl

theorem cell23_3188971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 6].length) (baseStart_3188971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188971 prefixEnd_3188971 := by exact prefixLift 3188971
  have htrace : WordTrace (prefixWord ++ tailWord_3188971) baseStart_3188971 baseEnd_3188971 := by
    simpa [prefixWord, tailWord_3188971, baseEnd_3188971] using wordTrace_append hprefix tailTrace_3188971
  have hstable : (prefixWord ++ tailWord_3188971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188971).length < 2 ^ (prefixWord ++ tailWord_3188971).sum := by decide
  have hdescent : baseEnd_3188971 < baseStart_3188971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188975 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 4]
def baseStart_3188975 : Nat := 118140960795 + 3188975 * 2 ^ 59
def prefixEnd_3188975 : Nat := 4983230072969 + 3 ^ 40 * 3188975 * 2
def baseEnd_3188975 : Nat := 1637476970171765854346677

theorem tailTrace_3188975 : CollatzResearch.WordTrace tailWord_3188975 prefixEnd_3188975 1637476970171765854346677 := by
  unfold tailWord_3188975
  simp only [CollatzResearch.WordTrace]
  refine ⟨116311473621895683414616379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77540982414597122276410919 116311473621895683414616379)
  ·
    refine ⟨174467210432843525121924569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116311473621895683414616379 174467210432843525121924569)
    ·
      refine ⟨130850407824632643841443427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174467210432843525121924569 130850407824632643841443427)
      ·
        refine ⟨196275611736948965762165141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130850407824632643841443427 196275611736948965762165141)
        ·
          refine ⟨9200419300169482770101491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196275611736948965762165141 9200419300169482770101491)
          ·
            refine ⟨13800628950254224155152237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200419300169482770101491 13800628950254224155152237)
            ·
              refine ⟨5175235856345334058182089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13800628950254224155152237 5175235856345334058182089)
              ·
                refine ⟨3881426892259000543636567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175235856345334058182089 3881426892259000543636567)
                ·
                  refine ⟨5822140338388500815454851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881426892259000543636567 5822140338388500815454851)
                  ·
                    refine ⟨8733210507582751223182277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5822140338388500815454851 8733210507582751223182277)
                    ·
                      refine ⟨1637476970171765854346677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8733210507582751223182277 1637476970171765854346677)
                      ·
                        rfl

theorem cell23_3188975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 1, 4].length) (baseStart_3188975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188975 prefixEnd_3188975 := by exact prefixLift 3188975
  have htrace : WordTrace (prefixWord ++ tailWord_3188975) baseStart_3188975 baseEnd_3188975 := by
    simpa [prefixWord, tailWord_3188975, baseEnd_3188975] using wordTrace_append hprefix tailTrace_3188975
  have hstable : (prefixWord ++ tailWord_3188975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188975).length < 2 ^ (prefixWord ++ tailWord_3188975).sum := by decide
  have hdescent : baseEnd_3188975 < baseStart_3188975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3188988 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_3188988 : Nat := 118140960795 + 3188988 * 2 ^ 59
def prefixEnd_3188988 : Nat := 4983230072969 + 3 ^ 40 * 3188988 * 2
def baseEnd_3188988 : Nat := 1637483645420274303484117

theorem tailTrace_3188988 : CollatzResearch.WordTrace tailWord_3188988 prefixEnd_3188988 1637483645420274303484117 := by
  unfold tailWord_3188988
  simp only [CollatzResearch.WordTrace]
  refine ⟨58155973885424293317419809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77541298513899057756559745 58155973885424293317419809)
  ·
    refine ⟨43616980414068219988064857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58155973885424293317419809 43616980414068219988064857)
    ·
      refine ⟨32712735310551164991048643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43616980414068219988064857 32712735310551164991048643)
      ·
        refine ⟨49069102965826747486572965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32712735310551164991048643 49069102965826747486572965)
        ·
          refine ⟨9200456806092515153732431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49069102965826747486572965 9200456806092515153732431)
          ·
            refine ⟨13800685209138772730598647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200456806092515153732431 13800685209138772730598647)
            ·
              refine ⟨20701027813708159095897971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13800685209138772730598647 20701027813708159095897971)
              ·
                refine ⟨31051541720562238643846957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20701027813708159095897971 31051541720562238643846957)
                ·
                  refine ⟨11644328145210839491442609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31051541720562238643846957 11644328145210839491442609)
                  ·
                    refine ⟨8733246108908129618581957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11644328145210839491442609 8733246108908129618581957)
                    ·
                      refine ⟨1637483645420274303484117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8733246108908129618581957 1637483645420274303484117)
                      ·
                        rfl

theorem cell23_3188988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_3188988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3188988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3188988 prefixEnd_3188988 := by exact prefixLift 3188988
  have htrace : WordTrace (prefixWord ++ tailWord_3188988) baseStart_3188988 baseEnd_3188988 := by
    simpa [prefixWord, tailWord_3188988, baseEnd_3188988] using wordTrace_append hprefix tailTrace_3188988
  have hstable : (prefixWord ++ tailWord_3188988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3188988).length < 2 ^ (prefixWord ++ tailWord_3188988).sum := by decide
  have hdescent : baseEnd_3188988 < baseStart_3188988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3188988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189009 : List Nat := [1, 2, 2, 1, 1, 6, 1, 4, 1, 2, 2]
def baseStart_3189009 : Nat := 118140960795 + 3189009 * 2 ^ 59
def prefixEnd_3189009 : Nat := 4983230072969 + 3 ^ 40 * 3189009 * 2
def baseEnd_3189009 : Nat := 1637494428514018721321521

theorem tailTrace_3189009 : CollatzResearch.WordTrace tailWord_3189009 prefixEnd_3189009 1637494428514018721321521 := by
  unfold tailWord_3189009
  simp only [CollatzResearch.WordTrace]
  refine ⟨116312713703772507221354081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77541809135848338147569387 116312713703772507221354081)
  ·
    refine ⟨87234535277829380416015561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116312713703772507221354081 87234535277829380416015561)
    ·
      refine ⟨65425901458372035312011671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87234535277829380416015561 65425901458372035312011671)
      ·
        refine ⟨98138852187558052968017507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65425901458372035312011671 98138852187558052968017507)
        ·
          refine ⟨147208278281337079452026261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98138852187558052968017507 147208278281337079452026261)
          ·
            refine ⟨6900388044437675599313731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 147208278281337079452026261 6900388044437675599313731)
            ·
              refine ⟨10350582066656513398970597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900388044437675599313731 10350582066656513398970597)
              ·
                refine ⟨1940734137498096262306987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10350582066656513398970597 1940734137498096262306987)
                ·
                  refine ⟨2911101206247144393460481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940734137498096262306987 2911101206247144393460481)
                  ·
                    refine ⟨2183325904685358295095361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2911101206247144393460481 2183325904685358295095361)
                    ·
                      refine ⟨1637494428514018721321521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183325904685358295095361 1637494428514018721321521)
                      ·
                        rfl

theorem cell23_3189009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 1, 4, 1, 2, 2].length) (baseStart_3189009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189009 prefixEnd_3189009 := by exact prefixLift 3189009
  have htrace : WordTrace (prefixWord ++ tailWord_3189009) baseStart_3189009 baseEnd_3189009 := by
    simpa [prefixWord, tailWord_3189009, baseEnd_3189009] using wordTrace_append hprefix tailTrace_3189009
  have hstable : (prefixWord ++ tailWord_3189009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189009).length < 2 ^ (prefixWord ++ tailWord_3189009).sum := by decide
  have hdescent : baseEnd_3189009 < baseStart_3189009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189022 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3189022 : Nat := 118140960795 + 3189022 * 2 ^ 59
def prefixEnd_3189022 : Nat := 4983230072969 + 3 ^ 40 * 3189022 * 2
def baseEnd_3189022 : Nat := 1637501103762527170458961

theorem tailTrace_3189022 : CollatzResearch.WordTrace tailWord_3189022 prefixEnd_3189022 1637501103762527170458961 := by
  unfold tailWord_3189022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14539148481590676305197165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77542125235150273627718213 14539148481590676305197165)
  ·
    refine ⟨5452180680596503614448937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14539148481590676305197165 5452180680596503614448937)
    ·
      refine ⟨4089135510447377710836703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5452180680596503614448937 4089135510447377710836703)
      ·
        refine ⟨6133703265671066566255055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4089135510447377710836703 6133703265671066566255055)
        ·
          refine ⟨9200554898506599849382583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6133703265671066566255055 9200554898506599849382583)
          ·
            refine ⟨13800832347759899774073875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9200554898506599849382583 13800832347759899774073875)
            ·
              refine ⟨20701248521639849661110813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13800832347759899774073875 20701248521639849661110813)
              ·
                refine ⟨7762968195614943622916555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20701248521639849661110813 7762968195614943622916555)
                ·
                  refine ⟨11644452293422415434374833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7762968195614943622916555 11644452293422415434374833)
                  ·
                    refine ⟨8733339220066811575781125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11644452293422415434374833 8733339220066811575781125)
                    ·
                      refine ⟨1637501103762527170458961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8733339220066811575781125 1637501103762527170458961)
                      ·
                        rfl

theorem cell23_3189022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3189022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189022 prefixEnd_3189022 := by exact prefixLift 3189022
  have htrace : WordTrace (prefixWord ++ tailWord_3189022) baseStart_3189022 baseEnd_3189022 := by
    simpa [prefixWord, tailWord_3189022, baseEnd_3189022] using wordTrace_append hprefix tailTrace_3189022
  have hstable : (prefixWord ++ tailWord_3189022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189022).length < 2 ^ (prefixWord ++ tailWord_3189022).sum := by decide
  have hdescent : baseEnd_3189022 < baseStart_3189022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189052 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_3189052 : Nat := 118140960795 + 3189052 * 2 ^ 59
def prefixEnd_3189052 : Nat := 4983230072969 + 3 ^ 40 * 3189052 * 2
def baseEnd_3189052 : Nat := 1637516508182162053083823

theorem tailTrace_3189052 : CollatzResearch.WordTrace tailWord_3189052 prefixEnd_3189052 1637516508182162053083823 := by
  unfold tailWord_3189052
  simp only [CollatzResearch.WordTrace]
  refine ⟨58157141021308362782584705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77542854695077817043446273 58157141021308362782584705)
  ·
    refine ⟨43617855765981272086938529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58157141021308362782584705 43617855765981272086938529)
    ·
      refine ⟨32713391824485954065203897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43617855765981272086938529 32713391824485954065203897)
      ·
        refine ⟨24535043868364465548902923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32713391824485954065203897 24535043868364465548902923)
        ·
          refine ⟨36802565802546698323354385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24535043868364465548902923 36802565802546698323354385)
          ·
            refine ⟨27601924351910023742515789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36802565802546698323354385 27601924351910023742515789)
            ·
              refine ⟨10350721631966258903443421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27601924351910023742515789 10350721631966258903443421)
              ·
                refine ⟨3881520611987347088791283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10350721631966258903443421 3881520611987347088791283)
                ·
                  refine ⟨5822280917981020633186925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3881520611987347088791283 5822280917981020633186925)
                  ·
                    refine ⟨2183355344242882737445097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5822280917981020633186925 2183355344242882737445097)
                    ·
                      refine ⟨1637516508182162053083823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183355344242882737445097 1637516508182162053083823)
                      ·
                        rfl

theorem cell23_3189052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_3189052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189052 prefixEnd_3189052 := by exact prefixLift 3189052
  have htrace : WordTrace (prefixWord ++ tailWord_3189052) baseStart_3189052 baseEnd_3189052 := by
    simpa [prefixWord, tailWord_3189052, baseEnd_3189052] using wordTrace_append hprefix tailTrace_3189052
  have hstable : (prefixWord ++ tailWord_3189052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189052).length < 2 ^ (prefixWord ++ tailWord_3189052).sum := by decide
  have hdescent : baseEnd_3189052 < baseStart_3189052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189125 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 2, 5, 2]
def baseStart_3189125 : Nat := 118140960795 + 3189125 * 2 ^ 59
def prefixEnd_3189125 : Nat := 4983230072969 + 3 ^ 40 * 3189125 * 2
def baseEnd_3189125 : Nat := 1637553992269940267470987

theorem tailTrace_3189125 : CollatzResearch.WordTrace tailWord_3189125 prefixEnd_3189125 1637553992269940267470987 := by
  unfold tailWord_3189125
  simp only [CollatzResearch.WordTrace]
  refine ⟨116316944571352259032576829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77544629714234839355051219 116316944571352259032576829)
  ·
    refine ⟨43618854214257097137216311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116316944571352259032576829 43618854214257097137216311)
    ·
      refine ⟨65428281321385645705824467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43618854214257097137216311 65428281321385645705824467)
      ·
        refine ⟨98142421982078468558736701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65428281321385645705824467 98142421982078468558736701)
        ·
          refine ⟨36803408243279425709526263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98142421982078468558736701 36803408243279425709526263)
          ·
            refine ⟨55205112364919138564289395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36803408243279425709526263 55205112364919138564289395)
            ·
              refine ⟨82807668547378707846434093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55205112364919138564289395 82807668547378707846434093)
              ·
                refine ⟨31052875705267015442412785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82807668547378707846434093 31052875705267015442412785)
                ·
                  refine ⟨23289656778950261581809589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31052875705267015442412785 23289656778950261581809589)
                  ·
                    refine ⟨2183405323026587023294649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23289656778950261581809589 2183405323026587023294649)
                    ·
                      refine ⟨1637553992269940267470987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183405323026587023294649 1637553992269940267470987)
                      ·
                        rfl

theorem cell23_3189125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_3189125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189125 prefixEnd_3189125 := by exact prefixLift 3189125
  have htrace : WordTrace (prefixWord ++ tailWord_3189125) baseStart_3189125 baseEnd_3189125 := by
    simpa [prefixWord, tailWord_3189125, baseEnd_3189125] using wordTrace_append hprefix tailTrace_3189125
  have hstable : (prefixWord ++ tailWord_3189125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189125).length < 2 ^ (prefixWord ++ tailWord_3189125).sum := by decide
  have hdescent : baseEnd_3189125 < baseStart_3189125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189155 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 4]
def baseStart_3189155 : Nat := 118140960795 + 3189155 * 2 ^ 59
def prefixEnd_3189155 : Nat := 4983230072969 + 3 ^ 40 * 3189155 * 2
def baseEnd_3189155 : Nat := 1637569396689575150095849

theorem tailTrace_3189155 : CollatzResearch.WordTrace tailWord_3189155 prefixEnd_3189155 1637569396689575150095849 := by
  unfold tailWord_3189155
  simp only [CollatzResearch.WordTrace]
  refine ⟨116318038761243574156168919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77545359174162382770779279 116318038761243574156168919)
  ·
    refine ⟨174477058141865361234253379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116318038761243574156168919 174477058141865361234253379)
    ·
      refine ⟨261715587212798041851380069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174477058141865361234253379 261715587212798041851380069)
      ·
        refine ⟨49071672602399632847133763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261715587212798041851380069 49071672602399632847133763)
        ·
          refine ⟨73607508903599449270700645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49071672602399632847133763 73607508903599449270700645)
          ·
            refine ⟨13801407919424896738256371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73607508903599449270700645 13801407919424896738256371)
            ·
              refine ⟨20702111879137345107384557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13801407919424896738256371 20702111879137345107384557)
              ·
                refine ⟨7763291954676504415269209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20702111879137345107384557 7763291954676504415269209)
                ·
                  refine ⟨5822468966007378311451907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7763291954676504415269209 5822468966007378311451907)
                  ·
                    refine ⟨8733703449011067467177861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5822468966007378311451907 8733703449011067467177861)
                    ·
                      refine ⟨1637569396689575150095849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8733703449011067467177861 1637569396689575150095849)
                      ·
                        rfl

theorem cell23_3189155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_3189155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189155 prefixEnd_3189155 := by exact prefixLift 3189155
  have htrace : WordTrace (prefixWord ++ tailWord_3189155) baseStart_3189155 baseEnd_3189155 := by
    simpa [prefixWord, tailWord_3189155, baseEnd_3189155] using wordTrace_append hprefix tailTrace_3189155
  have hstable : (prefixWord ++ tailWord_3189155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189155).length < 2 ^ (prefixWord ++ tailWord_3189155).sum := by decide
  have hdescent : baseEnd_3189155 < baseStart_3189155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189168 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4]
def baseStart_3189168 : Nat := 118140960795 + 3189168 * 2 ^ 59
def prefixEnd_3189168 : Nat := 4983230072969 + 3 ^ 40 * 3189168 * 2
def baseEnd_3189168 : Nat := 1637576071938083599233289

theorem tailTrace_3189168 : CollatzResearch.WordTrace tailWord_3189168 prefixEnd_3189168 1637576071938083599233289 := by
  unfold tailWord_3189168
  simp only [CollatzResearch.WordTrace]
  refine ⟨58159256455098238688196079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77545675273464318250928105 58159256455098238688196079)
  ·
    refine ⟨87238884682647358032294119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58159256455098238688196079 87238884682647358032294119)
    ·
      refine ⟨130858327023971037048441179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87238884682647358032294119 130858327023971037048441179)
      ·
        refine ⟨196287490535956555572661769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130858327023971037048441179 196287490535956555572661769)
        ·
          refine ⟨147215617901967416679496327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196287490535956555572661769 147215617901967416679496327)
          ·
            refine ⟨220823426852951125019244491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147215617901967416679496327 220823426852951125019244491)
            ·
              refine ⟨331235140279426687528866737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220823426852951125019244491 331235140279426687528866737)
              ·
                refine ⟨248426355209570015646650053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 331235140279426687528866737 248426355209570015646650053)
                ·
                  refine ⟨46579941601794377933746885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 248426355209570015646650053 46579941601794377933746885)
                  ·
                    refine ⟨8733739050336445862577541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46579941601794377933746885 8733739050336445862577541)
                    ·
                      refine ⟨1637576071938083599233289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8733739050336445862577541 1637576071938083599233289)
                      ·
                        rfl

theorem cell23_3189168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 4].length) (baseStart_3189168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189168 prefixEnd_3189168 := by exact prefixLift 3189168
  have htrace : WordTrace (prefixWord ++ tailWord_3189168) baseStart_3189168 baseEnd_3189168 := by
    simpa [prefixWord, tailWord_3189168, baseEnd_3189168] using wordTrace_append hprefix tailTrace_3189168
  have hstable : (prefixWord ++ tailWord_3189168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189168).length < 2 ^ (prefixWord ++ tailWord_3189168).sum := by decide
  have hdescent : baseEnd_3189168 < baseStart_3189168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189178 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 8]
def baseStart_3189178 : Nat := 118140960795 + 3189178 * 2 ^ 59
def prefixEnd_3189178 : Nat := 4983230072969 + 3 ^ 40 * 3189178 * 2
def baseEnd_3189178 : Nat := 181953467416069840012027

theorem tailTrace_3189178 : CollatzResearch.WordTrace tailWord_3189178 prefixEnd_3189178 181953467416069840012027 := by
  unfold tailWord_3189178
  simp only [CollatzResearch.WordTrace]
  refine ⟨29079719410040062271064047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77545918426773499389504125 29079719410040062271064047)
  ·
    refine ⟨43619579115060093406596071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29079719410040062271064047 43619579115060093406596071)
    ·
      refine ⟨65429368672590140109894107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43619579115060093406596071 65429368672590140109894107)
      ·
        refine ⟨98144053008885210164841161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65429368672590140109894107 98144053008885210164841161)
        ·
          refine ⟨73608039756663907623630871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98144053008885210164841161 73608039756663907623630871)
          ·
            refine ⟨110412059634995861435446307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73608039756663907623630871 110412059634995861435446307)
            ·
              refine ⟨165618089452493792153169461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110412059634995861435446307 165618089452493792153169461)
              ·
                refine ⟨15526695886171293014359637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165618089452493792153169461 15526695886171293014359637)
                ·
                  refine ⟨181953467416069840012027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15526695886171293014359637 181953467416069840012027)
                  ·
                    rfl

theorem cell23_3189178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 8].length) (baseStart_3189178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189178 prefixEnd_3189178 := by exact prefixLift 3189178
  have htrace : WordTrace (prefixWord ++ tailWord_3189178) baseStart_3189178 baseEnd_3189178 := by
    simpa [prefixWord, tailWord_3189178, baseEnd_3189178] using wordTrace_append hprefix tailTrace_3189178
  have hstable : (prefixWord ++ tailWord_3189178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189178).length < 2 ^ (prefixWord ++ tailWord_3189178).sum := by decide
  have hdescent : baseEnd_3189178 < baseStart_3189178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189229 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 6]
def baseStart_3189229 : Nat := 118140960795 + 3189229 * 2 ^ 59
def prefixEnd_3189229 : Nat := 4983230072969 + 3 ^ 40 * 3189229 * 2
def baseEnd_3189229 : Nat := 181956377139778651174501

theorem tailTrace_3189229 : CollatzResearch.WordTrace tailWord_3189229 prefixEnd_3189229 181956377139778651174501 := by
  unfold tailWord_3189229
  simp only [CollatzResearch.WordTrace]
  refine ⟨116320737762975484794362741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77547158508650323196241827 116320737762975484794362741)
  ·
    refine ⟨10905069165278951699471507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116320737762975484794362741 10905069165278951699471507)
    ·
      refine ⟨16357603747918427549207261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10905069165278951699471507 16357603747918427549207261)
      ·
        refine ⟨6134101405469410330952723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16357603747918427549207261 6134101405469410330952723)
        ·
          refine ⟨9201152108204115496429085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134101405469410330952723 9201152108204115496429085)
          ·
            refine ⟨3450432040576543311160907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9201152108204115496429085 3450432040576543311160907)
            ·
              refine ⟨5175648060864814966741361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450432040576543311160907 5175648060864814966741361)
              ·
                refine ⟨3881736045648611225056021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5175648060864814966741361 3881736045648611225056021)
                ·
                  refine ⟨181956377139778651174501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3881736045648611225056021 181956377139778651174501)
                  ·
                    rfl

theorem cell23_3189229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_3189229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189229 prefixEnd_3189229 := by exact prefixLift 3189229
  have htrace : WordTrace (prefixWord ++ tailWord_3189229) baseStart_3189229 baseEnd_3189229 := by
    simpa [prefixWord, tailWord_3189229, baseEnd_3189229] using wordTrace_append hprefix tailTrace_3189229
  have hstable : (prefixWord ++ tailWord_3189229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189229).length < 2 ^ (prefixWord ++ tailWord_3189229).sum := by decide
  have hdescent : baseEnd_3189229 < baseStart_3189229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189232 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 4, 3, 2]
def baseStart_3189232 : Nat := 118140960795 + 3189232 * 2 ^ 59
def prefixEnd_3189232 : Nat := 4983230072969 + 3 ^ 40 * 3189232 * 2
def baseEnd_3189232 : Nat := 1637608934699971348832995

theorem tailTrace_3189232 : CollatzResearch.WordTrace tailWord_3189232 prefixEnd_3189232 1637608934699971348832995 := by
  unfold tailWord_3189232
  simp only [CollatzResearch.WordTrace]
  refine ⟨58160423590982308153360975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77547231454643077537814633 58160423590982308153360975)
  ·
    refine ⟨87240635386473462230041463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58160423590982308153360975 87240635386473462230041463)
    ·
      refine ⟨130860953079710193345062195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87240635386473462230041463 130860953079710193345062195)
      ·
        refine ⟨196291429619565290017593293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130860953079710193345062195 196291429619565290017593293)
        ·
          refine ⟨73609286107336983756597485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196291429619565290017593293 73609286107336983756597485)
          ·
            refine ⟨27603482290251368908724057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73609286107336983756597485 27603482290251368908724057)
            ·
              refine ⟨20702611717688526681543043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27603482290251368908724057 20702611717688526681543043)
              ·
                refine ⟨31053917576532790022314565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20702611717688526681543043 31053917576532790022314565)
                ·
                  refine ⟨5822609545599898129183981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31053917576532790022314565 5822609545599898129183981)
                  ·
                    refine ⟨2183478579599961798443993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5822609545599898129183981 2183478579599961798443993)
                    ·
                      refine ⟨1637608934699971348832995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183478579599961798443993 1637608934699971348832995)
                      ·
                        rfl

theorem cell23_3189232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 3, 2].length) (baseStart_3189232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189232 prefixEnd_3189232 := by exact prefixLift 3189232
  have htrace : WordTrace (prefixWord ++ tailWord_3189232) baseStart_3189232 baseEnd_3189232 := by
    simpa [prefixWord, tailWord_3189232, baseEnd_3189232] using wordTrace_append hprefix tailTrace_3189232
  have hstable : (prefixWord ++ tailWord_3189232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189232).length < 2 ^ (prefixWord ++ tailWord_3189232).sum := by decide
  have hdescent : baseEnd_3189232 < baseStart_3189232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189272 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 4, 4]
def baseStart_3189272 : Nat := 118140960795 + 3189272 * 2 ^ 59
def prefixEnd_3189272 : Nat := 4983230072969 + 3 ^ 40 * 3189272 * 2
def baseEnd_3189272 : Nat := 545876491308717064110937

theorem tailTrace_3189272 : CollatzResearch.WordTrace tailWord_3189272 prefixEnd_3189272 545876491308717064110937 := by
  unfold tailWord_3189272
  simp only [CollatzResearch.WordTrace]
  refine ⟨58161153050909851569089035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77548204067879802092118713 58161153050909851569089035)
  ·
    refine ⟨87241729576364777353633553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58161153050909851569089035 87241729576364777353633553)
    ·
      refine ⟨65431297182273583015225165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87241729576364777353633553 65431297182273583015225165)
      ·
        refine ⟨24536736443352593630709437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65431297182273583015225165 24536736443352593630709437)
        ·
          refine ⟨9201276166257222611516039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24536736443352593630709437 9201276166257222611516039)
          ·
            refine ⟨13801914249385833917274059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9201276166257222611516039 13801914249385833917274059)
            ·
              refine ⟨20702871374078750875911089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13801914249385833917274059 20702871374078750875911089)
              ·
                refine ⟨15527153530559063156933317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20702871374078750875911089 15527153530559063156933317)
                ·
                  refine ⟨2911341286979824341924997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15527153530559063156933317 2911341286979824341924997)
                  ·
                    refine ⟨545876491308717064110937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2911341286979824341924997 545876491308717064110937)
                    ·
                      rfl

theorem cell23_3189272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 4, 4].length) (baseStart_3189272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189272 prefixEnd_3189272 := by exact prefixLift 3189272
  have htrace : WordTrace (prefixWord ++ tailWord_3189272) baseStart_3189272 baseEnd_3189272 := by
    simpa [prefixWord, tailWord_3189272, baseEnd_3189272] using wordTrace_append hprefix tailTrace_3189272
  have hstable : (prefixWord ++ tailWord_3189272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189272).length < 2 ^ (prefixWord ++ tailWord_3189272).sum := by decide
  have hdescent : baseEnd_3189272 < baseStart_3189272 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189282 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_3189282 : Nat := 118140960795 + 3189282 * 2 ^ 59
def prefixEnd_3189282 : Nat := 4983230072969 + 3 ^ 40 * 3189282 * 2
def baseEnd_3189282 : Nat := 1637634608732696153207765

theorem tailTrace_3189282 : CollatzResearch.WordTrace tailWord_3189282 prefixEnd_3189282 1637634608732696153207765 := by
  unfold tailWord_3189282
  simp only [CollatzResearch.WordTrace]
  refine ⟨29080667707945868711510525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77548447221188983230694733 29080667707945868711510525)
  ·
    refine ⟨10905250390479700766816447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29080667707945868711510525 10905250390479700766816447)
    ·
      refine ⟨16357875585719551150224671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10905250390479700766816447 16357875585719551150224671)
      ·
        refine ⟨24536813378579326725337007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16357875585719551150224671 24536813378579326725337007)
        ·
          refine ⟨36805220067868990088005511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24536813378579326725337007 36805220067868990088005511)
          ·
            refine ⟨55207830101803485132008267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36805220067868990088005511 55207830101803485132008267)
            ·
              refine ⟨82811745152705227698012401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55207830101803485132008267 82811745152705227698012401)
              ·
                refine ⟨62108808864528920773509301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82811745152705227698012401 62108808864528920773509301)
                ·
                  refine ⟨5822700831049586322516497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62108808864528920773509301 5822700831049586322516497)
                  ·
                    refine ⟨4367025623287189741887373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5822700831049586322516497 4367025623287189741887373)
                    ·
                      refine ⟨1637634608732696153207765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4367025623287189741887373 1637634608732696153207765)
                      ·
                        rfl

theorem cell23_3189282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_3189282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189282 prefixEnd_3189282 := by exact prefixLift 3189282
  have htrace : WordTrace (prefixWord ++ tailWord_3189282) baseStart_3189282 baseEnd_3189282 := by
    simpa [prefixWord, tailWord_3189282, baseEnd_3189282] using wordTrace_append hprefix tailTrace_3189282
  have hstable : (prefixWord ++ tailWord_3189282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189282).length < 2 ^ (prefixWord ++ tailWord_3189282).sum := by decide
  have hdescent : baseEnd_3189282 < baseStart_3189282 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189296 : List Nat := [2, 1, 1, 1, 2, 3, 2, 6, 1, 2, 2]
def baseStart_3189296 : Nat := 118140960795 + 3189296 * 2 ^ 59
def prefixEnd_3189296 : Nat := 4983230072969 + 3 ^ 40 * 3189296 * 2
def baseEnd_3189296 : Nat := 1637641797461859098432701

theorem tailTrace_3189296 : CollatzResearch.WordTrace tailWord_3189296 prefixEnd_3189296 1637641797461859098432701 := by
  unfold tailWord_3189296
  simp only [CollatzResearch.WordTrace]
  refine ⟨58161590726866377618525871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77548787635821836824701161 58161590726866377618525871)
  ·
    refine ⟨87242386090299566427788807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58161590726866377618525871 87242386090299566427788807)
    ·
      refine ⟨130863579135449349641683211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87242386090299566427788807 130863579135449349641683211)
      ·
        refine ⟨196295368703174024462524817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130863579135449349641683211 196295368703174024462524817)
        ·
          refine ⟨147221526527380518346893613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196295368703174024462524817 147221526527380518346893613)
          ·
            refine ⟨55208072447767694380085105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147221526527380518346893613 55208072447767694380085105)
            ·
              refine ⟨41406054335825770785063829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55208072447767694380085105 41406054335825770785063829)
              ·
                refine ⟨1940908796991833005549867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41406054335825770785063829 1940908796991833005549867)
                ·
                  refine ⟨2911363195487749508324801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1940908796991833005549867 2911363195487749508324801)
                  ·
                    refine ⟨2183522396615812131243601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2911363195487749508324801 2183522396615812131243601)
                    ·
                      refine ⟨1637641797461859098432701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183522396615812131243601 1637641797461859098432701)
                      ·
                        rfl

theorem cell23_3189296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 6, 1, 2, 2].length) (baseStart_3189296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189296 prefixEnd_3189296 := by exact prefixLift 3189296
  have htrace : WordTrace (prefixWord ++ tailWord_3189296) baseStart_3189296 baseEnd_3189296 := by
    simpa [prefixWord, tailWord_3189296, baseEnd_3189296] using wordTrace_append hprefix tailTrace_3189296
  have hstable : (prefixWord ++ tailWord_3189296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189296).length < 2 ^ (prefixWord ++ tailWord_3189296).sum := by decide
  have hdescent : baseEnd_3189296 < baseStart_3189296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189302 : List Nat := [5, 1, 2, 1, 2, 1, 1, 10]
def baseStart_3189302 : Nat := 118140960795 + 3189302 * 2 ^ 59
def prefixEnd_3189302 : Nat := 4983230072969 + 3 ^ 40 * 3189302 * 2
def baseEnd_3189302 : Nat := 60653514012806891665099

theorem tailTrace_3189302 : CollatzResearch.WordTrace tailWord_3189302 prefixEnd_3189302 60653514012806891665099 := by
  unfold tailWord_3189302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7270212518231938641360635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77548933527807345507846773 7270212518231938641360635)
  ·
    refine ⟨10905318777347907962040953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7270212518231938641360635 10905318777347907962040953)
    ·
      refine ⟨8178989083010930971530715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10905318777347907962040953 8178989083010930971530715)
      ·
        refine ⟨12268483624516396457296073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8178989083010930971530715 12268483624516396457296073)
        ·
          refine ⟨9201362718387297342972055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12268483624516396457296073 9201362718387297342972055)
          ·
            refine ⟨13802044077580946014458083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9201362718387297342972055 13802044077580946014458083)
            ·
              refine ⟨20703066116371419021687125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13802044077580946014458083 20703066116371419021687125)
              ·
                refine ⟨60653514012806891665099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20703066116371419021687125 60653514012806891665099)
                ·
                  rfl

theorem cell23_3189302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 10].length) (baseStart_3189302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189302 prefixEnd_3189302 := by exact prefixLift 3189302
  have htrace : WordTrace (prefixWord ++ tailWord_3189302) baseStart_3189302 baseEnd_3189302 := by
    simpa [prefixWord, tailWord_3189302, baseEnd_3189302] using wordTrace_append hprefix tailTrace_3189302
  have hstable : (prefixWord ++ tailWord_3189302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189302).length < 2 ^ (prefixWord ++ tailWord_3189302).sum := by decide
  have hdescent : baseEnd_3189302 < baseStart_3189302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189305 : List Nat := [1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 6]
def baseStart_3189305 : Nat := 118140960795 + 3189305 * 2 ^ 59
def prefixEnd_3189305 : Nat := 4983230072969 + 3 ^ 40 * 3189305 * 2
def baseEnd_3189305 : Nat := 1637646418787749563220159

theorem tailTrace_3189305 : CollatzResearch.WordTrace tailWord_3189305 prefixEnd_3189305 1637646418787749563220159 := by
  unfold tailWord_3189305
  simp only [CollatzResearch.WordTrace]
  refine ⟨116323509710700149774129369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77549006473800099849419579 116323509710700149774129369)
  ·
    refine ⟨87242632283025112330597027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116323509710700149774129369 87242632283025112330597027)
    ·
      refine ⟨130863948424537668495895541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87242632283025112330597027 130863948424537668495895541)
      ·
        refine ⟨12268495164800406421490207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130863948424537668495895541 12268495164800406421490207)
        ·
          refine ⟨18402742747200609632235311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268495164800406421490207 18402742747200609632235311)
          ·
            refine ⟨27604114120800914448352967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18402742747200609632235311 27604114120800914448352967)
            ·
              refine ⟨41406171181201371672529451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27604114120800914448352967 41406171181201371672529451)
              ·
                refine ⟨62109256771802057508794177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41406171181201371672529451 62109256771802057508794177)
                ·
                  refine ⟨46581942578851543131595633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62109256771802057508794177 46581942578851543131595633)
                  ·
                    refine ⟨34936456934138657348696725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46581942578851543131595633 34936456934138657348696725)
                    ·
                      refine ⟨1637646418787749563220159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34936456934138657348696725 1637646418787749563220159)
                      ·
                        rfl

theorem cell23_3189305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_3189305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189305 prefixEnd_3189305 := by exact prefixLift 3189305
  have htrace : WordTrace (prefixWord ++ tailWord_3189305) baseStart_3189305 baseEnd_3189305 := by
    simpa [prefixWord, tailWord_3189305, baseEnd_3189305] using wordTrace_append hprefix tailTrace_3189305
  have hstable : (prefixWord ++ tailWord_3189305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189305).length < 2 ^ (prefixWord ++ tailWord_3189305).sum := by decide
  have hdescent : baseEnd_3189305 < baseStart_3189305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189306 : List Nat := [3, 1, 1, 1, 3, 5, 2, 1, 2, 4]
def baseStart_3189306 : Nat := 118140960795 + 3189306 * 2 ^ 59
def prefixEnd_3189306 : Nat := 4983230072969 + 3 ^ 40 * 3189306 * 2
def baseEnd_3189306 : Nat := 545882310756134686435885

theorem tailTrace_3189306 : CollatzResearch.WordTrace tailWord_3189306 prefixEnd_3189306 545882310756134686435885 := by
  unfold tailWord_3189306
  simp only [CollatzResearch.WordTrace]
  refine ⟨29080886545924131736228943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77549030789131017963277181 29080886545924131736228943)
  ·
    refine ⟨43621329818886197604343415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29080886545924131736228943 43621329818886197604343415)
    ·
      refine ⟨65431994728329296406515123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43621329818886197604343415 65431994728329296406515123)
      ·
        refine ⟨98147992092493944609772685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65431994728329296406515123 98147992092493944609772685)
        ·
          refine ⟨36805497034685229228664757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98147992092493944609772685 36805497034685229228664757)
          ·
            refine ⟨3450515347001740240187321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36805497034685229228664757 3450515347001740240187321)
            ·
              refine ⟨2587886510251305180140491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3450515347001740240187321 2587886510251305180140491)
              ·
                refine ⟨3881829765376957770210737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2587886510251305180140491 3881829765376957770210737)
                ·
                  refine ⟨2911372324032718327658053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3881829765376957770210737 2911372324032718327658053)
                  ·
                    refine ⟨545882310756134686435885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2911372324032718327658053 545882310756134686435885)
                    ·
                      rfl

theorem cell23_3189306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 1, 2, 4].length) (baseStart_3189306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189306 prefixEnd_3189306 := by exact prefixLift 3189306
  have htrace : WordTrace (prefixWord ++ tailWord_3189306) baseStart_3189306 baseEnd_3189306 := by
    simpa [prefixWord, tailWord_3189306, baseEnd_3189306] using wordTrace_append hprefix tailTrace_3189306
  have hstable : (prefixWord ++ tailWord_3189306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189306).length < 2 ^ (prefixWord ++ tailWord_3189306).sum := by decide
  have hdescent : baseEnd_3189306 < baseStart_3189306 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189355 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5]
def baseStart_3189355 : Nat := 118140960795 + 3189355 * 2 ^ 59
def prefixEnd_3189355 : Nat := 4983230072969 + 3 ^ 40 * 3189355 * 2
def baseEnd_3189355 : Nat := 1637672092820474367594929

theorem tailTrace_3189355 : CollatzResearch.WordTrace tailWord_3189355 prefixEnd_3189355 1637672092820474367594929 := by
  unfold tailWord_3189355
  simp only [CollatzResearch.WordTrace]
  refine ⟨116325333360519008313449519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77550222240346005542299679 116325333360519008313449519)
  ·
    refine ⟨174488000040778512470174279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116325333360519008313449519 174488000040778512470174279)
    ·
      refine ⟨261732000061167768705261419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174488000040778512470174279 261732000061167768705261419)
      ·
        refine ⟨392598000091751653057892129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261732000061167768705261419 392598000091751653057892129)
        ·
          refine ⟨294448500068813739793419097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392598000091751653057892129 294448500068813739793419097)
          ·
            refine ⟨220836375051610304845064323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 294448500068813739793419097 220836375051610304845064323)
            ·
              refine ⟨331254562577415457267596485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220836375051610304845064323 331254562577415457267596485)
              ·
                refine ⟨62110230483265398237674341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 331254562577415457267596485 62110230483265398237674341)
                ·
                  refine ⟨11645668215612262169563939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62110230483265398237674341 11645668215612262169563939)
                  ·
                    refine ⟨17468502323418393254345909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11645668215612262169563939 17468502323418393254345909)
                    ·
                      refine ⟨1637672092820474367594929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17468502323418393254345909 1637672092820474367594929)
                      ·
                        rfl

theorem cell23_3189355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 5].length) (baseStart_3189355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189355 prefixEnd_3189355 := by exact prefixLift 3189355
  have htrace : WordTrace (prefixWord ++ tailWord_3189355) baseStart_3189355 baseEnd_3189355 := by
    simpa [prefixWord, tailWord_3189355, baseEnd_3189355] using wordTrace_append hprefix tailTrace_3189355
  have hstable : (prefixWord ++ tailWord_3189355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189355).length < 2 ^ (prefixWord ++ tailWord_3189355).sum := by decide
  have hdescent : baseEnd_3189355 < baseStart_3189355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189369 : List Nat := [1, 2, 1, 3, 3, 2, 1, 3, 1, 4, 2]
def baseStart_3189369 : Nat := 118140960795 + 3189369 * 2 ^ 59
def prefixEnd_3189369 : Nat := 4983230072969 + 3 ^ 40 * 3189369 * 2
def baseEnd_3189369 : Nat := 1637679281549637312819865

theorem tailTrace_3189369 : CollatzResearch.WordTrace tailWord_3189369 prefixEnd_3189369 1637679281549637312819865 := by
  unfold tailWord_3189369
  simp only [CollatzResearch.WordTrace]
  refine ⟨116325843982468288704459161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77550562654978859136306107 116325843982468288704459161)
  ·
    refine ⟨87244382986851216528344371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116325843982468288704459161 87244382986851216528344371)
    ·
      refine ⟨130866574480276824792516557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87244382986851216528344371 130866574480276824792516557)
      ·
        refine ⟨49074965430103809297193709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130866574480276824792516557 49074965430103809297193709)
        ·
          refine ⟨18403112036288928486447641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49074965430103809297193709 18403112036288928486447641)
          ·
            refine ⟨13802334027216696364835731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18403112036288928486447641 13802334027216696364835731)
            ·
              refine ⟨20703501040825044547253597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13802334027216696364835731 20703501040825044547253597)
              ·
                refine ⟨7763812890309391705220099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20703501040825044547253597 7763812890309391705220099)
                ·
                  refine ⟨11645719335464087557830149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7763812890309391705220099 11645719335464087557830149)
                  ·
                    refine ⟨2183572375399516417093153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11645719335464087557830149 2183572375399516417093153)
                    ·
                      refine ⟨1637679281549637312819865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183572375399516417093153 1637679281549637312819865)
                      ·
                        rfl

theorem cell23_3189369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 3, 1, 4, 2].length) (baseStart_3189369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189369 prefixEnd_3189369 := by exact prefixLift 3189369
  have htrace : WordTrace (prefixWord ++ tailWord_3189369) baseStart_3189369 baseEnd_3189369 := by
    simpa [prefixWord, tailWord_3189369, baseEnd_3189369] using wordTrace_append hprefix tailTrace_3189369
  have hstable : (prefixWord ++ tailWord_3189369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189369).length < 2 ^ (prefixWord ++ tailWord_3189369).sum := by decide
  have hdescent : baseEnd_3189369 < baseStart_3189369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189385 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 7]
def baseStart_3189385 : Nat := 118140960795 + 3189385 * 2 ^ 59
def prefixEnd_3189385 : Nat := 4983230072969 + 3 ^ 40 * 3189385 * 2
def baseEnd_3189385 : Nat := 1637687497240109250219791

theorem tailTrace_3189385 : CollatzResearch.WordTrace tailWord_3189385 prefixEnd_3189385 1637687497240109250219791 := by
  unfold tailWord_3189385
  simp only [CollatzResearch.WordTrace]
  refine ⟨116326427550410323437041609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77550951700273548958027739 116326427550410323437041609)
  ·
    refine ⟨87244820662807742577781207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116326427550410323437041609 87244820662807742577781207)
    ·
      refine ⟨130867230994211613866671811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87244820662807742577781207 130867230994211613866671811)
      ·
        refine ⟨196300846491317420800007717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130867230994211613866671811 196300846491317420800007717)
        ·
          refine ⟨36806408717122016400001447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196300846491317420800007717 36806408717122016400001447)
          ·
            refine ⟨55209613075683024600002171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36806408717122016400001447 55209613075683024600002171)
            ·
              refine ⟨82814419613524536900003257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55209613075683024600002171 82814419613524536900003257)
              ·
                refine ⟨62110814710143402675002443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82814419613524536900003257 62110814710143402675002443)
                ·
                  refine ⟨93166222065215104012503665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62110814710143402675002443 93166222065215104012503665)
                  ·
                    refine ⟨69874666548911328009377749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93166222065215104012503665 69874666548911328009377749)
                    ·
                      refine ⟨1637687497240109250219791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69874666548911328009377749 1637687497240109250219791)
                      ·
                        rfl

theorem cell23_3189385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_3189385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189385 prefixEnd_3189385 := by exact prefixLift 3189385
  have htrace : WordTrace (prefixWord ++ tailWord_3189385) baseStart_3189385 baseEnd_3189385 := by
    simpa [prefixWord, tailWord_3189385, baseEnd_3189385] using wordTrace_append hprefix tailTrace_3189385
  have hstable : (prefixWord ++ tailWord_3189385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189385).length < 2 ^ (prefixWord ++ tailWord_3189385).sum := by decide
  have hdescent : baseEnd_3189385 < baseStart_3189385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189409 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 7]
def baseStart_3189409 : Nat := 118140960795 + 3189409 * 2 ^ 59
def prefixEnd_3189409 : Nat := 4983230072969 + 3 ^ 40 * 3189409 * 2
def baseEnd_3189409 : Nat := 181966646752868572924409

theorem tailTrace_3189409 : CollatzResearch.WordTrace tailWord_3189409 prefixEnd_3189409 181966646752868572924409 := by
  unfold tailWord_3189409
  simp only [CollatzResearch.WordTrace]
  refine ⟨116327302902323375535915281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77551535268215583690610187 116327302902323375535915281)
  ·
    refine ⟨87245477176742531651936461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116327302902323375535915281 87245477176742531651936461)
    ·
      refine ⟨32717053941278449369476173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87245477176742531651936461 32717053941278449369476173)
      ·
        refine ⟨12268895227979418513553565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32717053941278449369476173 12268895227979418513553565)
        ·
          refine ⟨4600835710492281942582587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12268895227979418513553565 4600835710492281942582587)
          ·
            refine ⟨6901253565738422913873881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4600835710492281942582587 6901253565738422913873881)
            ·
              refine ⟨5175940174303817185405411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6901253565738422913873881 5175940174303817185405411)
              ·
                refine ⟨7763910261455725778108117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5175940174303817185405411 7763910261455725778108117)
                ·
                  refine ⟨181966646752868572924409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7763910261455725778108117 181966646752868572924409)
                  ·
                    rfl

theorem cell23_3189409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 7].length) (baseStart_3189409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189409 prefixEnd_3189409 := by exact prefixLift 3189409
  have htrace : WordTrace (prefixWord ++ tailWord_3189409) baseStart_3189409 baseEnd_3189409 := by
    simpa [prefixWord, tailWord_3189409, baseEnd_3189409] using wordTrace_append hprefix tailTrace_3189409
  have hstable : (prefixWord ++ tailWord_3189409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189409).length < 2 ^ (prefixWord ++ tailWord_3189409).sum := by decide
  have hdescent : baseEnd_3189409 < baseStart_3189409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189559 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 4, 4]
def baseStart_3189559 : Nat := 118140960795 + 3189559 * 2 ^ 59
def prefixEnd_3189559 : Nat := 4983230072969 + 3 ^ 40 * 3189559 * 2
def baseEnd_3189559 : Nat := 545925614291330523147997

theorem tailTrace_3189559 : CollatzResearch.WordTrace tailWord_3189559 prefixEnd_3189559 545925614291330523147997 := by
  unfold tailWord_3189559
  simp only [CollatzResearch.WordTrace]
  refine ⟨116332773851779951153875731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77555182567853300769250487 116332773851779951153875731)
  ·
    refine ⟨174499160777669926730813597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116332773851779951153875731 174499160777669926730813597)
    ·
      refine ⟨65437185291626222524055099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174499160777669926730813597 65437185291626222524055099)
      ·
        refine ⟨98155777937439333786082649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65437185291626222524055099 98155777937439333786082649)
        ·
          refine ⟨73616833453079500339561987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98155777937439333786082649 73616833453079500339561987)
          ·
            refine ⟨110425250179619250509342981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73616833453079500339561987 110425250179619250509342981)
            ·
              refine ⟨20704734408678609470501809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110425250179619250509342981 20704734408678609470501809)
              ·
                refine ⟨15528550806508957102876357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20704734408678609470501809 15528550806508957102876357)
                ·
                  refine ⟨2911603276220429456789317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15528550806508957102876357 2911603276220429456789317)
                  ·
                    refine ⟨545925614291330523147997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2911603276220429456789317 545925614291330523147997)
                    ·
                      rfl

theorem cell23_3189559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 4, 4].length) (baseStart_3189559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189559 prefixEnd_3189559 := by exact prefixLift 3189559
  have htrace : WordTrace (prefixWord ++ tailWord_3189559) baseStart_3189559 baseEnd_3189559 := by
    simpa [prefixWord, tailWord_3189559, baseEnd_3189559] using wordTrace_append hprefix tailTrace_3189559
  have hstable : (prefixWord ++ tailWord_3189559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189559).length < 2 ^ (prefixWord ++ tailWord_3189559).sum := by decide
  have hdescent : baseEnd_3189559 < baseStart_3189559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189593 : List Nat := [1, 2, 1, 2, 2, 5, 3, 1, 2, 4]
def baseStart_3189593 : Nat := 118140960795 + 3189593 * 2 ^ 59
def prefixEnd_3189593 : Nat := 4983230072969 + 3 ^ 40 * 3189593 * 2
def baseEnd_3189593 : Nat := 545931433738748145472945

theorem tailTrace_3189593 : CollatzResearch.WordTrace tailWord_3189593 prefixEnd_3189593 545931433738748145472945 := by
  unfold tailWord_3189593
  simp only [CollatzResearch.WordTrace]
  refine ⟨116334013933656774960613433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77556009289104516640408955 116334013933656774960613433)
  ·
    refine ⟨87250510450242581220460075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116334013933656774960613433 87250510450242581220460075)
    ·
      refine ⟨130875765675363871830690113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87250510450242581220460075 130875765675363871830690113)
      ·
        refine ⟨98156824256522903873017585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130875765675363871830690113 98156824256522903873017585)
        ·
          refine ⟨73617618192392177904763189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98156824256522903873017585 73617618192392177904763189)
          ·
            refine ⟨6901651705536766678571549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73617618192392177904763189 6901651705536766678571549)
            ·
              refine ⟨2588119389576287504464331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6901651705536766678571549 2588119389576287504464331)
              ·
                refine ⟨3882179084364431256696497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588119389576287504464331 3882179084364431256696497)
                ·
                  refine ⟨2911634313273323442522373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882179084364431256696497 2911634313273323442522373)
                  ·
                    refine ⟨545931433738748145472945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2911634313273323442522373 545931433738748145472945)
                    ·
                      rfl

theorem cell23_3189593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 1, 2, 4].length) (baseStart_3189593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189593 prefixEnd_3189593 := by exact prefixLift 3189593
  have htrace : WordTrace (prefixWord ++ tailWord_3189593) baseStart_3189593 baseEnd_3189593 := by
    simpa [prefixWord, tailWord_3189593, baseEnd_3189593] using wordTrace_append hprefix tailTrace_3189593
  have hstable : (prefixWord ++ tailWord_3189593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189593).length < 2 ^ (prefixWord ++ tailWord_3189593).sum := by decide
  have hdescent : baseEnd_3189593 < baseStart_3189593 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189596 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3189596 : Nat := 118140960795 + 3189596 * 2 ^ 59
def prefixEnd_3189596 : Nat := 4983230072969 + 3 ^ 40 * 3189596 * 2
def baseEnd_3189596 : Nat := 1637795841658207924681321

theorem tailTrace_3189596 : CollatzResearch.WordTrace tailWord_3189596 prefixEnd_3189596 1637795841658207924681321 := by
  unfold tailWord_3189596
  simp only [CollatzResearch.WordTrace]
  refine ⟨58167061676322953236486321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77556082235097270981981761 58167061676322953236486321)
  ·
    refine ⟨43625296257242214927364741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58167061676322953236486321 43625296257242214927364741)
    ·
      refine ⟨8179743048232915298880889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43625296257242214927364741 8179743048232915298880889)
      ·
        refine ⟨6134807286174686474160667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8179743048232915298880889 6134807286174686474160667)
        ·
          refine ⟨9202210929262029711241001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134807286174686474160667 9202210929262029711241001)
          ·
            refine ⟨6901658196946522283430751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202210929262029711241001 6901658196946522283430751)
            ·
              refine ⟨10352487295419783425146127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901658196946522283430751 10352487295419783425146127)
              ·
                refine ⟨15528730943129675137719191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10352487295419783425146127 15528730943129675137719191)
                ·
                  refine ⟨23293096414694512706578787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15528730943129675137719191 23293096414694512706578787)
                  ·
                    refine ⟨34939644622041769059868181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23293096414694512706578787 34939644622041769059868181)
                    ·
                      refine ⟨1637795841658207924681321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34939644622041769059868181 1637795841658207924681321)
                      ·
                        rfl

theorem cell23_3189596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3189596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189596 prefixEnd_3189596 := by exact prefixLift 3189596
  have htrace : WordTrace (prefixWord ++ tailWord_3189596) baseStart_3189596 baseEnd_3189596 := by
    simpa [prefixWord, tailWord_3189596, baseEnd_3189596] using wordTrace_append hprefix tailTrace_3189596
  have hstable : (prefixWord ++ tailWord_3189596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189596).length < 2 ^ (prefixWord ++ tailWord_3189596).sum := by decide
  have hdescent : baseEnd_3189596 < baseStart_3189596 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189603 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 3]
def baseStart_3189603 : Nat := 118140960795 + 3189603 * 2 ^ 59
def prefixEnd_3189603 : Nat := 4983230072969 + 3 ^ 40 * 3189603 * 2
def baseEnd_3189603 : Nat := 1637799436022789397293789

theorem tailTrace_3189603 : CollatzResearch.WordTrace tailWord_3189603 prefixEnd_3189603 1637799436022789397293789 := by
  unfold tailWord_3189603
  simp only [CollatzResearch.WordTrace]
  refine ⟨116334378663620546668477463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77556252442413697778984975 116334378663620546668477463)
  ·
    refine ⟨174501567995430820002716195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116334378663620546668477463 174501567995430820002716195)
    ·
      refine ⟨261752351993146230004074293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174501567995430820002716195 261752351993146230004074293)
      ·
        refine ⟨24539282999357459062881965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 261752351993146230004074293 24539282999357459062881965)
        ·
          refine ⟨9202231124759047148580737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24539282999357459062881965 9202231124759047148580737)
          ·
            refine ⟨6901673343569285361435553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9202231124759047148580737 6901673343569285361435553)
            ·
              refine ⟨5176255007676964021076665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6901673343569285361435553 5176255007676964021076665)
              ·
                refine ⟨3882191255757723015807499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176255007676964021076665 3882191255757723015807499)
                ·
                  refine ⟨5823286883636584523711249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882191255757723015807499 5823286883636584523711249)
                  ·
                    refine ⟨4367465162727438392783437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5823286883636584523711249 4367465162727438392783437)
                    ·
                      refine ⟨1637799436022789397293789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4367465162727438392783437 1637799436022789397293789)
                      ·
                        rfl

theorem cell23_3189603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_3189603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189603 prefixEnd_3189603 := by exact prefixLift 3189603
  have htrace : WordTrace (prefixWord ++ tailWord_3189603) baseStart_3189603 baseEnd_3189603 := by
    simpa [prefixWord, tailWord_3189603, baseEnd_3189603] using wordTrace_append hprefix tailTrace_3189603
  have hstable : (prefixWord ++ tailWord_3189603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189603).length < 2 ^ (prefixWord ++ tailWord_3189603).sum := by decide
  have hdescent : baseEnd_3189603 < baseStart_3189603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189616 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 4, 1, 3]
def baseStart_3189616 : Nat := 118140960795 + 3189616 * 2 ^ 59
def prefixEnd_3189616 : Nat := 4983230072969 + 3 ^ 40 * 3189616 * 2
def baseEnd_3189616 : Nat := 1637806111271297846431229

theorem tailTrace_3189616 : CollatzResearch.WordTrace tailWord_3189616 prefixEnd_3189616 1637806111271297846431229 := by
  unfold tailWord_3189616
  simp only [CollatzResearch.WordTrace]
  refine ⟨58167426406286724944350351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77556568541715633259133801 58167426406286724944350351)
  ·
    refine ⟨87251139609430087416525527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58167426406286724944350351 87251139609430087416525527)
    ·
      refine ⟨130876709414145131124788291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87251139609430087416525527 130876709414145131124788291)
      ·
        refine ⟨196315064121217696687182437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130876709414145131124788291 196315064121217696687182437)
        ·
          refine ⟨36809074522728318128846707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 196315064121217696687182437 36809074522728318128846707)
          ·
            refine ⟨55213611784092477193270061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36809074522728318128846707 55213611784092477193270061)
            ·
              refine ⟨20705104419034678947476273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55213611784092477193270061 20705104419034678947476273)
              ·
                refine ⟨15528828314276009210607205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20705104419034678947476273 15528828314276009210607205)
                ·
                  refine ⟨2911655308926751726988851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15528828314276009210607205 2911655308926751726988851)
                  ·
                    refine ⟨4367482963390127590483277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2911655308926751726988851 4367482963390127590483277)
                    ·
                      refine ⟨1637806111271297846431229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4367482963390127590483277 1637806111271297846431229)
                      ·
                        rfl

theorem cell23_3189616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 4, 1, 3].length) (baseStart_3189616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189616 prefixEnd_3189616 := by exact prefixLift 3189616
  have htrace : WordTrace (prefixWord ++ tailWord_3189616) baseStart_3189616 baseEnd_3189616 := by
    simpa [prefixWord, tailWord_3189616, baseEnd_3189616] using wordTrace_append hprefix tailTrace_3189616
  have hstable : (prefixWord ++ tailWord_3189616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189616).length < 2 ^ (prefixWord ++ tailWord_3189616).sum := by decide
  have hdescent : baseEnd_3189616 < baseStart_3189616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189617 : List Nat := [1, 2, 2, 2, 1, 6, 1, 3, 1, 2, 2]
def baseStart_3189617 : Nat := 118140960795 + 3189617 * 2 ^ 59
def prefixEnd_3189617 : Nat := 4983230072969 + 3 ^ 40 * 3189617 * 2
def baseEnd_3189617 : Nat := 1637806624751952342518725

theorem tailTrace_3189617 : CollatzResearch.WordTrace tailWord_3189617 prefixEnd_3189617 1637806624751952342518725 := by
  unfold tailWord_3189617
  simp only [CollatzResearch.WordTrace]
  refine ⟨116334889285569827059487105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77556592857046551372991403 116334889285569827059487105)
  ·
    refine ⟨87251166964177370294615329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116334889285569827059487105 87251166964177370294615329)
    ·
      refine ⟨65438375223133027720961497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87251166964177370294615329 65438375223133027720961497)
      ·
        refine ⟨49078781417349770790721123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65438375223133027720961497 49078781417349770790721123)
        ·
          refine ⟨73618172126024656186081685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49078781417349770790721123 73618172126024656186081685)
          ·
            refine ⟨3450851818407405758722579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 73618172126024656186081685 3450851818407405758722579)
            ·
              refine ⟨5176277727611108638083869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450851818407405758722579 5176277727611108638083869)
              ·
                refine ⟨1941104147854165739281451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5176277727611108638083869 1941104147854165739281451)
                ·
                  refine ⟨2911656221781248608922177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941104147854165739281451 2911656221781248608922177)
                  ·
                    refine ⟨2183742166335936456691633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2911656221781248608922177 2183742166335936456691633)
                    ·
                      refine ⟨1637806624751952342518725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183742166335936456691633 1637806624751952342518725)
                      ·
                        rfl

theorem cell23_3189617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 6, 1, 3, 1, 2, 2].length) (baseStart_3189617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189617 prefixEnd_3189617 := by exact prefixLift 3189617
  have htrace : WordTrace (prefixWord ++ tailWord_3189617) baseStart_3189617 baseEnd_3189617 := by
    simpa [prefixWord, tailWord_3189617, baseEnd_3189617] using wordTrace_append hprefix tailTrace_3189617
  have hstable : (prefixWord ++ tailWord_3189617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189617).length < 2 ^ (prefixWord ++ tailWord_3189617).sum := by decide
  have hdescent : baseEnd_3189617 < baseStart_3189617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189626 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2]
def baseStart_3189626 : Nat := 118140960795 + 3189626 * 2 ^ 59
def prefixEnd_3189626 : Nat := 4983230072969 + 3 ^ 40 * 3189626 * 2
def baseEnd_3189626 : Nat := 1637811246077842807306183

theorem tailTrace_3189626 : CollatzResearch.WordTrace tailWord_3189626 prefixEnd_3189626 1637811246077842807306183 := by
  unfold tailWord_3189626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29083804385634305399141183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77556811695024814397709821 29083804385634305399141183)
  ·
    refine ⟨43625706578451458098711775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29083804385634305399141183 43625706578451458098711775)
    ·
      refine ⟨65438559867677187148067663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43625706578451458098711775 65438559867677187148067663)
      ·
        refine ⟨98157839801515780722101495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65438559867677187148067663 98157839801515780722101495)
        ·
          refine ⟨147236759702273671083152243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98157839801515780722101495 147236759702273671083152243)
          ·
            refine ⟨220855139553410506624728365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147236759702273671083152243 220855139553410506624728365)
            ·
              refine ⟨82820677332528939984273137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220855139553410506624728365 82820677332528939984273137)
              ·
                refine ⟨62115507999396704988204853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82820677332528939984273137 62115507999396704988204853)
                ·
                  refine ⟨5823328874943441092644205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62115507999396704988204853 5823328874943441092644205)
                  ·
                    refine ⟨2183748328103790409741577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5823328874943441092644205 2183748328103790409741577)
                    ·
                      refine ⟨1637811246077842807306183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183748328103790409741577 1637811246077842807306183)
                      ·
                        rfl

theorem cell23_3189626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_3189626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189626 prefixEnd_3189626 := by exact prefixLift 3189626
  have htrace : WordTrace (prefixWord ++ tailWord_3189626) baseStart_3189626 baseEnd_3189626 := by
    simpa [prefixWord, tailWord_3189626, baseEnd_3189626] using wordTrace_append hprefix tailTrace_3189626
  have hstable : (prefixWord ++ tailWord_3189626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189626).length < 2 ^ (prefixWord ++ tailWord_3189626).sum := by decide
  have hdescent : baseEnd_3189626 < baseStart_3189626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189654 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 1, 2, 3]
def baseStart_3189654 : Nat := 118140960795 + 3189654 * 2 ^ 59
def prefixEnd_3189654 : Nat := 4983230072969 + 3 ^ 40 * 3189654 * 2
def baseEnd_3189654 : Nat := 1637825623536168697756055

theorem tailTrace_3189654 : CollatzResearch.WordTrace tailWord_3189654 prefixEnd_3189654 1637825623536168697756055 := by
  unfold tailWord_3189654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271014924152236398661501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77557492524290521585722677 7271014924152236398661501)
  ·
    refine ⟨2726630596557088649498063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7271014924152236398661501 2726630596557088649498063)
    ·
      refine ⟨4089945894835632974247095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2726630596557088649498063 4089945894835632974247095)
      ·
        refine ⟨6134918842253449461370643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4089945894835632974247095 6134918842253449461370643)
        ·
          refine ⟨9202378263380174192055965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6134918842253449461370643 9202378263380174192055965)
          ·
            refine ⟨3450891848767565322020987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9202378263380174192055965 3450891848767565322020987)
            ·
              refine ⟨5176337773151347983031481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3450891848767565322020987 5176337773151347983031481)
              ·
                refine ⟨3882253329863510987273611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176337773151347983031481 3882253329863510987273611)
                ·
                  refine ⟨5823379994795266480910417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3882253329863510987273611 5823379994795266480910417)
                  ·
                    refine ⟨4367534996096449860682813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5823379994795266480910417 4367534996096449860682813)
                    ·
                      refine ⟨1637825623536168697756055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4367534996096449860682813 1637825623536168697756055)
                      ·
                        rfl

theorem cell23_3189654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_3189654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189654 prefixEnd_3189654 := by exact prefixLift 3189654
  have htrace : WordTrace (prefixWord ++ tailWord_3189654) baseStart_3189654 baseEnd_3189654 := by
    simpa [prefixWord, tailWord_3189654, baseEnd_3189654] using wordTrace_append hprefix tailTrace_3189654
  have hstable : (prefixWord ++ tailWord_3189654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189654).length < 2 ^ (prefixWord ++ tailWord_3189654).sum := by decide
  have hdescent : baseEnd_3189654 < baseStart_3189654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189660 : List Nat := [2, 2, 3, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_3189660 : Nat := 118140960795 + 3189660 * 2 ^ 59
def prefixEnd_3189660 : Nat := 4983230072969 + 3 ^ 40 * 3189660 * 2
def baseEnd_3189660 : Nat := 1637828704420095674281027

theorem tailTrace_3189660 : CollatzResearch.WordTrace tailWord_3189660 prefixEnd_3189660 1637828704420095674281027 := by
  unfold tailWord_3189660
  simp only [CollatzResearch.WordTrace]
  refine ⟨58168228812207022701651217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77557638416276030268868289 58168228812207022701651217)
  ·
    refine ⟨43626171609155267026238413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58168228812207022701651217 43626171609155267026238413)
    ·
      refine ⟨16359814353433225134839405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43626171609155267026238413 16359814353433225134839405)
      ·
        refine ⟨6134930382537459425564777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16359814353433225134839405 6134930382537459425564777)
        ·
          refine ⟨4601197786903094569173583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6134930382537459425564777 4601197786903094569173583)
          ·
            refine ⟨6901796680354641853760375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601197786903094569173583 6901796680354641853760375)
            ·
              refine ⟨10352695020531962780640563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6901796680354641853760375 10352695020531962780640563)
              ·
                refine ⟨15529042530797944170960845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10352695020531962780640563 15529042530797944170960845)
                ·
                  refine ⟨5823390949049229064110317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15529042530797944170960845 5823390949049229064110317)
                  ·
                    refine ⟨2183771605893460899041369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5823390949049229064110317 2183771605893460899041369)
                    ·
                      refine ⟨1637828704420095674281027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183771605893460899041369 1637828704420095674281027)
                      ·
                        rfl

theorem cell23_3189660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_3189660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189660 prefixEnd_3189660 := by exact prefixLift 3189660
  have htrace : WordTrace (prefixWord ++ tailWord_3189660) baseStart_3189660 baseEnd_3189660 := by
    simpa [prefixWord, tailWord_3189660, baseEnd_3189660] using wordTrace_append hprefix tailTrace_3189660
  have hstable : (prefixWord ++ tailWord_3189660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189660).length < 2 ^ (prefixWord ++ tailWord_3189660).sum := by decide
  have hdescent : baseEnd_3189660 < baseStart_3189660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189669 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_3189669 : Nat := 118140960795 + 3189669 * 2 ^ 59
def prefixEnd_3189669 : Nat := 4983230072969 + 3 ^ 40 * 3189669 * 2
def baseEnd_3189669 : Nat := 1637833325745986139068485

theorem tailTrace_3189669 : CollatzResearch.WordTrace tailWord_3189669 prefixEnd_3189669 1637833325745986139068485 := by
  unfold tailWord_3189669
  simp only [CollatzResearch.WordTrace]
  refine ⟨116336785881381439940380061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77557857254254293293586707 116336785881381439940380061)
  ·
    refine ⟨43626294705518039977642523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116336785881381439940380061 43626294705518039977642523)
    ·
      refine ⟨65439442058277059966463785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43626294705518039977642523 65439442058277059966463785)
      ·
        refine ⟨49079581543707794974847839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65439442058277059966463785 49079581543707794974847839)
        ·
          refine ⟨73619372315561692462271759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49079581543707794974847839 73619372315561692462271759)
          ·
            refine ⟨110429058473342538693407639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73619372315561692462271759 110429058473342538693407639)
            ·
              refine ⟨165643587710013808040111459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110429058473342538693407639 165643587710013808040111459)
              ·
                refine ⟨248465381565020712060167189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165643587710013808040111459 248465381565020712060167189)
                ·
                  refine ⟨11646814760860345877820337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 248465381565020712060167189 11646814760860345877820337)
                  ·
                    refine ⟨8735111070645259408365253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11646814760860345877820337 8735111070645259408365253)
                    ·
                      refine ⟨1637833325745986139068485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8735111070645259408365253 1637833325745986139068485)
                      ·
                        rfl

theorem cell23_3189669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_3189669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189669 prefixEnd_3189669 := by exact prefixLift 3189669
  have htrace : WordTrace (prefixWord ++ tailWord_3189669) baseStart_3189669 baseEnd_3189669 := by
    simpa [prefixWord, tailWord_3189669, baseEnd_3189669] using wordTrace_append hprefix tailTrace_3189669
  have hstable : (prefixWord ++ tailWord_3189669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189669).length < 2 ^ (prefixWord ++ tailWord_3189669).sum := by decide
  have hdescent : baseEnd_3189669 < baseStart_3189669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189690 : List Nat := [3, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2]
def baseStart_3189690 : Nat := 118140960795 + 3189690 * 2 ^ 59
def prefixEnd_3189690 : Nat := 4983230072969 + 3 ^ 40 * 3189690 * 2
def baseEnd_3189690 : Nat := 1637844108839730556905889

theorem tailTrace_3189690 : CollatzResearch.WordTrace tailWord_3189690 prefixEnd_3189690 1637844108839730556905889 := by
  unfold tailWord_3189690
  simp only [CollatzResearch.WordTrace]
  refine ⟨29084387953576340131723631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77558367876203573684596349 29084387953576340131723631)
  ·
    refine ⟨43626581930364510197585447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29084387953576340131723631 43626581930364510197585447)
    ·
      refine ⟨65439872895546765296378171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43626581930364510197585447 65439872895546765296378171)
      ·
        refine ⟨98159809343320147944567257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65439872895546765296378171 98159809343320147944567257)
        ·
          refine ⟨73619857007490110958425443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98159809343320147944567257 73619857007490110958425443)
          ·
            refine ⟨110429785511235166437638165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73619857007490110958425443 110429785511235166437638165)
            ·
              refine ⟨5176396195839148426764289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110429785511235166437638165 5176396195839148426764289)
              ·
                refine ⟨3882297146879361320073217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5176396195839148426764289 3882297146879361320073217)
                ·
                  refine ⟨2911722860159520990054913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882297146879361320073217 2911722860159520990054913)
                  ·
                    refine ⟨2183792145119640742541185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2911722860159520990054913 2183792145119640742541185)
                    ·
                      refine ⟨1637844108839730556905889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183792145119640742541185 1637844108839730556905889)
                      ·
                        rfl

theorem cell23_3189690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_3189690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189690 prefixEnd_3189690 := by exact prefixLift 3189690
  have htrace : WordTrace (prefixWord ++ tailWord_3189690) baseStart_3189690 baseEnd_3189690 := by
    simpa [prefixWord, tailWord_3189690, baseEnd_3189690] using wordTrace_append hprefix tailTrace_3189690
  have hstable : (prefixWord ++ tailWord_3189690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189690).length < 2 ^ (prefixWord ++ tailWord_3189690).sum := by decide
  have hdescent : baseEnd_3189690 < baseStart_3189690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189719 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3189719 : Nat := 118140960795 + 3189719 * 2 ^ 59
def prefixEnd_3189719 : Nat := 4983230072969 + 3 ^ 40 * 3189719 * 2
def baseEnd_3189719 : Nat := 1637858999778710943443255

theorem tailTrace_3189719 : CollatzResearch.WordTrace tailWord_3189719 prefixEnd_3189719 1637858999778710943443255 := by
  unfold tailWord_3189719
  simp only [CollatzResearch.WordTrace]
  refine ⟨116338609531200298479700211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77559073020800198986466807 116338609531200298479700211)
  ·
    refine ⟨174507914296800447719550317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116338609531200298479700211 174507914296800447719550317)
    ·
      refine ⟨65440467861300167894831369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174507914296800447719550317 65440467861300167894831369)
      ·
        refine ⟨49080350895975125921123527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65440467861300167894831369 49080350895975125921123527)
        ·
          refine ⟨73620526343962688881685291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49080350895975125921123527 73620526343962688881685291)
          ·
            refine ⟨110430789515944033322527937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73620526343962688881685291 110430789515944033322527937)
            ·
              refine ⟨82823092136958024991895953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110430789515944033322527937 82823092136958024991895953)
              ·
                refine ⟨62117319102718518743921965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82823092136958024991895953 62117319102718518743921965)
                ·
                  refine ⟨23293994663519444528970737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62117319102718518743921965 23293994663519444528970737)
                  ·
                    refine ⟨17470495997639583396728053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23293994663519444528970737 17470495997639583396728053)
                    ·
                      refine ⟨1637858999778710943443255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17470495997639583396728053 1637858999778710943443255)
                      ·
                        rfl

theorem cell23_3189719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3189719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189719 prefixEnd_3189719 := by exact prefixLift 3189719
  have htrace : WordTrace (prefixWord ++ tailWord_3189719) baseStart_3189719 baseEnd_3189719 := by
    simpa [prefixWord, tailWord_3189719, baseEnd_3189719] using wordTrace_append hprefix tailTrace_3189719
  have hstable : (prefixWord ++ tailWord_3189719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189719).length < 2 ^ (prefixWord ++ tailWord_3189719).sum := by decide
  have hdescent : baseEnd_3189719 < baseStart_3189719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189730 : List Nat := [3, 3, 3, 1, 1, 1, 1, 5, 5]
def baseStart_3189730 : Nat := 118140960795 + 3189730 * 2 ^ 59
def prefixEnd_3189730 : Nat := 4983230072969 + 3 ^ 40 * 3189730 * 2
def baseEnd_3189730 : Nat := 181984960896212266711745

theorem tailTrace_3189730 : CollatzResearch.WordTrace tailWord_3189730 prefixEnd_3189730 181984960896212266711745 := by
  unfold tailWord_3189730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29084752683540111839587661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77559340489440298238900429 29084752683540111839587661)
  ·
    refine ⟨10906782256327541939845373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29084752683540111839587661 10906782256327541939845373)
    ·
      refine ⟨4090043346122828227442015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10906782256327541939845373 4090043346122828227442015)
      ·
        refine ⟨6135065019184242341163023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090043346122828227442015 6135065019184242341163023)
        ·
          refine ⟨9202597528776363511744535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135065019184242341163023 9202597528776363511744535)
          ·
            refine ⟨13803896293164545267616803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9202597528776363511744535 13803896293164545267616803)
            ·
              refine ⟨20705844439746817901425205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13803896293164545267616803 20705844439746817901425205)
              ·
                refine ⟨1941172916226264178258613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20705844439746817901425205 1941172916226264178258613)
                ·
                  refine ⟨181984960896212266711745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1941172916226264178258613 181984960896212266711745)
                  ·
                    rfl

theorem cell23_3189730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 5, 5].length) (baseStart_3189730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189730 prefixEnd_3189730 := by exact prefixLift 3189730
  have htrace : WordTrace (prefixWord ++ tailWord_3189730) baseStart_3189730 baseEnd_3189730 := by
    simpa [prefixWord, tailWord_3189730, baseEnd_3189730] using wordTrace_append hprefix tailTrace_3189730
  have hstable : (prefixWord ++ tailWord_3189730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189730).length < 2 ^ (prefixWord ++ tailWord_3189730).sum := by decide
  have hdescent : baseEnd_3189730 < baseStart_3189730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189783 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 3]
def baseStart_3189783 : Nat := 118140960795 + 3189783 * 2 ^ 59
def prefixEnd_3189783 : Nat := 4983230072969 + 3 ^ 40 * 3189783 * 2
def baseEnd_3189783 : Nat := 1637891862540598693042961

theorem tailTrace_3189783 : CollatzResearch.WordTrace tailWord_3189783 prefixEnd_3189783 1637891862540598693042961 := by
  unfold tailWord_3189783
  simp only [CollatzResearch.WordTrace]
  refine ⟨116340943802968437410030003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77560629201978958273353335 116340943802968437410030003)
  ·
    refine ⟨174511415704452656115045005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116340943802968437410030003 174511415704452656115045005)
    ·
      refine ⟨65441780889169746043141877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174511415704452656115045005 65441780889169746043141877)
      ·
        refine ⟨6135166958359663691544551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65441780889169746043141877 6135166958359663691544551)
        ·
          refine ⟨9202750437539495537316827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135166958359663691544551 9202750437539495537316827)
          ·
            refine ⟨13804125656309243305975241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9202750437539495537316827 13804125656309243305975241)
            ·
              refine ⟨10353094242231932479481431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13804125656309243305975241 10353094242231932479481431)
              ·
                refine ⟨15529641363347898719222147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10353094242231932479481431 15529641363347898719222147)
                ·
                  refine ⟨23294462045021848078833221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15529641363347898719222147 23294462045021848078833221)
                  ·
                    refine ⟨4367711633441596514781229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23294462045021848078833221 4367711633441596514781229)
                    ·
                      refine ⟨1637891862540598693042961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4367711633441596514781229 1637891862540598693042961)
                      ·
                        rfl

theorem cell23_3189783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_3189783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189783 prefixEnd_3189783 := by exact prefixLift 3189783
  have htrace : WordTrace (prefixWord ++ tailWord_3189783) baseStart_3189783 baseEnd_3189783 := by
    simpa [prefixWord, tailWord_3189783, baseEnd_3189783] using wordTrace_append hprefix tailTrace_3189783
  have hstable : (prefixWord ++ tailWord_3189783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189783).length < 2 ^ (prefixWord ++ tailWord_3189783).sum := by decide
  have hdescent : baseEnd_3189783 < baseStart_3189783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189820 : List Nat := [2, 2, 2, 2, 2, 4, 2, 1, 6]
def baseStart_3189820 : Nat := 118140960795 + 3189820 * 2 ^ 59
def prefixEnd_3189820 : Nat := 4983230072969 + 3 ^ 40 * 3189820 * 2
def baseEnd_3189820 : Nat := 181990095702757227586699

theorem tailTrace_3189820 : CollatzResearch.WordTrace tailWord_3189820 prefixEnd_3189820 181990095702757227586699 := by
  unfold tailWord_3189820
  simp only [CollatzResearch.WordTrace]
  refine ⟨58171146651917196364563457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77561528869222928486084609 58171146651917196364563457)
  ·
    refine ⟨43628359988937897273422593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58171146651917196364563457 43628359988937897273422593)
    ·
      refine ⟨32721269991703422955066945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43628359988937897273422593 32721269991703422955066945)
      ·
        refine ⟨24540952493777567216300209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32721269991703422955066945 24540952493777567216300209)
        ·
          refine ⟨18405714370333175412225157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24540952493777567216300209 18405714370333175412225157)
          ·
            refine ⟨3451071444437470389792217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18405714370333175412225157 3451071444437470389792217)
            ·
              refine ⟨2588303583328102792344163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451071444437470389792217 2588303583328102792344163)
              ·
                refine ⟨3882455374992154188516245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588303583328102792344163 3882455374992154188516245)
                ·
                  refine ⟨181990095702757227586699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3882455374992154188516245 181990095702757227586699)
                  ·
                    rfl

theorem cell23_3189820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_3189820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189820 prefixEnd_3189820 := by exact prefixLift 3189820
  have htrace : WordTrace (prefixWord ++ tailWord_3189820) baseStart_3189820 baseEnd_3189820 := by
    simpa [prefixWord, tailWord_3189820, baseEnd_3189820] using wordTrace_append hprefix tailTrace_3189820
  have hstable : (prefixWord ++ tailWord_3189820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189820).length < 2 ^ (prefixWord ++ tailWord_3189820).sum := by decide
  have hdescent : baseEnd_3189820 < baseStart_3189820 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189823 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 6, 3, 2]
def baseStart_3189823 : Nat := 118140960795 + 3189823 * 2 ^ 59
def prefixEnd_3189823 : Nat := 4983230072969 + 3 ^ 40 * 3189823 * 2
def baseEnd_3189823 : Nat := 1637912401766778536542777

theorem tailTrace_3189823 : CollatzResearch.WordTrace tailWord_3189823 prefixEnd_3189823 1637912401766778536542777 := by
  unfold tailWord_3189823
  simp only [CollatzResearch.WordTrace]
  refine ⟨116342402722823524241486123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77561601815215682827657415 116342402722823524241486123)
  ·
    refine ⟨174513604084235286362229185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116342402722823524241486123 174513604084235286362229185)
    ·
      refine ⟨130885203063176464771671889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174513604084235286362229185 130885203063176464771671889)
      ·
        refine ⟨98163902297382348578753917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130885203063176464771671889 98163902297382348578753917)
        ·
          refine ⟨36811463361518380717032719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98163902297382348578753917 36811463361518380717032719)
          ·
            refine ⟨55217195042277571075549079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36811463361518380717032719 55217195042277571075549079)
            ·
              refine ⟨82825792563416356613323619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55217195042277571075549079 82825792563416356613323619)
              ·
                refine ⟨124238688845124534919985429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82825792563416356613323619 124238688845124534919985429)
                ·
                  refine ⟨5823688539615212574374317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124238688845124534919985429 5823688539615212574374317)
                  ·
                    refine ⟨2183883202355704715390369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5823688539615212574374317 2183883202355704715390369)
                    ·
                      refine ⟨1637912401766778536542777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183883202355704715390369 1637912401766778536542777)
                      ·
                        rfl

theorem cell23_3189823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 6, 3, 2].length) (baseStart_3189823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189823 prefixEnd_3189823 := by exact prefixLift 3189823
  have htrace : WordTrace (prefixWord ++ tailWord_3189823) baseStart_3189823 baseEnd_3189823 := by
    simpa [prefixWord, tailWord_3189823, baseEnd_3189823] using wordTrace_append hprefix tailTrace_3189823
  have hstable : (prefixWord ++ tailWord_3189823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189823).length < 2 ^ (prefixWord ++ tailWord_3189823).sum := by decide
  have hdescent : baseEnd_3189823 < baseStart_3189823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189920 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 4, 1, 3]
def baseStart_3189920 : Nat := 118140960795 + 3189920 * 2 ^ 59
def prefixEnd_3189920 : Nat := 4983230072969 + 3 ^ 40 * 3189920 * 2
def baseEnd_3189920 : Nat := 1637962209390264657029831

theorem tailTrace_3189920 : CollatzResearch.WordTrace tailWord_3189920 prefixEnd_3189920 1637962209390264657029831 := by
  unfold tailWord_3189920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58172970301736054903883607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77563960402314739871844809 58172970301736054903883607)
  ·
    refine ⟨87259455452604082355825411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58172970301736054903883607 87259455452604082355825411)
    ·
      refine ⟨130889183178906123533738117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87259455452604082355825411 130889183178906123533738117)
      ·
        refine ⟨24541721846044898162575897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 130889183178906123533738117 24541721846044898162575897)
        ·
          refine ⟨18406291384533673621931923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24541721846044898162575897 18406291384533673621931923)
          ·
            refine ⟨27609437076800510432897885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18406291384533673621931923 27609437076800510432897885)
            ·
              refine ⟨10353538903800191412336707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27609437076800510432897885 10353538903800191412336707)
              ·
                refine ⟨15530308355700287118505061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10353538903800191412336707 15530308355700287118505061)
                ·
                  refine ⟨2911932816693803834719699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15530308355700287118505061 2911932816693803834719699)
                  ·
                    refine ⟨4367899225040705752079549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2911932816693803834719699 4367899225040705752079549)
                    ·
                      refine ⟨1637962209390264657029831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4367899225040705752079549 1637962209390264657029831)
                      ·
                        rfl

theorem cell23_3189920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 4, 1, 3].length) (baseStart_3189920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189920 prefixEnd_3189920 := by exact prefixLift 3189920
  have htrace : WordTrace (prefixWord ++ tailWord_3189920) baseStart_3189920 baseEnd_3189920 := by
    simpa [prefixWord, tailWord_3189920, baseEnd_3189920] using wordTrace_append hprefix tailTrace_3189920
  have hstable : (prefixWord ++ tailWord_3189920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189920).length < 2 ^ (prefixWord ++ tailWord_3189920).sum := by decide
  have hdescent : baseEnd_3189920 < baseStart_3189920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189937 : List Nat := [1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 3]
def baseStart_3189937 : Nat := 118140960795 + 3189937 * 2 ^ 59
def prefixEnd_3189937 : Nat := 4983230072969 + 3 ^ 40 * 3189937 * 2
def baseEnd_3189937 : Nat := 1637970938561391090517253

theorem tailTrace_3189937 : CollatzResearch.WordTrace tailWord_3189937 prefixEnd_3189937 1637970938561391090517253 := by
  unfold tailWord_3189937
  simp only [CollatzResearch.WordTrace]
  refine ⟨116346560644410521711136065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77564373762940347807424043 116346560644410521711136065)
  ·
    refine ⟨87259920483307891283352049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116346560644410521711136065 87259920483307891283352049)
    ·
      refine ⟨65444940362480918462514037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87259920483307891283352049 65444940362480918462514037)
      ·
        refine ⟨6135463158982586105860691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65444940362480918462514037 6135463158982586105860691)
        ·
          refine ⟨9203194738473879158791037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135463158982586105860691 9203194738473879158791037)
          ·
            refine ⟨3451198026927704684546639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9203194738473879158791037 3451198026927704684546639)
            ·
              refine ⟨5176797040391557026819959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451198026927704684546639 5176797040391557026819959)
              ·
                refine ⟨7765195560587335540229939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176797040391557026819959 7765195560587335540229939)
                ·
                  refine ⟨11647793340881003310344909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765195560587335540229939 11647793340881003310344909)
                  ·
                    refine ⟨4367922502830376241379341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11647793340881003310344909 4367922502830376241379341)
                    ·
                      refine ⟨1637970938561391090517253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4367922502830376241379341 1637970938561391090517253)
                      ·
                        rfl

theorem cell23_3189937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_3189937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189937 prefixEnd_3189937 := by exact prefixLift 3189937
  have htrace : WordTrace (prefixWord ++ tailWord_3189937) baseStart_3189937 baseEnd_3189937 := by
    simpa [prefixWord, tailWord_3189937, baseEnd_3189937] using wordTrace_append hprefix tailTrace_3189937
  have hstable : (prefixWord ++ tailWord_3189937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189937).length < 2 ^ (prefixWord ++ tailWord_3189937).sum := by decide
  have hdescent : baseEnd_3189937 < baseStart_3189937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189960 : List Nat := [2, 1, 3, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_3189960 : Nat := 118140960795 + 3189960 * 2 ^ 59
def prefixEnd_3189960 : Nat := 4983230072969 + 3 ^ 40 * 3189960 * 2
def baseEnd_3189960 : Nat := 1637982748616444500529647

theorem tailTrace_3189960 : CollatzResearch.WordTrace tailWord_3189960 prefixEnd_3189960 1637982748616444500529647 := by
  unfold tailWord_3189960
  simp only [CollatzResearch.WordTrace]
  refine ⟨58173699761663598319611667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77564933015551464426148889 58173699761663598319611667)
  ·
    refine ⟨87260549642495397479417501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58173699761663598319611667 87260549642495397479417501)
    ·
      refine ⟨32722706115935774054781563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87260549642495397479417501 32722706115935774054781563)
      ·
        refine ⟨49084059173903661082172345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32722706115935774054781563 49084059173903661082172345)
        ·
          refine ⟨36813044380427745811629259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49084059173903661082172345 36813044380427745811629259)
          ·
            refine ⟨55219566570641618717443889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36813044380427745811629259 55219566570641618717443889)
            ·
              refine ⟨41414674927981214038082917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55219566570641618717443889 41414674927981214038082917)
              ·
                refine ⟨7765251548996477632140547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41414674927981214038082917 7765251548996477632140547)
                ·
                  refine ⟨11647877323494716448210821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765251548996477632140547 11647877323494716448210821)
                  ·
                    refine ⟨2183976998155259334039529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11647877323494716448210821 2183976998155259334039529)
                    ·
                      refine ⟨1637982748616444500529647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183976998155259334039529 1637982748616444500529647)
                      ·
                        rfl

theorem cell23_3189960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_3189960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189960 prefixEnd_3189960 := by exact prefixLift 3189960
  have htrace : WordTrace (prefixWord ++ tailWord_3189960) baseStart_3189960 baseEnd_3189960 := by
    simpa [prefixWord, tailWord_3189960, baseEnd_3189960] using wordTrace_append hprefix tailTrace_3189960
  have hstable : (prefixWord ++ tailWord_3189960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189960).length < 2 ^ (prefixWord ++ tailWord_3189960).sum := by decide
  have hdescent : baseEnd_3189960 < baseStart_3189960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189977 : List Nat := [1, 2, 1, 2, 3, 1, 1, 6, 2, 2, 2]
def baseStart_3189977 : Nat := 118140960795 + 3189977 * 2 ^ 59
def prefixEnd_3189977 : Nat := 4983230072969 + 3 ^ 40 * 3189977 * 2
def baseEnd_3189977 : Nat := 1637991477787570934017069

theorem tailTrace_3189977 : CollatzResearch.WordTrace tailWord_3189977 prefixEnd_3189977 1637991477787570934017069 := by
  unfold tailWord_3189977
  simp only [CollatzResearch.WordTrace]
  refine ⟨116348019564265608542592185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77565346376177072361728123 116348019564265608542592185)
  ·
    refine ⟨87261014673199206406944139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116348019564265608542592185 87261014673199206406944139)
    ·
      refine ⟨130891522009798809610416209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87261014673199206406944139 130891522009798809610416209)
      ·
        refine ⟨98168641507349107207812157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130891522009798809610416209 98168641507349107207812157)
        ·
          refine ⟨36813240565255915202929559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98168641507349107207812157 36813240565255915202929559)
          ·
            refine ⟨55219860847883872804394339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36813240565255915202929559 55219860847883872804394339)
            ·
              refine ⟨82829791271825809206591509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55219860847883872804394339 82829791271825809206591509)
              ·
                refine ⟨3882646465866834806558977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82829791271825809206591509 3882646465866834806558977)
                ·
                  refine ⟨2911984849400126104919233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882646465866834806558977 2911984849400126104919233)
                  ·
                    refine ⟨2183988637050094578689425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2911984849400126104919233 2183988637050094578689425)
                    ·
                      refine ⟨1637991477787570934017069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2183988637050094578689425 1637991477787570934017069)
                      ·
                        rfl

theorem cell23_3189977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 6, 2, 2, 2].length) (baseStart_3189977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189977 prefixEnd_3189977 := by exact prefixLift 3189977
  have htrace : WordTrace (prefixWord ++ tailWord_3189977) baseStart_3189977 baseEnd_3189977 := by
    simpa [prefixWord, tailWord_3189977, baseEnd_3189977] using wordTrace_append hprefix tailTrace_3189977
  have hstable : (prefixWord ++ tailWord_3189977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189977).length < 2 ^ (prefixWord ++ tailWord_3189977).sum := by decide
  have hdescent : baseEnd_3189977 < baseStart_3189977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189983 : List Nat := [1, 1, 2, 3, 2, 1, 5, 1, 7]
def baseStart_3189983 : Nat := 118140960795 + 3189983 * 2 ^ 59
def prefixEnd_3189983 : Nat := 4983230072969 + 3 ^ 40 * 3189983 * 2
def baseEnd_3189983 : Nat := 181999395407944212282449

theorem tailTrace_3189983 : CollatzResearch.WordTrace tailWord_3189983 prefixEnd_3189983 181999395407944212282449 := by
  unfold tailWord_3189983
  simp only [CollatzResearch.WordTrace]
  refine ⟨116348238402243871567310603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77565492268162581044873735 116348238402243871567310603)
  ·
    refine ⟨174522357603365807350965905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116348238402243871567310603 174522357603365807350965905)
    ·
      refine ⟨130891768202524355513224429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174522357603365807350965905 130891768202524355513224429)
      ·
        refine ⟨49084413075946633317459161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130891768202524355513224429 49084413075946633317459161)
        ·
          refine ⟨36813309806959974988094371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49084413075946633317459161 36813309806959974988094371)
          ·
            refine ⟨55219964710439962482141557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36813309806959974988094371 55219964710439962482141557)
            ·
              refine ⟨5176871691603746482700771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55219964710439962482141557 5176871691603746482700771)
              ·
                refine ⟨7765307537405619724051157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5176871691603746482700771 7765307537405619724051157)
                ·
                  refine ⟨181999395407944212282449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7765307537405619724051157 181999395407944212282449)
                  ·
                    rfl

theorem cell23_3189983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 1, 7].length) (baseStart_3189983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189983 prefixEnd_3189983 := by exact prefixLift 3189983
  have htrace : WordTrace (prefixWord ++ tailWord_3189983) baseStart_3189983 baseEnd_3189983 := by
    simpa [prefixWord, tailWord_3189983, baseEnd_3189983] using wordTrace_append hprefix tailTrace_3189983
  have hstable : (prefixWord ++ tailWord_3189983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189983).length < 2 ^ (prefixWord ++ tailWord_3189983).sum := by decide
  have hdescent : baseEnd_3189983 < baseStart_3189983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3189994 : List Nat := [3, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2]
def baseStart_3189994 : Nat := 118140960795 + 3189994 * 2 ^ 59
def prefixEnd_3189994 : Nat := 4983230072969 + 3 ^ 40 * 3189994 * 2
def baseEnd_3189994 : Nat := 1638000206958697367504491

theorem tailTrace_3189994 : CollatzResearch.WordTrace tailWord_3189994 prefixEnd_3189994 1638000206958697367504491 := by
  unfold tailWord_3189994
  simp only [CollatzResearch.WordTrace]
  refine ⟨29087159901301005111490259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77565759736802680297307357 29087159901301005111490259)
  ·
    refine ⟨43630739851951507667235389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29087159901301005111490259 43630739851951507667235389)
    ·
      refine ⟨16361527444481815375213271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43630739851951507667235389 16361527444481815375213271)
      ·
        refine ⟨24542291166722723062819907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16361527444481815375213271 24542291166722723062819907)
        ·
          refine ⟨36813436750084084594229861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24542291166722723062819907 36813436750084084594229861)
          ·
            refine ⟨6902519390640765861418099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36813436750084084594229861 6902519390640765861418099)
            ·
              refine ⟨10353779085961148792127149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902519390640765861418099 10353779085961148792127149)
              ·
                refine ⟨3882667157235430797047681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10353779085961148792127149 3882667157235430797047681)
                ·
                  refine ⟨2912000367926573097785761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882667157235430797047681 2912000367926573097785761)
                  ·
                    refine ⟨2184000275944929823339321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912000367926573097785761 2184000275944929823339321)
                    ·
                      refine ⟨1638000206958697367504491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184000275944929823339321 1638000206958697367504491)
                      ·
                        rfl

theorem cell23_3189994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 3, 2, 2, 2].length) (baseStart_3189994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3189994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3189994 prefixEnd_3189994 := by exact prefixLift 3189994
  have htrace : WordTrace (prefixWord ++ tailWord_3189994) baseStart_3189994 baseEnd_3189994 := by
    simpa [prefixWord, tailWord_3189994, baseEnd_3189994] using wordTrace_append hprefix tailTrace_3189994
  have hstable : (prefixWord ++ tailWord_3189994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3189994).length < 2 ^ (prefixWord ++ tailWord_3189994).sum := by decide
  have hdescent : baseEnd_3189994 < baseStart_3189994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3189994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190030 : List Nat := [4, 1, 1, 2, 1, 3, 2, 2, 2, 5]
def baseStart_3190030 : Nat := 118140960795 + 3190030 * 2 ^ 59
def prefixEnd_3190030 : Nat := 4983230072969 + 3 ^ 40 * 3190030 * 2
def baseEnd_3190030 : Nat := 546006230754086408884775

theorem tailTrace_3190030 : CollatzResearch.WordTrace tailWord_3190030 prefixEnd_3190030 546006230754086408884775 := by
  unfold tailWord_3190030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14543744079134199824283943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77566635088715732396181029 14543744079134199824283943)
  ·
    refine ⟨21815616118701299736425915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14543744079134199824283943 21815616118701299736425915)
    ·
      refine ⟨32723424178051949604638873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21815616118701299736425915 32723424178051949604638873)
      ·
        refine ⟨24542568133538962203479155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32723424178051949604638873 24542568133538962203479155)
        ·
          refine ⟨36813852200308443305218733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24542568133538962203479155 36813852200308443305218733)
          ·
            refine ⟨13805194575115666239457025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36813852200308443305218733 13805194575115666239457025)
            ·
              refine ⟨10353895931336749679592769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13805194575115666239457025 10353895931336749679592769)
              ·
                refine ⟨7765421948502562259694577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10353895931336749679592769 7765421948502562259694577)
                ·
                  refine ⟨5824066461376921694770933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7765421948502562259694577 5824066461376921694770933)
                  ·
                    refine ⟨546006230754086408884775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5824066461376921694770933 546006230754086408884775)
                    ·
                      rfl

theorem cell23_3190030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_3190030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190030 prefixEnd_3190030 := by exact prefixLift 3190030
  have htrace : WordTrace (prefixWord ++ tailWord_3190030) baseStart_3190030 baseEnd_3190030 := by
    simpa [prefixWord, tailWord_3190030, baseEnd_3190030] using wordTrace_append hprefix tailTrace_3190030
  have hstable : (prefixWord ++ tailWord_3190030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190030).length < 2 ^ (prefixWord ++ tailWord_3190030).sum := by decide
  have hdescent : baseEnd_3190030 < baseStart_3190030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190067 : List Nat := [1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 4]
def baseStart_3190067 : Nat := 118140960795 + 3190067 * 2 ^ 59
def prefixEnd_3190067 : Nat := 4983230072969 + 3 ^ 40 * 3190067 * 2
def baseEnd_3190067 : Nat := 1638037691046475581891655

theorem tailTrace_3190067 : CollatzResearch.WordTrace tailWord_3190067 prefixEnd_3190067 1638037691046475581891655 := by
  unfold tailWord_3190067
  simp only [CollatzResearch.WordTrace]
  refine ⟨116351302133939553913368455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77567534755959702608912303 116351302133939553913368455)
  ·
    refine ⟨174526953200909330870052683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116351302133939553913368455 174526953200909330870052683)
    ·
      refine ⟨261790429801363996305079025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174526953200909330870052683 261790429801363996305079025)
      ·
        refine ⟨196342822351022997228809269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261790429801363996305079025 196342822351022997228809269)
        ·
          refine ⟨18407139595408405990200869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 196342822351022997228809269 18407139595408405990200869)
          ·
            refine ⟨3451338674139076123162663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18407139595408405990200869 3451338674139076123162663)
            ·
              refine ⟨5177008011208614184743995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451338674139076123162663 5177008011208614184743995)
              ·
                refine ⟨7765512016812921277115993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5177008011208614184743995 7765512016812921277115993)
                ·
                  refine ⟨5824134012609690957836995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7765512016812921277115993 5824134012609690957836995)
                  ·
                    refine ⟨8736201018914536436755493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5824134012609690957836995 8736201018914536436755493)
                    ·
                      refine ⟨1638037691046475581891655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8736201018914536436755493 1638037691046475581891655)
                      ·
                        rfl

theorem cell23_3190067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_3190067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190067 prefixEnd_3190067 := by exact prefixLift 3190067
  have htrace : WordTrace (prefixWord ++ tailWord_3190067) baseStart_3190067 baseEnd_3190067 := by
    simpa [prefixWord, tailWord_3190067, baseEnd_3190067] using wordTrace_append hprefix tailTrace_3190067
  have hstable : (prefixWord ++ tailWord_3190067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190067).length < 2 ^ (prefixWord ++ tailWord_3190067).sum := by decide
  have hdescent : baseEnd_3190067 < baseStart_3190067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190084 : List Nat := [2, 3, 4, 1, 1, 1, 1, 2, 2, 4, 2]
def baseStart_3190084 : Nat := 118140960795 + 3190084 * 2 ^ 59
def prefixEnd_3190084 : Nat := 4983230072969 + 3 ^ 40 * 3190084 * 2
def baseEnd_3190084 : Nat := 1638046420217602015379077

theorem tailTrace_3190084 : CollatzResearch.WordTrace tailWord_3190084 prefixEnd_3190084 1638046420217602015379077 := by
  unfold tailWord_3190084
  simp only [CollatzResearch.WordTrace]
  refine ⟨58175961087438982908368653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77567948116585310544491537 58175961087438982908368653)
  ·
    refine ⟨21815985407789618590638245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58175961087438982908368653 21815985407789618590638245)
    ·
      refine ⟨4090497263960553485744671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21815985407789618590638245 4090497263960553485744671)
      ·
        refine ⟨6135745895940830228617007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090497263960553485744671 6135745895940830228617007)
        ·
          refine ⟨9203618843911245342925511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6135745895940830228617007 9203618843911245342925511)
          ·
            refine ⟨13805428265866868014388267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9203618843911245342925511 13805428265866868014388267)
            ·
              refine ⟨20708142398800302021582401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13805428265866868014388267 20708142398800302021582401)
              ·
                refine ⟨15531106799100226516186801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20708142398800302021582401 15531106799100226516186801)
                ·
                  refine ⟨11648330099325169887140101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15531106799100226516186801 11648330099325169887140101)
                  ·
                    refine ⟨2184061893623469353838769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11648330099325169887140101 2184061893623469353838769)
                    ·
                      refine ⟨1638046420217602015379077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184061893623469353838769 1638046420217602015379077)
                      ·
                        rfl

theorem cell23_3190084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_3190084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190084 prefixEnd_3190084 := by exact prefixLift 3190084
  have htrace : WordTrace (prefixWord ++ tailWord_3190084) baseStart_3190084 baseEnd_3190084 := by
    simpa [prefixWord, tailWord_3190084, baseEnd_3190084] using wordTrace_append hprefix tailTrace_3190084
  have hstable : (prefixWord ++ tailWord_3190084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190084).length < 2 ^ (prefixWord ++ tailWord_3190084).sum := by decide
  have hdescent : baseEnd_3190084 < baseStart_3190084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190113 : List Nat := [1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 7]
def baseStart_3190113 : Nat := 118140960795 + 3190113 * 2 ^ 59
def prefixEnd_3190113 : Nat := 4983230072969 + 3 ^ 40 * 3190113 * 2
def baseEnd_3190113 : Nat := 1638061311156582401916443

theorem tailTrace_3190113 : CollatzResearch.WordTrace tailWord_3190113 prefixEnd_3190113 1638061311156582401916443 := by
  unfold tailWord_3190113
  simp only [CollatzResearch.WordTrace]
  refine ⟨116352979891772903769542993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77568653261181935846361995 116352979891772903769542993)
  ·
    refine ⟨87264734918829677827157245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116352979891772903769542993 87264734918829677827157245)
    ·
      refine ⟨32724275594561129185183967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87264734918829677827157245 32724275594561129185183967)
      ·
        refine ⟨49086413391841693777775951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32724275594561129185183967 49086413391841693777775951)
        ·
          refine ⟨73629620087762540666663927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49086413391841693777775951 73629620087762540666663927)
          ·
            refine ⟨110444430131643810999995891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73629620087762540666663927 110444430131643810999995891)
            ·
              refine ⟨165666645197465716499993837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110444430131643810999995891 165666645197465716499993837)
              ·
                refine ⟨62124991949049643687497689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 165666645197465716499993837 62124991949049643687497689)
                ·
                  refine ⟨46593743961787232765623267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62124991949049643687497689 46593743961787232765623267)
                  ·
                    refine ⟨69890615942680849148434901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46593743961787232765623267 69890615942680849148434901)
                    ·
                      refine ⟨1638061311156582401916443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69890615942680849148434901 1638061311156582401916443)
                      ·
                        rfl

theorem cell23_3190113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_3190113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190113 prefixEnd_3190113 := by exact prefixLift 3190113
  have htrace : WordTrace (prefixWord ++ tailWord_3190113) baseStart_3190113 baseEnd_3190113 := by
    simpa [prefixWord, tailWord_3190113, baseEnd_3190113] using wordTrace_append hprefix tailTrace_3190113
  have hstable : (prefixWord ++ tailWord_3190113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190113).length < 2 ^ (prefixWord ++ tailWord_3190113).sum := by decide
  have hdescent : baseEnd_3190113 < baseStart_3190113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190117 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_3190117 : Nat := 118140960795 + 3190117 * 2 ^ 59
def prefixEnd_3190117 : Nat := 4983230072969 + 3 ^ 40 * 3190117 * 2
def baseEnd_3190117 : Nat := 1638063365079200386266425

theorem tailTrace_3190117 : CollatzResearch.WordTrace tailWord_3190117 prefixEnd_3190117 1638063365079200386266425 := by
  unfold tailWord_3190117
  simp only [CollatzResearch.WordTrace]
  refine ⟨116353125783758412452688605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77568750522505608301792403 116353125783758412452688605)
  ·
    refine ⟨43632422168909404669758227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116353125783758412452688605 43632422168909404669758227)
    ·
      refine ⟨65448633253364107004637341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43632422168909404669758227 65448633253364107004637341)
      ·
        refine ⟨24543237470011540126739003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65448633253364107004637341 24543237470011540126739003)
        ·
          refine ⟨36814856205017310190108505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24543237470011540126739003 36814856205017310190108505)
          ·
            refine ⟨27611142153762982642581379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36814856205017310190108505 27611142153762982642581379)
            ·
              refine ⟨41416713230644473963872069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27611142153762982642581379 41416713230644473963872069)
              ·
                refine ⟨7765633730745838868226013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41416713230644473963872069 7765633730745838868226013)
                ·
                  refine ⟨2912112649029689575584755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7765633730745838868226013 2912112649029689575584755)
                  ·
                    refine ⟨4368168973544534363377133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2912112649029689575584755 4368168973544534363377133)
                    ·
                      refine ⟨1638063365079200386266425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4368168973544534363377133 1638063365079200386266425)
                      ·
                        rfl

theorem cell23_3190117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_3190117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190117 prefixEnd_3190117 := by exact prefixLift 3190117
  have htrace : WordTrace (prefixWord ++ tailWord_3190117) baseStart_3190117 baseEnd_3190117 := by
    simpa [prefixWord, tailWord_3190117, baseEnd_3190117] using wordTrace_append hprefix tailTrace_3190117
  have hstable : (prefixWord ++ tailWord_3190117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190117).length < 2 ^ (prefixWord ++ tailWord_3190117).sum := by decide
  have hdescent : baseEnd_3190117 < baseStart_3190117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190127 : List Nat := [1, 1, 2, 1, 3, 1, 4, 3, 2, 3, 2]
def baseStart_3190127 : Nat := 118140960795 + 3190127 * 2 ^ 59
def prefixEnd_3190127 : Nat := 4983230072969 + 3 ^ 40 * 3190127 * 2
def baseEnd_3190127 : Nat := 1638068499885745347141379

theorem tailTrace_3190127 : CollatzResearch.WordTrace tailWord_3190127 prefixEnd_3190127 1638068499885745347141379 := by
  unfold tailWord_3190127
  simp only [CollatzResearch.WordTrace]
  refine ⟨116353490513722184160552635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77568993675814789440368423 116353490513722184160552635)
  ·
    refine ⟨174530235770583276240828953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116353490513722184160552635 174530235770583276240828953)
    ·
      refine ⟨130897676827937457180621715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174530235770583276240828953 130897676827937457180621715)
      ·
        refine ⟨196346515241906185770932573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130897676827937457180621715 196346515241906185770932573)
        ·
          refine ⟨73629943215714819664099715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196346515241906185770932573 73629943215714819664099715)
          ·
            refine ⟨110444914823572229496149573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73629943215714819664099715 110444914823572229496149573)
            ·
              refine ⟨20708421529419793030528045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110444914823572229496149573 20708421529419793030528045)
              ·
                refine ⟨7765658073532422386448017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20708421529419793030528045 7765658073532422386448017)
                ·
                  refine ⟨5824243555149316789836013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7765658073532422386448017 5824243555149316789836013)
                  ·
                    refine ⟨2184091333180993796188505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5824243555149316789836013 2184091333180993796188505)
                    ·
                      refine ⟨1638068499885745347141379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184091333180993796188505 1638068499885745347141379)
                      ·
                        rfl

theorem cell23_3190127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 3, 2, 3, 2].length) (baseStart_3190127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190127 prefixEnd_3190127 := by exact prefixLift 3190127
  have htrace : WordTrace (prefixWord ++ tailWord_3190127) baseStart_3190127 baseEnd_3190127 := by
    simpa [prefixWord, tailWord_3190127, baseEnd_3190127] using wordTrace_append hprefix tailTrace_3190127
  have hstable : (prefixWord ++ tailWord_3190127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190127).length < 2 ^ (prefixWord ++ tailWord_3190127).sum := by decide
  have hdescent : baseEnd_3190127 < baseStart_3190127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190170 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3190170 : Nat := 118140960795 + 3190170 * 2 ^ 59
def prefixEnd_3190170 : Nat := 4983230072969 + 3 ^ 40 * 3190170 * 2
def baseEnd_3190170 : Nat := 1638090579553888678903681

theorem tailTrace_3190170 : CollatzResearch.WordTrace tailWord_3190170 prefixEnd_3190170 1638090579553888678903681 := by
  unfold tailWord_3190170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29088764713141600626091991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77570039235044268336245309 29088764713141600626091991)
  ·
    refine ⟨43633147069712400939137987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29088764713141600626091991 43633147069712400939137987)
    ·
      refine ⟨65449720604568601408706981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43633147069712400939137987 65449720604568601408706981)
      ·
        refine ⟨12271822613356612764132559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65449720604568601408706981 12271822613356612764132559)
        ·
          refine ⟨18407733920034919146198839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12271822613356612764132559 18407733920034919146198839)
          ·
            refine ⟨27611600880052378719298259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18407733920034919146198839 27611600880052378719298259)
            ·
              refine ⟨41417401320078568078947389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27611600880052378719298259 41417401320078568078947389)
              ·
                refine ⟨15531525495029463029605271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41417401320078568078947389 15531525495029463029605271)
                ·
                  refine ⟨23297288242544194544407907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15531525495029463029605271 23297288242544194544407907)
                  ·
                    refine ⟨34945932363816291816611861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23297288242544194544407907 34945932363816291816611861)
                    ·
                      refine ⟨1638090579553888678903681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34945932363816291816611861 1638090579553888678903681)
                      ·
                        rfl

theorem cell23_3190170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3190170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190170 prefixEnd_3190170 := by exact prefixLift 3190170
  have htrace : WordTrace (prefixWord ++ tailWord_3190170) baseStart_3190170 baseEnd_3190170 := by
    simpa [prefixWord, tailWord_3190170, baseEnd_3190170] using wordTrace_append hprefix tailTrace_3190170
  have hstable : (prefixWord ++ tailWord_3190170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190170).length < 2 ^ (prefixWord ++ tailWord_3190170).sum := by decide
  have hdescent : baseEnd_3190170 < baseStart_3190170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190184 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3190184 : Nat := 118140960795 + 3190184 * 2 ^ 59
def prefixEnd_3190184 : Nat := 4983230072969 + 3 ^ 40 * 3190184 * 2
def baseEnd_3190184 : Nat := 546032589427683874709539

theorem tailTrace_3190184 : CollatzResearch.WordTrace tailWord_3190184 prefixEnd_3190184 546032589427683874709539 := by
  unfold tailWord_3190184
  simp only [CollatzResearch.WordTrace]
  refine ⟨58177784737257841447688803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77570379649677121930251737 58177784737257841447688803)
  ·
    refine ⟨87266677105886762171533205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58177784737257841447688803 87266677105886762171533205)
    ·
      refine ⟨4090625489338441976790619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87266677105886762171533205 4090625489338441976790619)
      ·
        refine ⟨6135938234007662965185929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4090625489338441976790619 6135938234007662965185929)
        ·
          refine ⟨4601953675505747223889447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6135938234007662965185929 4601953675505747223889447)
          ·
            refine ⟨6902930513258620835834171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4601953675505747223889447 6902930513258620835834171)
            ·
              refine ⟨10354395769887931253751257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6902930513258620835834171 10354395769887931253751257)
              ·
                refine ⟨7765796827415948440313443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10354395769887931253751257 7765796827415948440313443)
                ·
                  refine ⟨11648695241123922660470165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7765796827415948440313443 11648695241123922660470165)
                  ·
                    refine ⟨546032589427683874709539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11648695241123922660470165 546032589427683874709539)
                    ·
                      rfl

theorem cell23_3190184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3190184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190184 prefixEnd_3190184 := by exact prefixLift 3190184
  have htrace : WordTrace (prefixWord ++ tailWord_3190184) baseStart_3190184 baseEnd_3190184 := by
    simpa [prefixWord, tailWord_3190184, baseEnd_3190184] using wordTrace_append hprefix tailTrace_3190184
  have hstable : (prefixWord ++ tailWord_3190184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190184).length < 2 ^ (prefixWord ++ tailWord_3190184).sum := by decide
  have hdescent : baseEnd_3190184 < baseStart_3190184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190207 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 3]
def baseStart_3190207 : Nat := 118140960795 + 3190207 * 2 ^ 59
def prefixEnd_3190207 : Nat := 4983230072969 + 3 ^ 40 * 3190207 * 2
def baseEnd_3190207 : Nat := 1638109578338105034141011

theorem tailTrace_3190207 : CollatzResearch.WordTrace tailWord_3190207 prefixEnd_3190207 1638109578338105034141011 := by
  unfold tailWord_3190207
  simp only [CollatzResearch.WordTrace]
  refine ⟨116356408353432357823464875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77570938902288238548976583 116356408353432357823464875)
  ·
    refine ⟨174534612530148536735197313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116356408353432357823464875 174534612530148536735197313)
    ·
      refine ⟨130900959397611402551397985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174534612530148536735197313 130900959397611402551397985)
      ·
        refine ⟨98175719548208551913548489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130900959397611402551397985 98175719548208551913548489)
        ·
          refine ⟨73631789661156413935161367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98175719548208551913548489 73631789661156413935161367)
          ·
            refine ⟨110447684491734620902742051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73631789661156413935161367 110447684491734620902742051)
            ·
              refine ⟨165671526737601931354113077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110447684491734620902742051 165671526737601931354113077)
              ·
                refine ⟨15531705631650181064448101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165671526737601931354113077 15531705631650181064448101)
                ·
                  refine ⟨2912194805934408949584019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15531705631650181064448101 2912194805934408949584019)
                  ·
                    refine ⟨4368292208901613424376029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2912194805934408949584019 4368292208901613424376029)
                    ·
                      refine ⟨1638109578338105034141011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4368292208901613424376029 1638109578338105034141011)
                      ·
                        rfl

theorem cell23_3190207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 4, 1, 3].length) (baseStart_3190207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190207 prefixEnd_3190207 := by exact prefixLift 3190207
  have htrace : WordTrace (prefixWord ++ tailWord_3190207) baseStart_3190207 baseEnd_3190207 := by
    simpa [prefixWord, tailWord_3190207, baseEnd_3190207] using wordTrace_append hprefix tailTrace_3190207
  have hstable : (prefixWord ++ tailWord_3190207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190207).length < 2 ^ (prefixWord ++ tailWord_3190207).sum := by decide
  have hdescent : baseEnd_3190207 < baseStart_3190207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190208 : List Nat := [2, 1, 1, 2, 3, 1, 6, 2, 1, 2, 2]
def baseStart_3190208 : Nat := 118140960795 + 3190208 * 2 ^ 59
def prefixEnd_3190208 : Nat := 4983230072969 + 3 ^ 40 * 3190208 * 2
def baseEnd_3190208 : Nat := 1638110091818759530228507

theorem tailTrace_3190208 : CollatzResearch.WordTrace tailWord_3190208 prefixEnd_3190208 1638110091818759530228507 := by
  unfold tailWord_3190208
  simp only [CollatzResearch.WordTrace]
  refine ⟨58178222413214367497125639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77570963217619156662834185 58178222413214367497125639)
  ·
    refine ⟨87267333619821551245688459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58178222413214367497125639 87267333619821551245688459)
    ·
      refine ⟨130901000429732326868532689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87267333619821551245688459 130901000429732326868532689)
      ·
        refine ⟨98175750322299245151399517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130901000429732326868532689 98175750322299245151399517)
        ·
          refine ⟨36815906370862216931774819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98175750322299245151399517 36815906370862216931774819)
          ·
            refine ⟨55223859556293325397662229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36815906370862216931774819 55223859556293325397662229)
            ·
              refine ⟨2588618416701249628015417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55223859556293325397662229 2588618416701249628015417)
              ·
                refine ⟨1941463812525937221011563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588618416701249628015417 1941463812525937221011563)
                ·
                  refine ⟨2912195718788905831517345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941463812525937221011563 2912195718788905831517345)
                  ·
                    refine ⟨2184146789091679373638009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912195718788905831517345 2184146789091679373638009)
                    ·
                      refine ⟨1638110091818759530228507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184146789091679373638009 1638110091818759530228507)
                      ·
                        rfl

theorem cell23_3190208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 6, 2, 1, 2, 2].length) (baseStart_3190208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190208 prefixEnd_3190208 := by exact prefixLift 3190208
  have htrace : WordTrace (prefixWord ++ tailWord_3190208) baseStart_3190208 baseEnd_3190208 := by
    simpa [prefixWord, tailWord_3190208, baseEnd_3190208] using wordTrace_append hprefix tailTrace_3190208
  have hstable : (prefixWord ++ tailWord_3190208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190208).length < 2 ^ (prefixWord ++ tailWord_3190208).sum := by decide
  have hdescent : baseEnd_3190208 < baseStart_3190208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190234 : List Nat := [3, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2]
def baseStart_3190234 : Nat := 118140960795 + 3190234 * 2 ^ 59
def prefixEnd_3190234 : Nat := 4983230072969 + 3 ^ 40 * 3190234 * 2
def baseEnd_3190234 : Nat := 1638123442315776428503387

theorem tailTrace_3190234 : CollatzResearch.WordTrace tailWord_3190234 prefixEnd_3190234 1638123442315776428503387 := by
  unfold tailWord_3190234
  simp only [CollatzResearch.WordTrace]
  refine ⟨29089348281083635358674439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77571595416223027623131837 29089348281083635358674439)
  ·
    refine ⟨43634022421625453038011659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29089348281083635358674439 43634022421625453038011659)
    ·
      refine ⟨65451033632438179557017489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43634022421625453038011659 65451033632438179557017489)
      ·
        refine ⟨49088275224328634667763117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65451033632438179557017489 49088275224328634667763117)
        ·
          refine ⟨18408103209123238000411169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49088275224328634667763117 18408103209123238000411169)
          ·
            refine ⟨13806077406842428500308377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18408103209123238000411169 13806077406842428500308377)
            ·
              refine ⟨10354558055131821375231283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13806077406842428500308377 10354558055131821375231283)
              ·
                refine ⟨15531837082697732062846925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354558055131821375231283 15531837082697732062846925)
                ·
                  refine ⟨5824438906011649523567597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15531837082697732062846925 5824438906011649523567597)
                  ·
                    refine ⟨2184164589754368571337849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5824438906011649523567597 2184164589754368571337849)
                    ·
                      refine ⟨1638123442315776428503387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184164589754368571337849 1638123442315776428503387)
                      ·
                        rfl

theorem cell23_3190234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_3190234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190234 prefixEnd_3190234 := by exact prefixLift 3190234
  have htrace : WordTrace (prefixWord ++ tailWord_3190234) baseStart_3190234 baseEnd_3190234 := by
    simpa [prefixWord, tailWord_3190234, baseEnd_3190234] using wordTrace_append hprefix tailTrace_3190234
  have hstable : (prefixWord ++ tailWord_3190234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190234).length < 2 ^ (prefixWord ++ tailWord_3190234).sum := by decide
  have hdescent : baseEnd_3190234 < baseStart_3190234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190258 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 2, 1, 3]
def baseStart_3190258 : Nat := 118140960795 + 3190258 * 2 ^ 59
def prefixEnd_3190258 : Nat := 4983230072969 + 3 ^ 40 * 3190258 * 2
def baseEnd_3190258 : Nat := 1638135765851484334603277

theorem tailTrace_3190258 : CollatzResearch.WordTrace tailWord_3190258 prefixEnd_3190258 1638135765851484334603277 := by
  unfold tailWord_3190258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29089567119061898383392857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77572178984165062355714285 29089567119061898383392857)
  ·
    refine ⟨21817175339296423787544643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29089567119061898383392857 21817175339296423787544643)
    ·
      refine ⟨32725763008944635681316965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21817175339296423787544643 32725763008944635681316965)
      ·
        refine ⟨6136080564177119190246931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32725763008944635681316965 6136080564177119190246931)
        ·
          refine ⟨9204120846265678785370397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136080564177119190246931 9204120846265678785370397)
          ·
            refine ⟨3451545317349629544513899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9204120846265678785370397 3451545317349629544513899)
            ·
              refine ⟨5177317976024444316770849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451545317349629544513899 5177317976024444316770849)
              ·
                refine ⟨3882988482018333237578137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177317976024444316770849 3882988482018333237578137)
                ·
                  refine ⟨2912241361513749928183603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3882988482018333237578137 2912241361513749928183603)
                  ·
                    refine ⟨4368362042270624892275405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2912241361513749928183603 4368362042270624892275405)
                    ·
                      refine ⟨1638135765851484334603277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4368362042270624892275405 1638135765851484334603277)
                      ·
                        rfl

theorem cell23_3190258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_3190258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190258 prefixEnd_3190258 := by exact prefixLift 3190258
  have htrace : WordTrace (prefixWord ++ tailWord_3190258) baseStart_3190258 baseEnd_3190258 := by
    simpa [prefixWord, tailWord_3190258, baseEnd_3190258] using wordTrace_append hprefix tailTrace_3190258
  have hstable : (prefixWord ++ tailWord_3190258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190258).length < 2 ^ (prefixWord ++ tailWord_3190258).sum := by decide
  have hdescent : baseEnd_3190258 < baseStart_3190258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190274 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 2, 6]
def baseStart_3190274 : Nat := 118140960795 + 3190274 * 2 ^ 59
def prefixEnd_3190274 : Nat := 4983230072969 + 3 ^ 40 * 3190274 * 2
def baseEnd_3190274 : Nat := 546047993847318757334401

theorem tailTrace_3190274 : CollatzResearch.WordTrace tailWord_3190274 prefixEnd_3190274 546047993847318757334401 := by
  unfold tailWord_3190274
  simp only [CollatzResearch.WordTrace]
  refine ⟨29089713011047407066538469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77572568029459752177435917 29089713011047407066538469)
  ·
    refine ⟨5454321189571388824975963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29089713011047407066538469 5454321189571388824975963)
    ·
      refine ⟨8181481784357083237463945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5454321189571388824975963 8181481784357083237463945)
      ·
        refine ⟨6136111338267812428097959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8181481784357083237463945 6136111338267812428097959)
        ·
          refine ⟨9204167007401718642146939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136111338267812428097959 9204167007401718642146939)
          ·
            refine ⟨13806250511102577963220409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9204167007401718642146939 13806250511102577963220409)
            ·
              refine ⟨10354687883326933472415307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13806250511102577963220409 10354687883326933472415307)
              ·
                refine ⟨15532031824990400208622961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354687883326933472415307 15532031824990400208622961)
                ·
                  refine ⟨11649023868742800156467221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15532031824990400208622961 11649023868742800156467221)
                  ·
                    refine ⟨546047993847318757334401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11649023868742800156467221 546047993847318757334401)
                    ·
                      rfl

theorem cell23_3190274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 2, 6].length) (baseStart_3190274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190274 prefixEnd_3190274 := by exact prefixLift 3190274
  have htrace : WordTrace (prefixWord ++ tailWord_3190274) baseStart_3190274 baseEnd_3190274 := by
    simpa [prefixWord, tailWord_3190274, baseEnd_3190274] using wordTrace_append hprefix tailTrace_3190274
  have hstable : (prefixWord ++ tailWord_3190274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190274).length < 2 ^ (prefixWord ++ tailWord_3190274).sum := by decide
  have hdescent : baseEnd_3190274 < baseStart_3190274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190327 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 5]
def baseStart_3190327 : Nat := 118140960795 + 3190327 * 2 ^ 59
def prefixEnd_3190327 : Nat := 4983230072969 + 3 ^ 40 * 3190327 * 2
def baseEnd_3190327 : Nat := 1638171196016644564640459

theorem tailTrace_3190327 : CollatzResearch.WordTrace tailWord_3190327 prefixEnd_3190327 1638171196016644564640459 := by
  unfold tailWord_3190327
  simp only [CollatzResearch.WordTrace]
  refine ⟨116360785112997618317833235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77573856741998412211888823 116360785112997618317833235)
  ·
    refine ⟨174541177669496427476749853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116360785112997618317833235 174541177669496427476749853)
    ·
      refine ⟨65452941626061160303781195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174541177669496427476749853 65452941626061160303781195)
      ·
        refine ⟨98179412439091740455671793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65452941626061160303781195 98179412439091740455671793)
        ·
          refine ⟨73634559329318805341753845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98179412439091740455671793 73634559329318805341753845)
          ·
            refine ⟨6903239937123638000789423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73634559329318805341753845 6903239937123638000789423)
            ·
              refine ⟨10354859905685457001184135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6903239937123638000789423 10354859905685457001184135)
              ·
                refine ⟨15532289858528185501776203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10354859905685457001184135 15532289858528185501776203)
                ·
                  refine ⟨23298434787792278252664305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15532289858528185501776203 23298434787792278252664305)
                  ·
                    refine ⟨17473826090844208689498229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23298434787792278252664305 17473826090844208689498229)
                    ·
                      refine ⟨1638171196016644564640459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17473826090844208689498229 1638171196016644564640459)
                      ·
                        rfl

theorem cell23_3190327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_3190327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190327 prefixEnd_3190327 := by exact prefixLift 3190327
  have htrace : WordTrace (prefixWord ++ tailWord_3190327) baseStart_3190327 baseEnd_3190327 := by
    simpa [prefixWord, tailWord_3190327, baseEnd_3190327] using wordTrace_append hprefix tailTrace_3190327
  have hstable : (prefixWord ++ tailWord_3190327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190327).length < 2 ^ (prefixWord ++ tailWord_3190327).sum := by decide
  have hdescent : baseEnd_3190327 < baseStart_3190327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190332 : List Nat := [2, 2, 2, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_3190332 : Nat := 118140960795 + 3190332 * 2 ^ 59
def prefixEnd_3190332 : Nat := 4983230072969 + 3 ^ 40 * 3190332 * 2
def baseEnd_3190332 : Nat := 1638173763419917045077937

theorem tailTrace_3190332 : CollatzResearch.WordTrace tailWord_3190332 prefixEnd_3190332 1638173763419917045077937 := by
  unfold tailWord_3190332
  simp only [CollatzResearch.WordTrace]
  refine ⟨58180483738989752085882625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77573978318653002781176833 58180483738989752085882625)
  ·
    refine ⟨43635362804242314064411969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58180483738989752085882625 43635362804242314064411969)
    ·
      refine ⟨32726522103181735548308977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43635362804242314064411969 32726522103181735548308977)
      ·
        refine ⟨24544891577386301661231733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32726522103181735548308977 24544891577386301661231733)
        ·
          refine ⟨2301083585379965780740475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24544891577386301661231733 2301083585379965780740475)
          ·
            refine ⟨3451625378069948671110713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301083585379965780740475 3451625378069948671110713)
            ·
              refine ⟨2588719033552461503333035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451625378069948671110713 2588719033552461503333035)
              ·
                refine ⟨3883078550328692254999553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2588719033552461503333035 3883078550328692254999553)
                ·
                  refine ⟨2912308912746519191249665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883078550328692254999553 2912308912746519191249665)
                  ·
                    refine ⟨2184231684559889393437249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912308912746519191249665 2184231684559889393437249)
                    ·
                      refine ⟨1638173763419917045077937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184231684559889393437249 1638173763419917045077937)
                      ·
                        rfl

theorem cell23_3190332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_3190332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190332 prefixEnd_3190332 := by exact prefixLift 3190332
  have htrace : WordTrace (prefixWord ++ tailWord_3190332) baseStart_3190332 baseEnd_3190332 := by
    simpa [prefixWord, tailWord_3190332, baseEnd_3190332] using wordTrace_append hprefix tailTrace_3190332
  have hstable : (prefixWord ++ tailWord_3190332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190332).length < 2 ^ (prefixWord ++ tailWord_3190332).sum := by decide
  have hdescent : baseEnd_3190332 < baseStart_3190332 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190347 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 5, 4]
def baseStart_3190347 : Nat := 118140960795 + 3190347 * 2 ^ 59
def prefixEnd_3190347 : Nat := 4983230072969 + 3 ^ 40 * 3190347 * 2
def baseEnd_3190347 : Nat := 546060488543244828796789

theorem tailTrace_3190347 : CollatzResearch.WordTrace tailWord_3190347 prefixEnd_3190347 546060488543244828796789 := by
  unfold tailWord_3190347
  simp only [CollatzResearch.WordTrace]
  refine ⟨116361514572925161733561295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77574343048616774489040863 116361514572925161733561295)
  ·
    refine ⟨174542271859387742600341943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116361514572925161733561295 174542271859387742600341943)
    ·
      refine ⟨261813407789081613900512915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174542271859387742600341943 261813407789081613900512915)
      ·
        refine ⟨392720111683622420850769373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261813407789081613900512915 392720111683622420850769373)
        ·
          refine ⟨147270041881358407819038515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392720111683622420850769373 147270041881358407819038515)
          ·
            refine ⟨220905062822037611728557773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147270041881358407819038515 220905062822037611728557773)
            ·
              refine ⟨82839398558264104398209165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220905062822037611728557773 82839398558264104398209165)
              ·
                refine ⟨31064774459349039149328437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 82839398558264104398209165 31064774459349039149328437)
                ·
                  refine ⟨2912322605563972420249541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31064774459349039149328437 2912322605563972420249541)
                  ·
                    refine ⟨546060488543244828796789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2912322605563972420249541 546060488543244828796789)
                    ·
                      rfl

theorem cell23_3190347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 5, 4].length) (baseStart_3190347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190347 prefixEnd_3190347 := by exact prefixLift 3190347
  have htrace : WordTrace (prefixWord ++ tailWord_3190347) baseStart_3190347 baseEnd_3190347 := by
    simpa [prefixWord, tailWord_3190347, baseEnd_3190347] using wordTrace_append hprefix tailTrace_3190347
  have hstable : (prefixWord ++ tailWord_3190347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190347).length < 2 ^ (prefixWord ++ tailWord_3190347).sum := by decide
  have hdescent : baseEnd_3190347 < baseStart_3190347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190354 : List Nat := [3, 2, 2, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3190354 : Nat := 118140960795 + 3190354 * 2 ^ 59
def prefixEnd_3190354 : Nat := 4983230072969 + 3 ^ 40 * 3190354 * 2
def baseEnd_3190354 : Nat := 1638185059994315959002835

theorem tailTrace_3190354 : CollatzResearch.WordTrace tailWord_3190354 prefixEnd_3190354 1638185059994315959002835 := by
  unfold tailWord_3190354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29090442470974950482266529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77574513255933201286044077 29090442470974950482266529)
  ·
    refine ⟨21817831853231212861699897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29090442470974950482266529 21817831853231212861699897)
    ·
      refine ⟨16363373889923409646274923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21817831853231212861699897 16363373889923409646274923)
      ·
        refine ⟨24545060834885114469412385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16363373889923409646274923 24545060834885114469412385)
        ·
          refine ⟨18408795626163835852059289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24545060834885114469412385 18408795626163835852059289)
          ·
            refine ⟨13806596719622876889044467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18408795626163835852059289 13806596719622876889044467)
            ·
              refine ⟨20709895079434315333566701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13806596719622876889044467 20709895079434315333566701)
              ·
                refine ⟨7766210654787868250087513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20709895079434315333566701 7766210654787868250087513)
                ·
                  refine ⟨5824657991090901187565635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7766210654787868250087513 5824657991090901187565635)
                  ·
                    refine ⟨8736986986636351781348453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5824657991090901187565635 8736986986636351781348453)
                    ·
                      refine ⟨1638185059994315959002835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8736986986636351781348453 1638185059994315959002835)
                      ·
                        rfl

theorem cell23_3190354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3190354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190354 prefixEnd_3190354 := by exact prefixLift 3190354
  have htrace : WordTrace (prefixWord ++ tailWord_3190354) baseStart_3190354 baseEnd_3190354 := by
    simpa [prefixWord, tailWord_3190354, baseEnd_3190354] using wordTrace_append hprefix tailTrace_3190354
  have hstable : (prefixWord ++ tailWord_3190354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190354).length < 2 ^ (prefixWord ++ tailWord_3190354).sum := by decide
  have hdescent : baseEnd_3190354 < baseStart_3190354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190377 : List Nat := [1, 2, 1, 1, 1, 4, 3, 4, 6]
def baseStart_3190377 : Nat := 118140960795 + 3190377 * 2 ^ 59
def prefixEnd_3190377 : Nat := 4983230072969 + 3 ^ 40 * 3190377 * 2
def baseEnd_3190377 : Nat := 182021874449929929890581

theorem tailTrace_3190377 : CollatzResearch.WordTrace tailWord_3190377 prefixEnd_3190377 182021874449929929890581 := by
  unfold tailWord_3190377
  simp only [CollatzResearch.WordTrace]
  refine ⟨116362608762816476857153385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77575072508544317904768923 116362608762816476857153385)
  ·
    refine ⟨87271956572112357642865039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116362608762816476857153385 87271956572112357642865039)
    ·
      refine ⟨130907934858168536464297559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87271956572112357642865039 130907934858168536464297559)
      ·
        refine ⟨196361902287252804696446339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130907934858168536464297559 196361902287252804696446339)
        ·
          refine ⟨294542853430879207044669509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196361902287252804696446339 294542853430879207044669509)
          ·
            refine ⟨55226785018289851320875533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294542853430879207044669509 55226785018289851320875533)
            ·
              refine ⟨20710044381858694245328325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55226785018289851320875533 20710044381858694245328325)
              ·
                refine ⟨3883133321598505170999061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20710044381858694245328325 3883133321598505170999061)
                ·
                  refine ⟨182021874449929929890581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3883133321598505170999061 182021874449929929890581)
                  ·
                    rfl

theorem cell23_3190377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 4, 6].length) (baseStart_3190377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190377 prefixEnd_3190377 := by exact prefixLift 3190377
  have htrace : WordTrace (prefixWord ++ tailWord_3190377) baseStart_3190377 baseEnd_3190377 := by
    simpa [prefixWord, tailWord_3190377, baseEnd_3190377] using wordTrace_append hprefix tailTrace_3190377
  have hstable : (prefixWord ++ tailWord_3190377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190377).length < 2 ^ (prefixWord ++ tailWord_3190377).sum := by decide
  have hdescent : baseEnd_3190377 < baseStart_3190377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190428 : List Nat := [2, 2, 3, 2, 4, 1, 1, 2, 6]
def baseStart_3190428 : Nat := 118140960795 + 3190428 * 2 ^ 59
def prefixEnd_3190428 : Nat := 4983230072969 + 3 ^ 40 * 3190428 * 2
def baseEnd_3190428 : Nat := 182024784173638741053055

theorem tailTrace_3190428 : CollatzResearch.WordTrace tailWord_3190428 prefixEnd_3190428 182024784173638741053055 := by
  unfold tailWord_3190428
  simp only [CollatzResearch.WordTrace]
  refine ⟨58182234442815856283629969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77576312590421141711506625 58182234442815856283629969)
  ·
    refine ⟨43636675832111892212722477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58182234442815856283629969 43636675832111892212722477)
    ·
      refine ⟨16363753437041959579770929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43636675832111892212722477 16363753437041959579770929)
      ·
        refine ⟨12272815077781469684828197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16363753437041959579770929 12272815077781469684828197)
        ·
          refine ⟨2301152827084025565905287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12272815077781469684828197 2301152827084025565905287)
          ·
            refine ⟨3451729240626038348857931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301152827084025565905287 3451729240626038348857931)
            ·
              refine ⟨5177593860939057523286897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451729240626038348857931 5177593860939057523286897)
              ·
                refine ⟨3883195395704293142465173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177593860939057523286897 3883195395704293142465173)
                ·
                  refine ⟨182024784173638741053055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3883195395704293142465173 182024784173638741053055)
                  ·
                    rfl

theorem cell23_3190428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_3190428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190428 prefixEnd_3190428 := by exact prefixLift 3190428
  have htrace : WordTrace (prefixWord ++ tailWord_3190428) baseStart_3190428 baseEnd_3190428 := by
    simpa [prefixWord, tailWord_3190428, baseEnd_3190428] using wordTrace_append hprefix tailTrace_3190428
  have hstable : (prefixWord ++ tailWord_3190428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190428).length < 2 ^ (prefixWord ++ tailWord_3190428).sum := by decide
  have hdescent : baseEnd_3190428 < baseStart_3190428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190437 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 3, 6]
def baseStart_3190437 : Nat := 118140960795 + 3190437 * 2 ^ 59
def prefixEnd_3190437 : Nat := 4983230072969 + 3 ^ 40 * 3190437 * 2
def baseEnd_3190437 : Nat := 546075892962879711421651

theorem tailTrace_3190437 : CollatzResearch.WordTrace tailWord_3190437 prefixEnd_3190437 546075892962879711421651 := by
  unfold tailWord_3190437
  simp only [CollatzResearch.WordTrace]
  refine ⟨116364797142599107104337565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77576531428399404736225043 116364797142599107104337565)
  ·
    refine ⟨43636798928474665164126587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116364797142599107104337565 43636798928474665164126587)
    ·
      refine ⟨65455198392711997746189881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43636798928474665164126587 65455198392711997746189881)
      ·
        refine ⟨49091398794533998309642411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65455198392711997746189881 49091398794533998309642411)
        ·
          refine ⟨73637098191800997464463617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49091398794533998309642411 73637098191800997464463617)
          ·
            refine ⟨55227823643850748098347713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73637098191800997464463617 55227823643850748098347713)
            ·
              refine ⟨41420867732888061073760785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55227823643850748098347713 41420867732888061073760785)
              ·
                refine ⟨31065650799666045805320589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41420867732888061073760785 31065650799666045805320589)
                ·
                  refine ⟨11649619049874767176995221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31065650799666045805320589 11649619049874767176995221)
                  ·
                    refine ⟨546075892962879711421651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11649619049874767176995221 546075892962879711421651)
                    ·
                      rfl

theorem cell23_3190437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_3190437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190437 prefixEnd_3190437 := by exact prefixLift 3190437
  have htrace : WordTrace (prefixWord ++ tailWord_3190437) baseStart_3190437 baseEnd_3190437 := by
    simpa [prefixWord, tailWord_3190437, baseEnd_3190437] using wordTrace_append hprefix tailTrace_3190437
  have hstable : (prefixWord ++ tailWord_3190437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190437).length < 2 ^ (prefixWord ++ tailWord_3190437).sum := by decide
  have hdescent : baseEnd_3190437 < baseStart_3190437 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190461 : List Nat := [1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 4]
def baseStart_3190461 : Nat := 118140960795 + 3190461 * 2 ^ 59
def prefixEnd_3190461 : Nat := 4983230072969 + 3 ^ 40 * 3190461 * 2
def baseEnd_3190461 : Nat := 1638240002424347040364843

theorem tailTrace_3190461 : CollatzResearch.WordTrace tailWord_3190461 prefixEnd_3190461 1638240002424347040364843 := by
  unfold tailWord_3190461
  simp only [CollatzResearch.WordTrace]
  refine ⟨116365672494512159203211237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77577114996341439468807491 116365672494512159203211237)
  ·
    refine ⟨21818563592721029850602107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116365672494512159203211237 21818563592721029850602107)
    ·
      refine ⟨32727845389081544775903161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21818563592721029850602107 32727845389081544775903161)
      ·
        refine ⟨24545884041811158581927371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32727845389081544775903161 24545884041811158581927371)
        ·
          refine ⟨36818826062716737872891057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24545884041811158581927371 36818826062716737872891057)
          ·
            refine ⟨27614119547037553404668293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36818826062716737872891057 27614119547037553404668293)
            ·
              refine ⟨5177647415069541263375305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27614119547037553404668293 5177647415069541263375305)
              ·
                refine ⟨3883235561302155947531479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5177647415069541263375305 3883235561302155947531479)
                ·
                  refine ⟨5824853341953233921297219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883235561302155947531479 5824853341953233921297219)
                  ·
                    refine ⟨8737280012929850881945829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5824853341953233921297219 8737280012929850881945829)
                    ·
                      refine ⟨1638240002424347040364843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8737280012929850881945829 1638240002424347040364843)
                      ·
                        rfl

theorem cell23_3190461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_3190461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190461 prefixEnd_3190461 := by exact prefixLift 3190461
  have htrace : WordTrace (prefixWord ++ tailWord_3190461) baseStart_3190461 baseEnd_3190461 := by
    simpa [prefixWord, tailWord_3190461, baseEnd_3190461] using wordTrace_append hprefix tailTrace_3190461
  have hstable : (prefixWord ++ tailWord_3190461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190461).length < 2 ^ (prefixWord ++ tailWord_3190461).sum := by decide
  have hdescent : baseEnd_3190461 < baseStart_3190461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190466 : List Nat := [3, 5, 1, 2, 2, 1, 1, 3, 1, 4]
def baseStart_3190466 : Nat := 118140960795 + 3190466 * 2 ^ 59
def prefixEnd_3190466 : Nat := 4983230072969 + 3 ^ 40 * 3190466 * 2
def baseEnd_3190466 : Nat := 546080856609206506934107

theorem tailTrace_3190466 : CollatzResearch.WordTrace tailWord_3190466 prefixEnd_3190466 546080856609206506934107 := by
  unfold tailWord_3190466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29091463714873511264285813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77577236572996030038095501 29091463714873511264285813)
  ·
    refine ⟨2727324723269391681026795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29091463714873511264285813 2727324723269391681026795)
    ·
      refine ⟨4090987084904087521540193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727324723269391681026795 4090987084904087521540193)
      ·
        refine ⟨3068240313678065641155145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4090987084904087521540193 3068240313678065641155145)
        ·
          refine ⟨2301180235258549230866359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3068240313678065641155145 2301180235258549230866359)
          ·
            refine ⟨3451770352887823846299539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301180235258549230866359 3451770352887823846299539)
            ·
              refine ⟨5177655529331735769449309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3451770352887823846299539 5177655529331735769449309)
              ·
                refine ⟨1941620823499400913543491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5177655529331735769449309 1941620823499400913543491)
                ·
                  refine ⟨2912431235249101370315237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941620823499400913543491 2912431235249101370315237)
                  ·
                    refine ⟨546080856609206506934107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2912431235249101370315237 546080856609206506934107)
                    ·
                      rfl

theorem cell23_3190466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_3190466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190466 prefixEnd_3190466 := by exact prefixLift 3190466
  have htrace : WordTrace (prefixWord ++ tailWord_3190466) baseStart_3190466 baseEnd_3190466 := by
    simpa [prefixWord, tailWord_3190466, baseEnd_3190466] using wordTrace_append hprefix tailTrace_3190466
  have hstable : (prefixWord ++ tailWord_3190466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190466).length < 2 ^ (prefixWord ++ tailWord_3190466).sum := by decide
  have hdescent : baseEnd_3190466 < baseStart_3190466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190481 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 3]
def baseStart_3190481 : Nat := 118140960795 + 3190481 * 2 ^ 59
def prefixEnd_3190481 : Nat := 4983230072969 + 3 ^ 40 * 3190481 * 2
def baseEnd_3190481 : Nat := 1638250272037436962114751

theorem tailTrace_3190481 : CollatzResearch.WordTrace tailWord_3190481 prefixEnd_3190481 1638250272037436962114751 := by
  unfold tailWord_3190481
  simp only [CollatzResearch.WordTrace]
  refine ⟨116366401954439702618939297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77577601302959801745959531 116366401954439702618939297)
  ·
    refine ⟨87274801465829776964204473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116366401954439702618939297 87274801465829776964204473)
    ·
      refine ⟨65456101099372332723153355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87274801465829776964204473 65456101099372332723153355)
      ·
        refine ⟨98184151649058499084730033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65456101099372332723153355 98184151649058499084730033)
        ·
          refine ⟨73638113736793874313547525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98184151649058499084730033 73638113736793874313547525)
          ·
            refine ⟨13807146325648851433790161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73638113736793874313547525 13807146325648851433790161)
            ·
              refine ⟨10355359744236638575342621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13807146325648851433790161 10355359744236638575342621)
              ·
                refine ⟨3883259904088739465753483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10355359744236638575342621 3883259904088739465753483)
                ·
                  refine ⟨5824889856133109198630225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3883259904088739465753483 5824889856133109198630225)
                  ·
                    refine ⟨4368667392099831898972669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5824889856133109198630225 4368667392099831898972669)
                    ·
                      refine ⟨1638250272037436962114751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4368667392099831898972669 1638250272037436962114751)
                      ·
                        rfl

theorem cell23_3190481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 1, 2, 3].length) (baseStart_3190481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190481 prefixEnd_3190481 := by exact prefixLift 3190481
  have htrace : WordTrace (prefixWord ++ tailWord_3190481) baseStart_3190481 baseEnd_3190481 := by
    simpa [prefixWord, tailWord_3190481, baseEnd_3190481] using wordTrace_append hprefix tailTrace_3190481
  have hstable : (prefixWord ++ tailWord_3190481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190481).length < 2 ^ (prefixWord ++ tailWord_3190481).sum := by decide
  have hdescent : baseEnd_3190481 < baseStart_3190481 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190484 : List Nat := [2, 4, 1, 3, 1, 1, 11]
def baseStart_3190484 : Nat := 118140960795 + 3190484 * 2 ^ 59
def prefixEnd_3190484 : Nat := 4983230072969 + 3 ^ 40 * 3190484 * 2
def baseEnd_3190484 : Nat := 20225331018264203091077

theorem tailTrace_3190484 : CollatzResearch.WordTrace tailWord_3190484 prefixEnd_3190484 20225331018264203091077 := by
  unfold tailWord_3190484
  simp only [CollatzResearch.WordTrace]
  refine ⟨58183255686714417065649253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77577674248952556087532337 58183255686714417065649253)
  ·
    refine ⟨10909360441258953199809235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58183255686714417065649253 10909360441258953199809235)
    ·
      refine ⟨16364040661888429799713853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10909360441258953199809235 16364040661888429799713853)
      ·
        refine ⟨6136515248208161174892695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16364040661888429799713853 6136515248208161174892695)
        ·
          refine ⟨9204772872312241762339043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136515248208161174892695 9204772872312241762339043)
          ·
            refine ⟨13807159308468362643508565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9204772872312241762339043 13807159308468362643508565)
            ·
              refine ⟨20225331018264203091077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13807159308468362643508565 20225331018264203091077)
              ·
                rfl

theorem cell23_3190484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 11].length) (baseStart_3190484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190484 prefixEnd_3190484 := by exact prefixLift 3190484
  have htrace : WordTrace (prefixWord ++ tailWord_3190484) baseStart_3190484 baseEnd_3190484 := by
    simpa [prefixWord, tailWord_3190484, baseEnd_3190484] using wordTrace_append hprefix tailTrace_3190484
  have hstable : (prefixWord ++ tailWord_3190484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190484).length < 2 ^ (prefixWord ++ tailWord_3190484).sum := by decide
  have hdescent : baseEnd_3190484 < baseStart_3190484 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190546 : List Nat := [3, 2, 4, 1, 1, 3, 2, 2, 1, 2, 2]
def baseStart_3190546 : Nat := 118140960795 + 3190546 * 2 ^ 59
def prefixEnd_3190546 : Nat := 4983230072969 + 3 ^ 40 * 3190546 * 2
def baseEnd_3190546 : Nat := 1638283648279979207801953

theorem tailTrace_3190546 : CollatzResearch.WordTrace tailWord_3190546 prefixEnd_3190546 1638283648279979207801953 := by
  unfold tailWord_3190546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29092193174801054680013873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77579181799469479146703661 29092193174801054680013873)
  ·
    refine ⟨21819144881100791010010405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29092193174801054680013873 21819144881100791010010405)
    ·
      refine ⟨4091089665206398314376951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21819144881100791010010405 4091089665206398314376951)
      ·
        refine ⟨6136634497809597471565427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4091089665206398314376951 6136634497809597471565427)
        ·
          refine ⟨9204951746714396207348141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6136634497809597471565427 9204951746714396207348141)
          ·
            refine ⟨3451856905017898577755553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9204951746714396207348141 3451856905017898577755553)
            ·
              refine ⟨2588892678763423933316665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3451856905017898577755553 2588892678763423933316665)
              ·
                refine ⟨1941669509072567949987499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2588892678763423933316665 1941669509072567949987499)
                ·
                  refine ⟨2912504263608851924981249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941669509072567949987499 2912504263608851924981249)
                  ·
                    refine ⟨2184378197706638943735937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2912504263608851924981249 2184378197706638943735937)
                    ·
                      refine ⟨1638283648279979207801953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184378197706638943735937 1638283648279979207801953)
                      ·
                        rfl

theorem cell23_3190546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 2, 2, 1, 2, 2].length) (baseStart_3190546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190546 prefixEnd_3190546 := by exact prefixLift 3190546
  have htrace : WordTrace (prefixWord ++ tailWord_3190546) baseStart_3190546 baseEnd_3190546 := by
    simpa [prefixWord, tailWord_3190546, baseEnd_3190546] using wordTrace_append hprefix tailTrace_3190546
  have hstable : (prefixWord ++ tailWord_3190546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190546).length < 2 ^ (prefixWord ++ tailWord_3190546).sum := by decide
  have hdescent : baseEnd_3190546 < baseStart_3190546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190568 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_3190568 : Nat := 118140960795 + 3190568 * 2 ^ 59
def prefixEnd_3190568 : Nat := 4983230072969 + 3 ^ 40 * 3190568 * 2
def baseEnd_3190568 : Nat := 1638294944854378121726851

theorem tailTrace_3190568 : CollatzResearch.WordTrace tailWord_3190568 prefixEnd_3190568 1638294944854378121726851 := by
  unfold tailWord_3190568
  simp only [CollatzResearch.WordTrace]
  refine ⟨58184787552562258238678179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77579716736749677651570905 58184787552562258238678179)
  ·
    refine ⟨87277181328843387358017269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58184787552562258238678179 87277181328843387358017269)
    ·
      refine ⟨8182235749579067564814119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87277181328843387358017269 8182235749579067564814119)
      ·
        refine ⟨12273353624368601347221179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182235749579067564814119 12273353624368601347221179)
        ·
          refine ⟨18410030436552902020831769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12273353624368601347221179 18410030436552902020831769)
          ·
            refine ⟨13807522827414676515623827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18410030436552902020831769 13807522827414676515623827)
            ·
              refine ⟨20711284241122014773435741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13807522827414676515623827 20711284241122014773435741)
              ·
                refine ⟨7766731590420755540038403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20711284241122014773435741 7766731590420755540038403)
                ·
                  refine ⟨11650097385631133310057605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7766731590420755540038403 11650097385631133310057605)
                  ·
                    refine ⟨2184393259805837495635801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11650097385631133310057605 2184393259805837495635801)
                    ·
                      refine ⟨1638294944854378121726851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184393259805837495635801 1638294944854378121726851)
                      ·
                        rfl

theorem cell23_3190568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_3190568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190568 prefixEnd_3190568 := by exact prefixLift 3190568
  have htrace : WordTrace (prefixWord ++ tailWord_3190568) baseStart_3190568 baseEnd_3190568 := by
    simpa [prefixWord, tailWord_3190568, baseEnd_3190568] using wordTrace_append hprefix tailTrace_3190568
  have hstable : (prefixWord ++ tailWord_3190568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190568).length < 2 ^ (prefixWord ++ tailWord_3190568).sum := by decide
  have hdescent : baseEnd_3190568 < baseStart_3190568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190641 : List Nat := [1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 4]
def baseStart_3190641 : Nat := 118140960795 + 3190641 * 2 ^ 59
def prefixEnd_3190641 : Nat := 4983230072969 + 3 ^ 40 * 3190641 * 2
def baseEnd_3190641 : Nat := 1638332428942156336114015

theorem tailTrace_3190641 : CollatzResearch.WordTrace tailWord_3190641 prefixEnd_3190641 1638332428942156336114015 := by
  unfold tailWord_3190641
  simp only [CollatzResearch.WordTrace]
  refine ⟨116372237633860049944763777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77581491755906699963175851 116372237633860049944763777)
  ·
    refine ⟨87279178225395037458572833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116372237633860049944763777 87279178225395037458572833)
    ·
      refine ⟨65459383669046278093929625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87279178225395037458572833 65459383669046278093929625)
      ·
        refine ⟨49094537751784708570447219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65459383669046278093929625 49094537751784708570447219)
        ·
          refine ⟨73641806627677062855670829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49094537751784708570447219 73641806627677062855670829)
          ·
            refine ⟨27615677485378898570876561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73641806627677062855670829 27615677485378898570876561)
            ·
              refine ⟨20711758114034173928157421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27615677485378898570876561 20711758114034173928157421)
              ·
                refine ⟨7766909292762815223059033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20711758114034173928157421 7766909292762815223059033)
                ·
                  refine ⟨5825181969572111417294275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7766909292762815223059033 5825181969572111417294275)
                  ·
                    refine ⟨8737772954358167125941413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5825181969572111417294275 8737772954358167125941413)
                    ·
                      refine ⟨1638332428942156336114015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8737772954358167125941413 1638332428942156336114015)
                      ·
                        rfl

theorem cell23_3190641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_3190641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190641 prefixEnd_3190641 := by exact prefixLift 3190641
  have htrace : WordTrace (prefixWord ++ tailWord_3190641) baseStart_3190641 baseEnd_3190641 := by
    simpa [prefixWord, tailWord_3190641, baseEnd_3190641] using wordTrace_append hprefix tailTrace_3190641
  have hstable : (prefixWord ++ tailWord_3190641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190641).length < 2 ^ (prefixWord ++ tailWord_3190641).sum := by decide
  have hdescent : baseEnd_3190641 < baseStart_3190641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190695 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_3190695 : Nat := 118140960795 + 3190695 * 2 ^ 59
def prefixEnd_3190695 : Nat := 4983230072969 + 3 ^ 40 * 3190695 * 2
def baseEnd_3190695 : Nat := 1638360156897499124838767

theorem tailTrace_3190695 : CollatzResearch.WordTrace tailWord_3190695 prefixEnd_3190695 1638360156897499124838767 := by
  unfold tailWord_3190695
  simp only [CollatzResearch.WordTrace]
  refine ⟨116374207175664417167229539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77582804783776278111486359 116374207175664417167229539)
  ·
    refine ⟨174561310763496625750844309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116374207175664417167229539 174561310763496625750844309)
    ·
      refine ⟨8182561442038904332070827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 174561310763496625750844309 8182561442038904332070827)
      ·
        refine ⟨12273842163058356498106241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182561442038904332070827 12273842163058356498106241)
        ·
          refine ⟨9205381622293767373579681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12273842163058356498106241 9205381622293767373579681)
          ·
            refine ⟨6904036216720325530184761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9205381622293767373579681 6904036216720325530184761)
            ·
              refine ⟨5178027162540244147638571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904036216720325530184761 5178027162540244147638571)
              ·
                refine ⟨7767040743810366221457857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178027162540244147638571 7767040743810366221457857)
                ·
                  refine ⟨5825280557857774666093393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7767040743810366221457857 5825280557857774666093393)
                  ·
                    refine ⟨4368960418393330999570045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825280557857774666093393 4368960418393330999570045)
                    ·
                      refine ⟨1638360156897499124838767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4368960418393330999570045 1638360156897499124838767)
                      ·
                        rfl

theorem cell23_3190695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_3190695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190695 prefixEnd_3190695 := by exact prefixLift 3190695
  have htrace : WordTrace (prefixWord ++ tailWord_3190695) baseStart_3190695 baseEnd_3190695 := by
    simpa [prefixWord, tailWord_3190695, baseEnd_3190695] using wordTrace_append hprefix tailTrace_3190695
  have hstable : (prefixWord ++ tailWord_3190695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190695).length < 2 ^ (prefixWord ++ tailWord_3190695).sum := by decide
  have hdescent : baseEnd_3190695 < baseStart_3190695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190704 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7]
def baseStart_3190704 : Nat := 118140960795 + 3190704 * 2 ^ 59
def prefixEnd_3190704 : Nat := 4983230072969 + 3 ^ 40 * 3190704 * 2
def baseEnd_3190704 : Nat := 1638364778223389589626225

theorem tailTrace_3190704 : CollatzResearch.WordTrace tailWord_3190704 prefixEnd_3190704 1638364778223389589626225 := by
  unfold tailWord_3190704
  simp only [CollatzResearch.WordTrace]
  refine ⟨58187267716315905852153583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77583023621754541136204777 58187267716315905852153583)
  ·
    refine ⟨87280901574473858778230375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58187267716315905852153583 87280901574473858778230375)
    ·
      refine ⟨130921352361710788167345563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87280901574473858778230375 130921352361710788167345563)
      ·
        refine ⟨196382028542566182251018345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130921352361710788167345563 196382028542566182251018345)
        ·
          refine ⟨147286521406924636688263759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196382028542566182251018345 147286521406924636688263759)
          ·
            refine ⟨220929782110386955032395639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147286521406924636688263759 220929782110386955032395639)
            ·
              refine ⟨331394673165580432548593459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220929782110386955032395639 331394673165580432548593459)
              ·
                refine ⟨497092009748370648822890189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331394673165580432548593459 497092009748370648822890189)
                ·
                  refine ⟨186409503655638993308583821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 497092009748370648822890189 186409503655638993308583821)
                  ·
                    refine ⟨69903563870864622490718933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 186409503655638993308583821 69903563870864622490718933)
                    ·
                      refine ⟨1638364778223389589626225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69903563870864622490718933 1638364778223389589626225)
                      ·
                        rfl

theorem cell23_3190704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_3190704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190704 prefixEnd_3190704 := by exact prefixLift 3190704
  have htrace : WordTrace (prefixWord ++ tailWord_3190704) baseStart_3190704 baseEnd_3190704 := by
    simpa [prefixWord, tailWord_3190704, baseEnd_3190704] using wordTrace_append hprefix tailTrace_3190704
  have hstable : (prefixWord ++ tailWord_3190704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190704).length < 2 ^ (prefixWord ++ tailWord_3190704).sum := by decide
  have hdescent : baseEnd_3190704 < baseStart_3190704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190731 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 4]
def baseStart_3190731 : Nat := 118140960795 + 3190731 * 2 ^ 59
def prefixEnd_3190731 : Nat := 4983230072969 + 3 ^ 40 * 3190731 * 2
def baseEnd_3190731 : Nat := 1638378642201060983988601

theorem tailTrace_3190731 : CollatzResearch.WordTrace tailWord_3190731 prefixEnd_3190731 1638378642201060983988601 := by
  unfold tailWord_3190731
  simp only [CollatzResearch.WordTrace]
  refine ⟨116375520203533995315540047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77583680135689330210360031 116375520203533995315540047)
  ·
    refine ⟨174563280305300992973310071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116375520203533995315540047 174563280305300992973310071)
    ·
      refine ⟨261844920457951489459965107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174563280305300992973310071 261844920457951489459965107)
      ·
        refine ⟨392767380686927234189947661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261844920457951489459965107 392767380686927234189947661)
        ·
          refine ⟨147287767757597712821230373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 392767380686927234189947661 147287767757597712821230373)
          ·
            refine ⟨27616456454549571153980695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147287767757597712821230373 27616456454549571153980695)
            ·
              refine ⟨41424684681824356730971043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27616456454549571153980695 41424684681824356730971043)
              ·
                refine ⟨62137027022736535096456565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41424684681824356730971043 62137027022736535096456565)
                ·
                  refine ⟨5825346283381550165292803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62137027022736535096456565 5825346283381550165292803)
                  ·
                    refine ⟨8738019425072325247939205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5825346283381550165292803 8738019425072325247939205)
                    ·
                      refine ⟨1638378642201060983988601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8738019425072325247939205 1638378642201060983988601)
                      ·
                        rfl

theorem cell23_3190731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 5, 1, 4].length) (baseStart_3190731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190731 prefixEnd_3190731 := by exact prefixLift 3190731
  have htrace : WordTrace (prefixWord ++ tailWord_3190731) baseStart_3190731 baseEnd_3190731 := by
    simpa [prefixWord, tailWord_3190731, baseEnd_3190731] using wordTrace_append hprefix tailTrace_3190731
  have hstable : (prefixWord ++ tailWord_3190731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190731).length < 2 ^ (prefixWord ++ tailWord_3190731).sum := by decide
  have hdescent : baseEnd_3190731 < baseStart_3190731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190759 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_3190759 : Nat := 118140960795 + 3190759 * 2 ^ 59
def prefixEnd_3190759 : Nat := 4983230072969 + 3 ^ 40 * 3190759 * 2
def baseEnd_3190759 : Nat := 1638393019659386874438473

theorem tailTrace_3190759 : CollatzResearch.WordTrace tailWord_3190759 prefixEnd_3190759 1638393019659386874438473 := by
  unfold tailWord_3190759
  simp only [CollatzResearch.WordTrace]
  refine ⟨116376541447432556097559331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77584360964955037398372887 116376541447432556097559331)
  ·
    refine ⟨174564812171148834146338997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116376541447432556097559331 174564812171148834146338997)
    ·
      refine ⟨16365451141045203201219281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174564812171148834146338997 16365451141045203201219281)
      ·
        refine ⟨12274088355783902400914461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16365451141045203201219281 12274088355783902400914461)
        ·
          refine ⟨4602783133418963400342923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12274088355783902400914461 4602783133418963400342923)
          ·
            refine ⟨6904174700128445100514385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4602783133418963400342923 6904174700128445100514385)
            ·
              refine ⟨5178131025096333825385789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6904174700128445100514385 5178131025096333825385789)
              ·
                refine ⟨1941799134411125184519671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5178131025096333825385789 1941799134411125184519671)
                ·
                  refine ⟨2912698701616687776779507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941799134411125184519671 2912698701616687776779507)
                  ·
                    refine ⟨4369048052425031665169261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2912698701616687776779507 4369048052425031665169261)
                    ·
                      refine ⟨1638393019659386874438473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369048052425031665169261 1638393019659386874438473)
                      ·
                        rfl

theorem cell23_3190759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_3190759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190759 prefixEnd_3190759 := by exact prefixLift 3190759
  have htrace : WordTrace (prefixWord ++ tailWord_3190759) baseStart_3190759 baseEnd_3190759 := by
    simpa [prefixWord, tailWord_3190759, baseEnd_3190759] using wordTrace_append hprefix tailTrace_3190759
  have hstable : (prefixWord ++ tailWord_3190759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190759).length < 2 ^ (prefixWord ++ tailWord_3190759).sum := by decide
  have hdescent : baseEnd_3190759 < baseStart_3190759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190805 : List Nat := [1, 3, 2, 1, 5, 2, 2, 7]
def baseStart_3190805 : Nat := 118140960795 + 3190805 * 2 ^ 59
def prefixEnd_3190805 : Nat := 4983230072969 + 3 ^ 40 * 3190805 * 2
def baseEnd_3190805 : Nat := 60682097769240507202343

theorem tailTrace_3190805 : CollatzResearch.WordTrace tailWord_3190805 prefixEnd_3190805 60682097769240507202343 := by
  unfold tailWord_3190805
  simp only [CollatzResearch.WordTrace]
  refine ⟨116378219205265905953733869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77585479470177270635822579 116378219205265905953733869)
  ·
    refine ⟨43641832201974714732650201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116378219205265905953733869 43641832201974714732650201)
    ·
      refine ⟨32731374151481036049487651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43641832201974714732650201 32731374151481036049487651)
      ·
        refine ⟨49097061227221554074231477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32731374151481036049487651 49097061227221554074231477)
        ·
          refine ⟨4602849490052020694459201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49097061227221554074231477 4602849490052020694459201)
          ·
            refine ⟨3452137117539015520844401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4602849490052020694459201 3452137117539015520844401)
            ·
              refine ⟨2589102838154261640633301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452137117539015520844401 2589102838154261640633301)
              ·
                refine ⟨60682097769240507202343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2589102838154261640633301 60682097769240507202343)
                ·
                  rfl

theorem cell23_3190805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 7].length) (baseStart_3190805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190805 prefixEnd_3190805 := by exact prefixLift 3190805
  have htrace : WordTrace (prefixWord ++ tailWord_3190805) baseStart_3190805 baseEnd_3190805 := by
    simpa [prefixWord, tailWord_3190805, baseEnd_3190805] using wordTrace_append hprefix tailTrace_3190805
  have hstable : (prefixWord ++ tailWord_3190805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190805).length < 2 ^ (prefixWord ++ tailWord_3190805).sum := by decide
  have hdescent : baseEnd_3190805 < baseStart_3190805 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190831 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 2, 6]
def baseStart_3190831 : Nat := 118140960795 + 3190831 * 2 ^ 59
def prefixEnd_3190831 : Nat := 4983230072969 + 3 ^ 40 * 3190831 * 2
def baseEnd_3190831 : Nat := 546143330088836864246047

theorem tailTrace_3190831 : CollatzResearch.WordTrace tailWord_3190831 prefixEnd_3190831 546143330088836864246047 := by
  unfold tailWord_3190831
  simp only [CollatzResearch.WordTrace]
  refine ⟨116379167503171712394180347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77586111668781141596120231 116379167503171712394180347)
  ·
    refine ⟨174568751254757568591270521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116379167503171712394180347 174568751254757568591270521)
    ·
      refine ⟨130926563441068176443452891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174568751254757568591270521 130926563441068176443452891)
      ·
        refine ⟨196389845161602264665179337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130926563441068176443452891 196389845161602264665179337)
        ·
          refine ⟨147292383871201698498884503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196389845161602264665179337 147292383871201698498884503)
          ·
            refine ⟨220938575806802547748326755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147292383871201698498884503 220938575806802547748326755)
            ·
              refine ⟨331407863710203821622490133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 220938575806802547748326755 331407863710203821622490133)
              ·
                refine ⟨15534743611415804138554225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 331407863710203821622490133 15534743611415804138554225)
                ·
                  refine ⟨11651057708561853103915669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15534743611415804138554225 11651057708561853103915669)
                  ·
                    refine ⟨546143330088836864246047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11651057708561853103915669 546143330088836864246047)
                    ·
                      rfl

theorem cell23_3190831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 2, 6].length) (baseStart_3190831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190831 prefixEnd_3190831 := by exact prefixLift 3190831
  have htrace : WordTrace (prefixWord ++ tailWord_3190831) baseStart_3190831 baseEnd_3190831 := by
    simpa [prefixWord, tailWord_3190831, baseEnd_3190831] using wordTrace_append hprefix tailTrace_3190831
  have hstable : (prefixWord ++ tailWord_3190831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190831).length < 2 ^ (prefixWord ++ tailWord_3190831).sum := by decide
  have hdescent : baseEnd_3190831 < baseStart_3190831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190849 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 2, 1, 3]
def baseStart_3190849 : Nat := 118140960795 + 3190849 * 2 ^ 59
def prefixEnd_3190849 : Nat := 4983230072969 + 3 ^ 40 * 3190849 * 2
def baseEnd_3190849 : Nat := 1638439232918291522313059

theorem tailTrace_3190849 : CollatzResearch.WordTrace tailWord_3190849 prefixEnd_3190849 1638439232918291522313059 := by
  unfold tailWord_3190849
  simp only [CollatzResearch.WordTrace]
  refine ⟨116379824017106501468335601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77586549344737667645557067 116379824017106501468335601)
  ·
    refine ⟨87284868012829876101251701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116379824017106501468335601 87284868012829876101251701)
    ·
      refine ⟨8182956376202800884492347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87284868012829876101251701 8182956376202800884492347)
      ·
        refine ⟨12274434564304201326738521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8182956376202800884492347 12274434564304201326738521)
        ·
          refine ⟨9205825923228150995053891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12274434564304201326738521 9205825923228150995053891)
          ·
            refine ⟨13808738884842226492580837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9205825923228150995053891 13808738884842226492580837)
            ·
              refine ⟨2589138540907917467358907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13808738884842226492580837 2589138540907917467358907)
              ·
                refine ⟨3883707811361876201038361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589138540907917467358907 3883707811361876201038361)
                ·
                  refine ⟨2912780858521407150778771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3883707811361876201038361 2912780858521407150778771)
                  ·
                    refine ⟨4369171287782110726168157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2912780858521407150778771 4369171287782110726168157)
                    ·
                      refine ⟨1638439232918291522313059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369171287782110726168157 1638439232918291522313059)
                      ·
                        rfl

theorem cell23_3190849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_3190849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190849 prefixEnd_3190849 := by exact prefixLift 3190849
  have htrace : WordTrace (prefixWord ++ tailWord_3190849) baseStart_3190849 baseEnd_3190849 := by
    simpa [prefixWord, tailWord_3190849, baseEnd_3190849] using wordTrace_append hprefix tailTrace_3190849
  have hstable : (prefixWord ++ tailWord_3190849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190849).length < 2 ^ (prefixWord ++ tailWord_3190849).sum := by decide
  have hdescent : baseEnd_3190849 < baseStart_3190849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190855 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 1, 4, 2]
def baseStart_3190855 : Nat := 118140960795 + 3190855 * 2 ^ 59
def prefixEnd_3190855 : Nat := 4983230072969 + 3 ^ 40 * 3190855 * 2
def baseEnd_3190855 : Nat := 1638442313802218498838031

theorem tailTrace_3190855 : CollatzResearch.WordTrace tailWord_3190855 prefixEnd_3190855 1638442313802218498838031 := by
  unfold tailWord_3190855
  simp only [CollatzResearch.WordTrace]
  refine ⟨116380042855084764493054019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77586695236723176328702679 116380042855084764493054019)
  ·
    refine ⟨174570064282627146739581029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116380042855084764493054019 174570064282627146739581029)
    ·
      refine ⟨32731887052992590013671443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174570064282627146739581029 32731887052992590013671443)
      ·
        refine ⟨49097830579488885020507165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32731887052992590013671443 49097830579488885020507165)
        ·
          refine ⟨18411686467308331882690187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49097830579488885020507165 18411686467308331882690187)
          ·
            refine ⟨27617529700962497824035281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18411686467308331882690187 27617529700962497824035281)
            ·
              refine ⟨20713147275721873368026461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27617529700962497824035281 20713147275721873368026461)
              ·
                refine ⟨7767430228395702513009923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20713147275721873368026461 7767430228395702513009923)
                ·
                  refine ⟨11651145342593553769514885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7767430228395702513009923 11651145342593553769514885)
                  ·
                    refine ⟨2184589751736291331784041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11651145342593553769514885 2184589751736291331784041)
                    ·
                      refine ⟨1638442313802218498838031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184589751736291331784041 1638442313802218498838031)
                      ·
                        rfl

theorem cell23_3190855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 4, 2].length) (baseStart_3190855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190855 prefixEnd_3190855 := by exact prefixLift 3190855
  have htrace : WordTrace (prefixWord ++ tailWord_3190855) baseStart_3190855 baseEnd_3190855 := by
    simpa [prefixWord, tailWord_3190855, baseEnd_3190855] using wordTrace_append hprefix tailTrace_3190855
  have hstable : (prefixWord ++ tailWord_3190855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190855).length < 2 ^ (prefixWord ++ tailWord_3190855).sum := by decide
  have hdescent : baseEnd_3190855 < baseStart_3190855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190868 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_3190868 : Nat := 118140960795 + 3190868 * 2 ^ 59
def prefixEnd_3190868 : Nat := 4983230072969 + 3 ^ 40 * 3190868 * 2
def baseEnd_3190868 : Nat := 1638448989050726947975471

theorem tailTrace_3190868 : CollatzResearch.WordTrace tailWord_3190868 prefixEnd_3190868 1638448989050726947975471 := by
  unfold tailWord_3190868
  simp only [CollatzResearch.WordTrace]
  refine ⟨58190258502018833856638629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77587011336025111808851505 58190258502018833856638629)
  ·
    refine ⟨10910673469128531348119743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58190258502018833856638629 10910673469128531348119743)
    ·
      refine ⟨16366010203692797022179615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10910673469128531348119743 16366010203692797022179615)
      ·
        refine ⟨24549015305539195533269423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16366010203692797022179615 24549015305539195533269423)
        ·
          refine ⟨36823522958308793299904135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24549015305539195533269423 36823522958308793299904135)
          ·
            refine ⟨55235284437463189949856203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36823522958308793299904135 55235284437463189949856203)
            ·
              refine ⟨82852926656194784924784305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55235284437463189949856203 82852926656194784924784305)
              ·
                refine ⟨62139694992146088693588229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82852926656194784924784305 62139694992146088693588229)
                ·
                  refine ⟨11651192811027391630047793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62139694992146088693588229 11651192811027391630047793)
                  ·
                    refine ⟨8738394608270543722535845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11651192811027391630047793 8738394608270543722535845)
                    ·
                      refine ⟨1638448989050726947975471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8738394608270543722535845 1638448989050726947975471)
                      ·
                        rfl

theorem cell23_3190868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_3190868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190868 prefixEnd_3190868 := by exact prefixLift 3190868
  have htrace : WordTrace (prefixWord ++ tailWord_3190868) baseStart_3190868 baseEnd_3190868 := by
    simpa [prefixWord, tailWord_3190868, baseEnd_3190868] using wordTrace_append hprefix tailTrace_3190868
  have hstable : (prefixWord ++ tailWord_3190868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190868).length < 2 ^ (prefixWord ++ tailWord_3190868).sum := by decide
  have hdescent : baseEnd_3190868 < baseStart_3190868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190895 : List Nat := [1, 1, 2, 1, 3, 5, 1, 4, 5]
def baseStart_3190895 : Nat := 118140960795 + 3190895 * 2 ^ 59
def prefixEnd_3190895 : Nat := 4983230072969 + 3 ^ 40 * 3190895 * 2
def baseEnd_3190895 : Nat := 182051428114266482481983

theorem tailTrace_3190895 : CollatzResearch.WordTrace tailWord_3190895 prefixEnd_3190895 182051428114266482481983 := by
  unfold tailWord_3190895
  simp only [CollatzResearch.WordTrace]
  refine ⟨116381501774939851324510139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77587667849959900883006759 116381501774939851324510139)
  ·
    refine ⟨174572252662409776986765209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116381501774939851324510139 174572252662409776986765209)
    ·
      refine ⟨130929189496807332740073907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174572252662409776986765209 130929189496807332740073907)
      ·
        refine ⟨196393784245210999110110861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130929189496807332740073907 196393784245210999110110861)
        ·
          refine ⟨73647669091954124666291573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196393784245210999110110861 73647669091954124666291573)
          ·
            refine ⟨6904468977370699187464835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73647669091954124666291573 6904468977370699187464835)
            ·
              refine ⟨10356703466056048781197253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904468977370699187464835 10356703466056048781197253)
              ·
                refine ⟨1941881899885509146474485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10356703466056048781197253 1941881899885509146474485)
                ·
                  refine ⟨182051428114266482481983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1941881899885509146474485 182051428114266482481983)
                  ·
                    rfl

theorem cell23_3190895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 4, 5].length) (baseStart_3190895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190895 prefixEnd_3190895 := by exact prefixLift 3190895
  have htrace : WordTrace (prefixWord ++ tailWord_3190895) baseStart_3190895 baseEnd_3190895 := by
    simpa [prefixWord, tailWord_3190895, baseEnd_3190895] using wordTrace_append hprefix tailTrace_3190895
  have hstable : (prefixWord ++ tailWord_3190895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190895).length < 2 ^ (prefixWord ++ tailWord_3190895).sum := by decide
  have hdescent : baseEnd_3190895 < baseStart_3190895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190905 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 3]
def baseStart_3190905 : Nat := 118140960795 + 3190905 * 2 ^ 59
def prefixEnd_3190905 : Nat := 4983230072969 + 3 ^ 40 * 3190905 * 2
def baseEnd_3190905 : Nat := 1638467987834943303212801

theorem tailTrace_3190905 : CollatzResearch.WordTrace tailWord_3190905 prefixEnd_3190905 1638467987834943303212801 := by
  unfold tailWord_3190905
  simp only [CollatzResearch.WordTrace]
  refine ⟨116381866504903623032374169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77587911003269082021582779 116381866504903623032374169)
  ·
    refine ⟨87286399878677717274280627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116381866504903623032374169 87286399878677717274280627)
    ·
      refine ⟨130929599818016575911420941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87286399878677717274280627 130929599818016575911420941)
      ·
        refine ⟨49098599931756215966782853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130929599818016575911420941 49098599931756215966782853)
        ·
          refine ⟨9205987487204290493771785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49098599931756215966782853 9205987487204290493771785)
          ·
            refine ⟨6904490615403217870328839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9205987487204290493771785 6904490615403217870328839)
            ·
              refine ⟨10356735923104826805493259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6904490615403217870328839 10356735923104826805493259)
              ·
                refine ⟨15535103884657240208239889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10356735923104826805493259 15535103884657240208239889)
                ·
                  refine ⟨11651327913492930156179917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15535103884657240208239889 11651327913492930156179917)
                  ·
                    refine ⟨4369247967559848808567469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11651327913492930156179917 4369247967559848808567469)
                    ·
                      refine ⟨1638467987834943303212801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369247967559848808567469 1638467987834943303212801)
                      ·
                        rfl

theorem cell23_3190905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 2, 3, 3].length) (baseStart_3190905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190905 prefixEnd_3190905 := by exact prefixLift 3190905
  have htrace : WordTrace (prefixWord ++ tailWord_3190905) baseStart_3190905 baseEnd_3190905 := by
    simpa [prefixWord, tailWord_3190905, baseEnd_3190905] using wordTrace_append hprefix tailTrace_3190905
  have hstable : (prefixWord ++ tailWord_3190905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190905).length < 2 ^ (prefixWord ++ tailWord_3190905).sum := by decide
  have hdescent : baseEnd_3190905 < baseStart_3190905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3190928 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4]
def baseStart_3190928 : Nat := 118140960795 + 3190928 * 2 ^ 59
def prefixEnd_3190928 : Nat := 4983230072969 + 3 ^ 40 * 3190928 * 2
def baseEnd_3190928 : Nat := 1638479797889996713225195

theorem tailTrace_3190928 : CollatzResearch.WordTrace tailWord_3190928 prefixEnd_3190928 1638479797889996713225195 := by
  unfold tailWord_3190928
  simp only [CollatzResearch.WordTrace]
  refine ⟨58191352691910148980230719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77588470255880198640307625 58191352691910148980230719)
  ·
    refine ⟨87287029037865223470346079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58191352691910148980230719 87287029037865223470346079)
    ·
      refine ⟨130930543556797835205519119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87287029037865223470346079 130930543556797835205519119)
      ·
        refine ⟨196395815335196752808278679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130930543556797835205519119 196395815335196752808278679)
        ·
          refine ⟨294593723002795129212418019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196395815335196752808278679 294593723002795129212418019)
          ·
            refine ⟨441890584504192693818627029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294593723002795129212418019 441890584504192693818627029)
            ·
              refine ⟨10356810574317016261374071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 441890584504192693818627029 10356810574317016261374071)
              ·
                refine ⟨15535215861475524392061107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10356810574317016261374071 15535215861475524392061107)
                ·
                  refine ⟨23302823792213286588091661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15535215861475524392061107 23302823792213286588091661)
                  ·
                    refine ⟨8738558922079982470534373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23302823792213286588091661 8738558922079982470534373)
                    ·
                      refine ⟨1638479797889996713225195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8738558922079982470534373 1638479797889996713225195)
                      ·
                        rfl

theorem cell23_3190928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_3190928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3190928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3190928 prefixEnd_3190928 := by exact prefixLift 3190928
  have htrace : WordTrace (prefixWord ++ tailWord_3190928) baseStart_3190928 baseEnd_3190928 := by
    simpa [prefixWord, tailWord_3190928, baseEnd_3190928] using wordTrace_append hprefix tailTrace_3190928
  have hstable : (prefixWord ++ tailWord_3190928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3190928).length < 2 ^ (prefixWord ++ tailWord_3190928).sum := by decide
  have hdescent : baseEnd_3190928 < baseStart_3190928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3190928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191022 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2]
def baseStart_3191022 : Nat := 118140960795 + 3191022 * 2 ^ 59
def prefixEnd_3191022 : Nat := 4983230072969 + 3 ^ 40 * 3191022 * 2
def baseEnd_3191022 : Nat := 1638528065071519345449763

theorem tailTrace_3191022 : CollatzResearch.WordTrace tailWord_3191022 prefixEnd_3191022 1638528065071519345449763 := by
  unfold tailWord_3191022
  simp only [CollatzResearch.WordTrace]
  refine ⟨14548266730684969001797915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77590755896986501342922213 14548266730684969001797915)
  ·
    refine ⟨21822400096027453502696873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14548266730684969001797915 21822400096027453502696873)
    ·
      refine ⟨16366800072020590127022655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21822400096027453502696873 16366800072020590127022655)
      ·
        refine ⟨24550200108030885190533983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16366800072020590127022655 24550200108030885190533983)
        ·
          refine ⟨36825300162046327785800975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24550200108030885190533983 36825300162046327785800975)
          ·
            refine ⟨55237950243069491678701463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36825300162046327785800975 55237950243069491678701463)
            ·
              refine ⟨82856925364604237518052195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55237950243069491678701463 82856925364604237518052195)
              ·
                refine ⟨124285388046906356277078293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82856925364604237518052195 124285388046906356277078293)
                ·
                  refine ⟨5825877564698735450488045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124285388046906356277078293 5825877564698735450488045)
                  ·
                    refine ⟨2184704086762025793933017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5825877564698735450488045 2184704086762025793933017)
                    ·
                      refine ⟨1638528065071519345449763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184704086762025793933017 1638528065071519345449763)
                      ·
                        rfl

theorem cell23_3191022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 6, 3, 2].length) (baseStart_3191022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191022 prefixEnd_3191022 := by exact prefixLift 3191022
  have htrace : WordTrace (prefixWord ++ tailWord_3191022) baseStart_3191022 baseEnd_3191022 := by
    simpa [prefixWord, tailWord_3191022, baseEnd_3191022] using wordTrace_append hprefix tailTrace_3191022
  have hstable : (prefixWord ++ tailWord_3191022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191022).length < 2 ^ (prefixWord ++ tailWord_3191022).sum := by decide
  have hdescent : baseEnd_3191022 < baseStart_3191022 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191045 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 4, 4]
def baseStart_3191045 : Nat := 118140960795 + 3191045 * 2 ^ 59
def prefixEnd_3191045 : Nat := 4983230072969 + 3 ^ 40 * 3191045 * 2
def baseEnd_3191045 : Nat := 546179958375524251820719

theorem tailTrace_3191045 : CollatzResearch.WordTrace tailWord_3191045 prefixEnd_3191045 546179958375524251820719 := by
  unfold tailWord_3191045
  simp only [CollatzResearch.WordTrace]
  refine ⟨116386972724396426942470589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77591315149597617961647059 116386972724396426942470589)
  ·
    refine ⟨43645114771648660103426471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116386972724396426942470589 43645114771648660103426471)
    ·
      refine ⟨65467672157472990155139707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43645114771648660103426471 65467672157472990155139707)
      ·
        refine ⟨98201508236209485232709561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65467672157472990155139707 98201508236209485232709561)
        ·
          refine ⟨73651131177157113924532171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98201508236209485232709561 73651131177157113924532171)
          ·
            refine ⟨110476696765735670886798257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73651131177157113924532171 110476696765735670886798257)
            ·
              refine ⟨82857522574301753165098693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110476696765735670886798257 82857522574301753165098693)
              ·
                refine ⟨15535785482681578718456005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82857522574301753165098693 15535785482681578718456005)
                ·
                  refine ⟨2912959778002796009710501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15535785482681578718456005 2912959778002796009710501)
                  ·
                    refine ⟨546179958375524251820719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2912959778002796009710501 546179958375524251820719)
                    ·
                      rfl

theorem cell23_3191045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_3191045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191045 prefixEnd_3191045 := by exact prefixLift 3191045
  have htrace : WordTrace (prefixWord ++ tailWord_3191045) baseStart_3191045 baseEnd_3191045 := by
    simpa [prefixWord, tailWord_3191045, baseEnd_3191045] using wordTrace_append hprefix tailTrace_3191045
  have hstable : (prefixWord ++ tailWord_3191045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191045).length < 2 ^ (prefixWord ++ tailWord_3191045).sum := by decide
  have hdescent : baseEnd_3191045 < baseStart_3191045 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191063 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 1, 1, 3]
def baseStart_3191063 : Nat := 118140960795 + 3191063 * 2 ^ 59
def prefixEnd_3191063 : Nat := 4983230072969 + 3 ^ 40 * 3191063 * 2
def baseEnd_3191063 : Nat := 1638549117778353685037075

theorem tailTrace_3191063 : CollatzResearch.WordTrace tailWord_3191063 prefixEnd_3191063 1638549117778353685037075 := by
  unfold tailWord_3191063
  simp only [CollatzResearch.WordTrace]
  refine ⟨116387629238331216016625843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77591752825554144011083895 116387629238331216016625843)
  ·
    refine ⟨174581443857496824024938765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116387629238331216016625843 174581443857496824024938765)
    ·
      refine ⟨65468041446561309009352037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174581443857496824024938765 65468041446561309009352037)
      ·
        refine ⟨12275257771230245439253507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65468041446561309009352037 12275257771230245439253507)
        ·
          refine ⟨18412886656845368158880261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275257771230245439253507 18412886656845368158880261)
          ·
            refine ⟨3452416248158506529790049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18412886656845368158880261 3452416248158506529790049)
            ·
              refine ⟨2589312186118879897342537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3452416248158506529790049 2589312186118879897342537)
              ·
                refine ⟨1941984139589159923006903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2589312186118879897342537 1941984139589159923006903)
                ·
                  refine ⟨2912976209383739884510355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1941984139589159923006903 2912976209383739884510355)
                  ·
                    refine ⟨4369464314075609826765533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2912976209383739884510355 4369464314075609826765533)
                    ·
                      refine ⟨1638549117778353685037075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369464314075609826765533 1638549117778353685037075)
                      ·
                        rfl

theorem cell23_3191063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_3191063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191063 prefixEnd_3191063 := by exact prefixLift 3191063
  have htrace : WordTrace (prefixWord ++ tailWord_3191063) baseStart_3191063 baseEnd_3191063 := by
    simpa [prefixWord, tailWord_3191063, baseEnd_3191063] using wordTrace_append hprefix tailTrace_3191063
  have hstable : (prefixWord ++ tailWord_3191063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191063).length < 2 ^ (prefixWord ++ tailWord_3191063).sum := by decide
  have hdescent : baseEnd_3191063 < baseStart_3191063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191072 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3]
def baseStart_3191072 : Nat := 118140960795 + 3191072 * 2 ^ 59
def prefixEnd_3191072 : Nat := 4983230072969 + 3 ^ 40 * 3191072 * 2
def baseEnd_3191072 : Nat := 1638553739104244149824533

theorem tailTrace_3191072 : CollatzResearch.WordTrace tailWord_3191072 prefixEnd_3191072 1638553739104244149824533 := by
  unfold tailWord_3191072
  simp only [CollatzResearch.WordTrace]
  refine ⟨58193978747649305276851735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77591971663532407035802313 58193978747649305276851735)
  ·
    refine ⟨87290968121473957915277603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58193978747649305276851735 87290968121473957915277603)
    ·
      refine ⟨130936452182210936872916405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87290968121473957915277603 130936452182210936872916405)
      ·
        refine ⟨12275292392082275331835913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 130936452182210936872916405 12275292392082275331835913)
        ·
          refine ⟨9206469294061706498876935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12275292392082275331835913 9206469294061706498876935)
          ·
            refine ⟨13809703941092559748315403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9206469294061706498876935 13809703941092559748315403)
            ·
              refine ⟨20714555911638839622473105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13809703941092559748315403 20714555911638839622473105)
              ·
                refine ⟨15535916933729129716854829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20714555911638839622473105 15535916933729129716854829)
                ·
                  refine ⟨5825968850148423643820561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15535916933729129716854829 5825968850148423643820561)
                  ·
                    refine ⟨4369476637611317732865421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5825968850148423643820561 4369476637611317732865421)
                    ·
                      refine ⟨1638553739104244149824533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369476637611317732865421 1638553739104244149824533)
                      ·
                        rfl

theorem cell23_3191072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 3].length) (baseStart_3191072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191072 prefixEnd_3191072 := by exact prefixLift 3191072
  have htrace : WordTrace (prefixWord ++ tailWord_3191072) baseStart_3191072 baseEnd_3191072 := by
    simpa [prefixWord, tailWord_3191072, baseEnd_3191072] using wordTrace_append hprefix tailTrace_3191072
  have hstable : (prefixWord ++ tailWord_3191072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191072).length < 2 ^ (prefixWord ++ tailWord_3191072).sum := by decide
  have hdescent : baseEnd_3191072 < baseStart_3191072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191135 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 2, 6]
def baseStart_3191135 : Nat := 118140960795 + 3191135 * 2 ^ 59
def prefixEnd_3191135 : Nat := 4983230072969 + 3 ^ 40 * 3191135 * 2
def baseEnd_3191135 : Nat := 546195362795159134445581

theorem tailTrace_3191135 : CollatzResearch.WordTrace tailWord_3191135 prefixEnd_3191135 546195362795159134445581 := by
  unfold tailWord_3191135
  simp only [CollatzResearch.WordTrace]
  refine ⟨116390255294070372313246859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77593503529380248208831239 116390255294070372313246859)
  ·
    refine ⟨174585382941105558469870289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116390255294070372313246859 174585382941105558469870289)
    ·
      refine ⟨130939037205829168852402717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174585382941105558469870289 130939037205829168852402717)
      ·
        refine ⟨49102138952185938319651019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130939037205829168852402717 49102138952185938319651019)
        ·
          refine ⟨73653208428278907479476529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49102138952185938319651019 73653208428278907479476529)
          ·
            refine ⟨55239906321209180609607397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73653208428278907479476529 55239906321209180609607397)
            ·
              refine ⟨10357482435226721364301387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55239906321209180609607397 10357482435226721364301387)
              ·
                refine ⟨15536223652840082046452081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10357482435226721364301387 15536223652840082046452081)
                ·
                  refine ⟨11652167739630061534839061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15536223652840082046452081 11652167739630061534839061)
                  ·
                    refine ⟨546195362795159134445581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11652167739630061534839061 546195362795159134445581)
                    ·
                      rfl

theorem cell23_3191135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 2, 6].length) (baseStart_3191135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191135 prefixEnd_3191135 := by exact prefixLift 3191135
  have htrace : WordTrace (prefixWord ++ tailWord_3191135) baseStart_3191135 baseEnd_3191135 := by
    simpa [prefixWord, tailWord_3191135, baseEnd_3191135] using wordTrace_append hprefix tailTrace_3191135
  have hstable : (prefixWord ++ tailWord_3191135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191135).length < 2 ^ (prefixWord ++ tailWord_3191135).sum := by decide
  have hdescent : baseEnd_3191135 < baseStart_3191135 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191136 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 1, 3, 3]
def baseStart_3191136 : Nat := 118140960795 + 3191136 * 2 ^ 59
def prefixEnd_3191136 : Nat := 4983230072969 + 3 ^ 40 * 3191136 * 2
def baseEnd_3191136 : Nat := 1638586601866131899424239

theorem tailTrace_3191136 : CollatzResearch.WordTrace tailWord_3191136 prefixEnd_3191136 1638586601866131899424239 := by
  unfold tailWord_3191136
  simp only [CollatzResearch.WordTrace]
  refine ⟨58195145883533374742016631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77593527844711166322688841 58195145883533374742016631)
  ·
    refine ⟨87292718825300062113024947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58195145883533374742016631 87292718825300062113024947)
    ·
      refine ⟨130939078237950093169537421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87292718825300062113024947 130939078237950093169537421)
      ·
        refine ⟨49102154339231284938576533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130939078237950093169537421 49102154339231284938576533)
        ·
          refine ⟨2301663484651466481495775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49102154339231284938576533 2301663484651466481495775)
          ·
            refine ⟨3452495226977199722243663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301663484651466481495775 3452495226977199722243663)
            ·
              refine ⟨5178742840465799583365495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452495226977199722243663 5178742840465799583365495)
              ·
                refine ⟨7768114260698699375048243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5178742840465799583365495 7768114260698699375048243)
                ·
                  refine ⟨11652171391048049062572365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7768114260698699375048243 11652171391048049062572365)
                  ·
                    refine ⟨4369564271643018398464637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11652171391048049062572365 4369564271643018398464637)
                    ·
                      refine ⟨1638586601866131899424239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369564271643018398464637 1638586601866131899424239)
                      ·
                        rfl

theorem cell23_3191136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 1, 3, 3].length) (baseStart_3191136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191136 prefixEnd_3191136 := by exact prefixLift 3191136
  have htrace : WordTrace (prefixWord ++ tailWord_3191136) baseStart_3191136 baseEnd_3191136 := by
    simpa [prefixWord, tailWord_3191136, baseEnd_3191136] using wordTrace_append hprefix tailTrace_3191136
  have hstable : (prefixWord ++ tailWord_3191136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191136).length < 2 ^ (prefixWord ++ tailWord_3191136).sum := by decide
  have hdescent : baseEnd_3191136 < baseStart_3191136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191145 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 5]
def baseStart_3191145 : Nat := 118140960795 + 3191145 * 2 ^ 59
def prefixEnd_3191145 : Nat := 4983230072969 + 3 ^ 40 * 3191145 * 2
def baseEnd_3191145 : Nat := 1638591223192022364211697

theorem tailTrace_3191145 : CollatzResearch.WordTrace tailWord_3191145 prefixEnd_3191145 1638591223192022364211697 := by
  unfold tailWord_3191145
  simp only [CollatzResearch.WordTrace]
  refine ⟨116390620024034144021110889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77593746682689429347407259 116390620024034144021110889)
  ·
    refine ⟨87292965018025608015833167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116390620024034144021110889 87292965018025608015833167)
    ·
      refine ⟨130939447527038412023749751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87292965018025608015833167 130939447527038412023749751)
      ·
        refine ⟨196409171290557618035624627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130939447527038412023749751 196409171290557618035624627)
        ·
          refine ⟨294613756935836427053436941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196409171290557618035624627 294613756935836427053436941)
          ·
            refine ⟨110480158850938660145038853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 294613756935836427053436941 110480158850938660145038853)
            ·
              refine ⟨20715029784550998777194785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110480158850938660145038853 20715029784550998777194785)
              ·
                refine ⟨15536272338413249082896089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20715029784550998777194785 15536272338413249082896089)
                ·
                  refine ⟨11652204253809936812172067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15536272338413249082896089 11652204253809936812172067)
                  ·
                    refine ⟨17478306380714905218258101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11652204253809936812172067 17478306380714905218258101)
                    ·
                      refine ⟨1638591223192022364211697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17478306380714905218258101 1638591223192022364211697)
                      ·
                        rfl

theorem cell23_3191145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 1, 5].length) (baseStart_3191145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191145 prefixEnd_3191145 := by exact prefixLift 3191145
  have htrace : WordTrace (prefixWord ++ tailWord_3191145) baseStart_3191145 baseEnd_3191145 := by
    simpa [prefixWord, tailWord_3191145, baseEnd_3191145] using wordTrace_append hprefix tailTrace_3191145
  have hstable : (prefixWord ++ tailWord_3191145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191145).length < 2 ^ (prefixWord ++ tailWord_3191145).sum := by decide
  have hdescent : baseEnd_3191145 < baseStart_3191145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191146 : List Nat := [3, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2]
def baseStart_3191146 : Nat := 118140960795 + 3191146 * 2 ^ 59
def prefixEnd_3191146 : Nat := 4983230072969 + 3 ^ 40 * 3191146 * 2
def baseEnd_3191146 : Nat := 1638591736672676860299193

theorem tailTrace_3191146 : CollatzResearch.WordTrace tailWord_3191146 prefixEnd_3191146 1638591736672676860299193 := by
  unfold tailWord_3191146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29097664124257630297974323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77593770998020347461264861 29097664124257630297974323)
  ·
    refine ⟨43646496186386445446961485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29097664124257630297974323 43646496186386445446961485)
    ·
      refine ⟨16367436069894917042610557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43646496186386445446961485 16367436069894917042610557)
      ·
        refine ⟨6137788526210593890978959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16367436069894917042610557 6137788526210593890978959)
        ·
          refine ⟨9206682789315890836468439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6137788526210593890978959 9206682789315890836468439)
          ·
            refine ⟨13810024183973836254702659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9206682789315890836468439 13810024183973836254702659)
            ·
              refine ⟨20715036275960754382053989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13810024183973836254702659 20715036275960754382053989)
              ·
                refine ⟨3884069301742641446635123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20715036275960754382053989 3884069301742641446635123)
                ·
                  refine ⟨5826103952613962169952685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884069301742641446635123 5826103952613962169952685)
                  ·
                    refine ⟨2184788982230235813732257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5826103952613962169952685 2184788982230235813732257)
                    ·
                      refine ⟨1638591736672676860299193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184788982230235813732257 1638591736672676860299193)
                      ·
                        rfl

theorem cell23_3191146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_3191146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191146 prefixEnd_3191146 := by exact prefixLift 3191146
  have htrace : WordTrace (prefixWord ++ tailWord_3191146) baseStart_3191146 baseEnd_3191146 := by
    simpa [prefixWord, tailWord_3191146, baseEnd_3191146] using wordTrace_append hprefix tailTrace_3191146
  have hstable : (prefixWord ++ tailWord_3191146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191146).length < 2 ^ (prefixWord ++ tailWord_3191146).sum := by decide
  have hdescent : baseEnd_3191146 < baseStart_3191146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191175 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_3191175 : Nat := 118140960795 + 3191175 * 2 ^ 59
def prefixEnd_3191175 : Nat := 4983230072969 + 3 ^ 40 * 3191175 * 2
def baseEnd_3191175 : Nat := 1638606627611657246836559

theorem tailTrace_3191175 : CollatzResearch.WordTrace tailWord_3191175 prefixEnd_3191175 1638606627611657246836559 := by
  unfold tailWord_3191175
  simp only [CollatzResearch.WordTrace]
  refine ⟨116391714213925459144702979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77594476142616972763135319 116391714213925459144702979)
  ·
    refine ⟨174587571320888188717054469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116391714213925459144702979 174587571320888188717054469)
    ·
      refine ⟨32735169622666535384447713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174587571320888188717054469 32735169622666535384447713)
      ·
        refine ⟨24551377216999901538335785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32735169622666535384447713 24551377216999901538335785)
        ·
          refine ⟨18413532912749926153751839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24551377216999901538335785 18413532912749926153751839)
          ·
            refine ⟨27620299369124889230627759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18413532912749926153751839 27620299369124889230627759)
            ·
              refine ⟨41430449053687333845941639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27620299369124889230627759 41430449053687333845941639)
              ·
                refine ⟨62145673580531000768912459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41430449053687333845941639 62145673580531000768912459)
                ·
                  refine ⟨93218510370796501153368689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62145673580531000768912459 93218510370796501153368689)
                  ·
                    refine ⟨69913882778097375865026517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93218510370796501153368689 69913882778097375865026517)
                    ·
                      refine ⟨1638606627611657246836559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69913882778097375865026517 1638606627611657246836559)
                      ·
                        rfl

theorem cell23_3191175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_3191175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191175 prefixEnd_3191175 := by exact prefixLift 3191175
  have htrace : WordTrace (prefixWord ++ tailWord_3191175) baseStart_3191175 baseEnd_3191175 := by
    simpa [prefixWord, tailWord_3191175, baseEnd_3191175] using wordTrace_append hprefix tailTrace_3191175
  have hstable : (prefixWord ++ tailWord_3191175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191175).length < 2 ^ (prefixWord ++ tailWord_3191175).sum := by decide
  have hdescent : baseEnd_3191175 < baseStart_3191175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191176 : List Nat := [2, 1, 3, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_3191176 : Nat := 118140960795 + 3191176 * 2 ^ 59
def prefixEnd_3191176 : Nat := 4983230072969 + 3 ^ 40 * 3191176 * 2
def baseEnd_3191176 : Nat := 1638607141092311742924055

theorem tailTrace_3191176 : CollatzResearch.WordTrace tailWord_3191176 prefixEnd_3191176 1638607141092311742924055 := by
  unfold tailWord_3191176
  simp only [CollatzResearch.WordTrace]
  refine ⟨58195875343460918157744691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77594500457947890876992921 58195875343460918157744691)
  ·
    refine ⟨87293813015191377236617037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58195875343460918157744691 87293813015191377236617037)
    ·
      refine ⟨32735179880696766463731389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87293813015191377236617037 32735179880696766463731389)
      ·
        refine ⟨12275692455261287423899271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32735179880696766463731389 12275692455261287423899271)
        ·
          refine ⟨18413538682891931135848907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12275692455261287423899271 18413538682891931135848907)
          ·
            refine ⟨27620308024337896703773361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18413538682891931135848907 27620308024337896703773361)
            ·
              refine ⟨20715231018253422527830021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27620308024337896703773361 20715231018253422527830021)
              ·
                refine ⟨3884105815922516723968129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20715231018253422527830021 3884105815922516723968129)
                ·
                  refine ⟨2913079361941887542976097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3884105815922516723968129 2913079361941887542976097)
                  ·
                    refine ⟨2184809521456415657232073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2913079361941887542976097 2184809521456415657232073)
                    ·
                      refine ⟨1638607141092311742924055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184809521456415657232073 1638607141092311742924055)
                      ·
                        rfl

theorem cell23_3191176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_3191176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191176 prefixEnd_3191176 := by exact prefixLift 3191176
  have htrace : WordTrace (prefixWord ++ tailWord_3191176) baseStart_3191176 baseEnd_3191176 := by
    simpa [prefixWord, tailWord_3191176, baseEnd_3191176] using wordTrace_append hprefix tailTrace_3191176
  have hstable : (prefixWord ++ tailWord_3191176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191176).length < 2 ^ (prefixWord ++ tailWord_3191176).sum := by decide
  have hdescent : baseEnd_3191176 < baseStart_3191176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191205 : List Nat := [1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_3191205 : Nat := 118140960795 + 3191205 * 2 ^ 59
def prefixEnd_3191205 : Nat := 4983230072969 + 3 ^ 40 * 3191205 * 2
def baseEnd_3191205 : Nat := 1638622032031292129461421

theorem tailTrace_3191205 : CollatzResearch.WordTrace tailWord_3191205 prefixEnd_3191205 1638622032031292129461421 := by
  unfold tailWord_3191205
  simp only [CollatzResearch.WordTrace]
  refine ⟨116392808403816774268295069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77595205602544516178863379 116392808403816774268295069)
  ·
    refine ⟨43647303151431290350610651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116392808403816774268295069 43647303151431290350610651)
    ·
      refine ⟨65470954727146935525915977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43647303151431290350610651 65470954727146935525915977)
      ·
        refine ⟨49103216045360201644436983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65470954727146935525915977 49103216045360201644436983)
        ·
          refine ⟨73654824068040302466655475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49103216045360201644436983 73654824068040302466655475)
          ·
            refine ⟨110482236102060453699983213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73654824068040302466655475 110482236102060453699983213)
            ·
              refine ⟨41430838538272670137493705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110482236102060453699983213 41430838538272670137493705)
              ·
                refine ⟨31073128903704502603120279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41430838538272670137493705 31073128903704502603120279)
                ·
                  refine ⟨46609693355556753904680419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31073128903704502603120279 46609693355556753904680419)
                  ·
                    refine ⟨69914540033335130857020629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46609693355556753904680419 69914540033335130857020629)
                    ·
                      refine ⟨1638622032031292129461421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69914540033335130857020629 1638622032031292129461421)
                      ·
                        rfl

theorem cell23_3191205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_3191205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191205 prefixEnd_3191205 := by exact prefixLift 3191205
  have htrace : WordTrace (prefixWord ++ tailWord_3191205) baseStart_3191205 baseEnd_3191205 := by
    simpa [prefixWord, tailWord_3191205, baseEnd_3191205] using wordTrace_append hprefix tailTrace_3191205
  have hstable : (prefixWord ++ tailWord_3191205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191205).length < 2 ^ (prefixWord ++ tailWord_3191205).sum := by decide
  have hdescent : baseEnd_3191205 < baseStart_3191205 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191210 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2]
def baseStart_3191210 : Nat := 118140960795 + 3191210 * 2 ^ 59
def prefixEnd_3191210 : Nat := 4983230072969 + 3 ^ 40 * 3191210 * 2
def baseEnd_3191210 : Nat := 1638624599434564609898899

theorem tailTrace_3191210 : CollatzResearch.WordTrace tailWord_3191210 prefixEnd_3191210 1638624599434564609898899 := by
  unfold tailWord_3191210
  simp only [CollatzResearch.WordTrace]
  refine ⟨29098247692199665030556771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77595327179199106748151389 29098247692199665030556771)
  ·
    refine ⟨43647371538299497545835157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29098247692199665030556771 43647371538299497545835157)
    ·
      refine ⟨2045970540857788947461023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 43647371538299497545835157 2045970540857788947461023)
      ·
        refine ⟨3068955811286683421191535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2045970540857788947461023 3068955811286683421191535)
        ·
          refine ⟨4603433716930025131787303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3068955811286683421191535 4603433716930025131787303)
          ·
            refine ⟨6905150575395037697680955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4603433716930025131787303 6905150575395037697680955)
            ·
              refine ⟨10357725863092556546521433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6905150575395037697680955 10357725863092556546521433)
              ·
                refine ⟨7768294397319417409891075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10357725863092556546521433 7768294397319417409891075)
                ·
                  refine ⟨11652441595979126114836613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7768294397319417409891075 11652441595979126114836613)
                  ·
                    refine ⟨2184832799246086146531865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11652441595979126114836613 2184832799246086146531865)
                    ·
                      refine ⟨1638624599434564609898899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2184832799246086146531865 1638624599434564609898899)
                      ·
                        rfl

theorem cell23_3191210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_3191210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191210 prefixEnd_3191210 := by exact prefixLift 3191210
  have htrace : WordTrace (prefixWord ++ tailWord_3191210) baseStart_3191210 baseEnd_3191210 := by
    simpa [prefixWord, tailWord_3191210, baseEnd_3191210] using wordTrace_append hprefix tailTrace_3191210
  have hstable : (prefixWord ++ tailWord_3191210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191210).length < 2 ^ (prefixWord ++ tailWord_3191210).sum := by decide
  have hdescent : baseEnd_3191210 < baseStart_3191210 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191235 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5]
def baseStart_3191235 : Nat := 118140960795 + 3191235 * 2 ^ 59
def prefixEnd_3191235 : Nat := 4983230072969 + 3 ^ 40 * 3191235 * 2
def baseEnd_3191235 : Nat := 1638637436450927012086283

theorem tailTrace_3191235 : CollatzResearch.WordTrace tailWord_3191235 prefixEnd_3191235 1638637436450927012086283 := by
  unfold tailWord_3191235
  simp only [CollatzResearch.WordTrace]
  refine ⟨116393902593708089391887159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77595935062472059594591439 116393902593708089391887159)
  ·
    refine ⟨174590853890562134087830739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116393902593708089391887159 174590853890562134087830739)
    ·
      refine ⟨261886280835843201131746109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174590853890562134087830739 261886280835843201131746109)
      ·
        refine ⟨98207355313441200424404791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261886280835843201131746109 98207355313441200424404791)
        ·
          refine ⟨147311032970161800636607187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98207355313441200424404791 147311032970161800636607187)
          ·
            refine ⟨220966549455242700954910781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147311032970161800636607187 220966549455242700954910781)
            ·
              refine ⟨82862456045716012858091543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 220966549455242700954910781 82862456045716012858091543)
              ·
                refine ⟨124293684068574019287137315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 82862456045716012858091543 124293684068574019287137315)
                ·
                  refine ⟨186440526102861028930705973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124293684068574019287137315 186440526102861028930705973)
                  ·
                    refine ⟨17478799322143221462253685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 186440526102861028930705973 17478799322143221462253685)
                    ·
                      refine ⟨1638637436450927012086283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17478799322143221462253685 1638637436450927012086283)
                      ·
                        rfl

theorem cell23_3191235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_3191235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191235 prefixEnd_3191235 := by exact prefixLift 3191235
  have htrace : WordTrace (prefixWord ++ tailWord_3191235) baseStart_3191235 baseEnd_3191235 := by
    simpa [prefixWord, tailWord_3191235, baseEnd_3191235] using wordTrace_append hprefix tailTrace_3191235
  have hstable : (prefixWord ++ tailWord_3191235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191235).length < 2 ^ (prefixWord ++ tailWord_3191235).sum := by decide
  have hdescent : baseEnd_3191235 < baseStart_3191235 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191255 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 12]
def baseStart_3191255 : Nat := 118140960795 + 3191255 * 2 ^ 59
def prefixEnd_3191255 : Nat := 4983230072969 + 3 ^ 40 * 3191255 * 2
def baseEnd_3191255 : Nat := 182071967340446325981799

theorem tailTrace_3191255 : CollatzResearch.WordTrace tailWord_3191255 prefixEnd_3191255 182071967340446325981799 := by
  unfold tailWord_3191255
  simp only [CollatzResearch.WordTrace]
  refine ⟨116394632053635632807615219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77596421369090421871743479 116394632053635632807615219)
  ·
    refine ⟨174591948080453449211422829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116394632053635632807615219 174591948080453449211422829)
    ·
      refine ⟨65471980530170043454283561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174591948080453449211422829 65471980530170043454283561)
      ·
        refine ⟨49103985397627532590712671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65471980530170043454283561 49103985397627532590712671)
        ·
          refine ⟨73655978096441298886069007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49103985397627532590712671 73655978096441298886069007)
          ·
            refine ⟨110483967144661948329103511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73655978096441298886069007 110483967144661948329103511)
            ·
              refine ⟨165725950716992922493655267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110483967144661948329103511 165725950716992922493655267)
              ·
                refine ⟨248588926075489383740482901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 165725950716992922493655267 248588926075489383740482901)
                ·
                  refine ⟨182071967340446325981799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 248588926075489383740482901 182071967340446325981799)
                  ·
                    rfl

theorem cell23_3191255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 12].length) (baseStart_3191255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191255 prefixEnd_3191255 := by exact prefixLift 3191255
  have htrace : WordTrace (prefixWord ++ tailWord_3191255) baseStart_3191255 baseEnd_3191255 := by
    simpa [prefixWord, tailWord_3191255, baseEnd_3191255] using wordTrace_append hprefix tailTrace_3191255
  have hstable : (prefixWord ++ tailWord_3191255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191255).length < 2 ^ (prefixWord ++ tailWord_3191255).sum := by decide
  have hdescent : baseEnd_3191255 < baseStart_3191255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191276 : List Nat := [2, 2, 1, 1, 2, 1, 6, 3, 1, 4]
def baseStart_3191276 : Nat := 118140960795 + 3191276 * 2 ^ 59
def prefixEnd_3191276 : Nat := 4983230072969 + 3 ^ 40 * 3191276 * 2
def baseEnd_3191276 : Nat := 546219496385920450557865

theorem tailTrace_3191276 : CollatzResearch.WordTrace tailWord_3191276 prefixEnd_3191276 546219496385920450557865 := by
  unfold tailWord_3191276
  simp only [CollatzResearch.WordTrace]
  refine ⟨58197698993279776697064841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77596931991039702262753121 58197698993279776697064841)
  ·
    refine ⟨43648274244959832522798631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58197698993279776697064841 43648274244959832522798631)
    ·
      refine ⟨65472411367439748784197947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43648274244959832522798631 65472411367439748784197947)
      ·
        refine ⟨98208617051159623176296921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65472411367439748784197947 98208617051159623176296921)
        ·
          refine ⟨73656462788369717382222691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98208617051159623176296921 73656462788369717382222691)
          ·
            refine ⟨110484694182554576073334037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73656462788369717382222691 110484694182554576073334037)
            ·
              refine ⟨5178970039807245753437533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110484694182554576073334037 5178970039807245753437533)
              ·
                refine ⟨1942113764927717157539075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5178970039807245753437533 1942113764927717157539075)
                ·
                  refine ⟨2913170647391575736308613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942113764927717157539075 2913170647391575736308613)
                  ·
                    refine ⟨546219496385920450557865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913170647391575736308613 546219496385920450557865)
                    ·
                      rfl

theorem cell23_3191276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_3191276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191276 prefixEnd_3191276 := by exact prefixLift 3191276
  have htrace : WordTrace (prefixWord ++ tailWord_3191276) baseStart_3191276 baseEnd_3191276 := by
    simpa [prefixWord, tailWord_3191276, baseEnd_3191276] using wordTrace_append hprefix tailTrace_3191276
  have hstable : (prefixWord ++ tailWord_3191276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191276).length < 2 ^ (prefixWord ++ tailWord_3191276).sum := by decide
  have hdescent : baseEnd_3191276 < baseStart_3191276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191333 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 1, 1, 3]
def baseStart_3191333 : Nat := 118140960795 + 3191333 * 2 ^ 59
def prefixEnd_3191333 : Nat := 4983230072969 + 3 ^ 40 * 3191333 * 2
def baseEnd_3191333 : Nat := 1638687757555067628660833

theorem tailTrace_3191333 : CollatzResearch.WordTrace tailWord_3191333 prefixEnd_3191333 1638687757555067628660833 := by
  unfold tailWord_3191333
  simp only [CollatzResearch.WordTrace]
  refine ⟨116397476947353052128954653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77598317964902034752636435 116397476947353052128954653)
  ·
    refine ⟨43649053855257394548357995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116397476947353052128954653 43649053855257394548357995)
    ·
      refine ⟨65473580782886091822536993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43649053855257394548357995 65473580782886091822536993)
      ·
        refine ⟨49105185587164568866902745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65473580782886091822536993 49105185587164568866902745)
        ·
          refine ⟨36828889190373426650177059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49105185587164568866902745 36828889190373426650177059)
          ·
            refine ⟨55243333785560139975265589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36828889190373426650177059 55243333785560139975265589)
            ·
              refine ⟨5179062542396263122681149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55243333785560139975265589 5179062542396263122681149)
              ·
                refine ⟨1942148453398598671005431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5179062542396263122681149 1942148453398598671005431)
                ·
                  refine ⟨2913222680097898006508147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942148453398598671005431 2913222680097898006508147)
                  ·
                    refine ⟨4369834020146847009762221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2913222680097898006508147 4369834020146847009762221)
                    ·
                      refine ⟨1638687757555067628660833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369834020146847009762221 1638687757555067628660833)
                      ·
                        rfl

theorem cell23_3191333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_3191333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191333 prefixEnd_3191333 := by exact prefixLift 3191333
  have htrace : WordTrace (prefixWord ++ tailWord_3191333) baseStart_3191333 baseEnd_3191333 := by
    simpa [prefixWord, tailWord_3191333, baseEnd_3191333] using wordTrace_append hprefix tailTrace_3191333
  have hstable : (prefixWord ++ tailWord_3191333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191333).length < 2 ^ (prefixWord ++ tailWord_3191333).sum := by decide
  have hdescent : baseEnd_3191333 < baseStart_3191333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191336 : List Nat := [2, 1, 5, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3191336 : Nat := 118140960795 + 3191336 * 2 ^ 59
def prefixEnd_3191336 : Nat := 4983230072969 + 3 ^ 40 * 3191336 * 2
def baseEnd_3191336 : Nat := 546229765999010372307773

theorem tailTrace_3191336 : CollatzResearch.WordTrace tailWord_3191336 prefixEnd_3191336 546229765999010372307773 := by
  unfold tailWord_3191336
  simp only [CollatzResearch.WordTrace]
  refine ⟨58198793183171091820656931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77598390910894789094209241 58198793183171091820656931)
  ·
    refine ⟨87298189774756637730985397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58198793183171091820656931 87298189774756637730985397)
    ·
      refine ⟨8184205291383434787279881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87298189774756637730985397 8184205291383434787279881)
      ·
        refine ⟨6138153968537576090459911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8184205291383434787279881 6138153968537576090459911)
        ·
          refine ⟨9207230952806364135689867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138153968537576090459911 9207230952806364135689867)
          ·
            refine ⟨13810846429209546203534801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207230952806364135689867 13810846429209546203534801)
            ·
              refine ⟨10358134821907159652651101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13810846429209546203534801 10358134821907159652651101)
              ·
                refine ⟨3884300558215184869744163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10358134821907159652651101 3884300558215184869744163)
                ·
                  refine ⟨5826450837322777304616245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884300558215184869744163 5826450837322777304616245)
                  ·
                    refine ⟨546229765999010372307773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5826450837322777304616245 546229765999010372307773)
                    ·
                      rfl

theorem cell23_3191336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3191336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191336 prefixEnd_3191336 := by exact prefixLift 3191336
  have htrace : WordTrace (prefixWord ++ tailWord_3191336) baseStart_3191336 baseEnd_3191336 := by
    simpa [prefixWord, tailWord_3191336, baseEnd_3191336] using wordTrace_append hprefix tailTrace_3191336
  have hstable : (prefixWord ++ tailWord_3191336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191336).length < 2 ^ (prefixWord ++ tailWord_3191336).sum := by decide
  have hdescent : baseEnd_3191336 < baseStart_3191336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191349 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 4, 4]
def baseStart_3191349 : Nat := 118140960795 + 3191349 * 2 ^ 59
def prefixEnd_3191349 : Nat := 4983230072969 + 3 ^ 40 * 3191349 * 2
def baseEnd_3191349 : Nat := 546231991081846522020253

theorem tailTrace_3191349 : CollatzResearch.WordTrace tailWord_3191349 prefixEnd_3191349 546231991081846522020253 := by
  unfold tailWord_3191349
  simp only [CollatzResearch.WordTrace]
  refine ⟨116398060515295086861537101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77598707010196724574358067 116398060515295086861537101)
  ·
    refine ⟨43649272693235657573076413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116398060515295086861537101 43649272693235657573076413)
    ·
      refine ⟨16368477259963371589903655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43649272693235657573076413 16368477259963371589903655)
      ·
        refine ⟨24552715889945057384855483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16368477259963371589903655 24552715889945057384855483)
        ·
          refine ⟨36829073834917586077283225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24552715889945057384855483 36829073834917586077283225)
          ·
            refine ⟨27621805376188189557962419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36829073834917586077283225 27621805376188189557962419)
            ·
              refine ⟨41432708064282284336943629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27621805376188189557962419 41432708064282284336943629)
              ·
                refine ⟨15537265524105856626353861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41432708064282284336943629 15537265524105856626353861)
                ·
                  refine ⟨2913237285769848117441349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15537265524105856626353861 2913237285769848117441349)
                  ·
                    refine ⟨546231991081846522020253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913237285769848117441349 546231991081846522020253)
                    ·
                      rfl

theorem cell23_3191349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_3191349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191349 prefixEnd_3191349 := by exact prefixLift 3191349
  have htrace : WordTrace (prefixWord ++ tailWord_3191349) baseStart_3191349 baseEnd_3191349 := by
    simpa [prefixWord, tailWord_3191349, baseEnd_3191349] using wordTrace_append hprefix tailTrace_3191349
  have hstable : (prefixWord ++ tailWord_3191349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191349).length < 2 ^ (prefixWord ++ tailWord_3191349).sum := by decide
  have hdescent : baseEnd_3191349 < baseStart_3191349 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191350 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_3191350 : Nat := 118140960795 + 3191350 * 2 ^ 59
def prefixEnd_3191350 : Nat := 4983230072969 + 3 ^ 40 * 3191350 * 2
def baseEnd_3191350 : Nat := 1638696486726194062148255

theorem tailTrace_3191350 : CollatzResearch.WordTrace tailWord_3191350 prefixEnd_3191350 1638696486726194062148255 := by
  unfold tailWord_3191350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7274881061768216502020219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77598731325527642688215669 7274881061768216502020219)
  ·
    refine ⟨10912321592652324753030329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7274881061768216502020219 10912321592652324753030329)
    ·
      refine ⟨8184241194489243564772747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10912321592652324753030329 8184241194489243564772747)
      ·
        refine ⟨12276361791733865347159121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8184241194489243564772747 12276361791733865347159121)
        ·
          refine ⟨9207271343800399010369341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12276361791733865347159121 9207271343800399010369341)
          ·
            refine ⟨3452726753925149628888503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9207271343800399010369341 3452726753925149628888503)
            ·
              refine ⟨5179090130887724443332755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452726753925149628888503 5179090130887724443332755)
              ·
                refine ⟨7768635196331586664999133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5179090130887724443332755 7768635196331586664999133)
                ·
                  refine ⟨2913238198624344999374675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7768635196331586664999133 2913238198624344999374675)
                  ·
                    refine ⟨4369857297936517499062013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2913238198624344999374675 4369857297936517499062013)
                    ·
                      refine ⟨1638696486726194062148255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369857297936517499062013 1638696486726194062148255)
                      ·
                        rfl

theorem cell23_3191350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_3191350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191350 prefixEnd_3191350 := by exact prefixLift 3191350
  have htrace : WordTrace (prefixWord ++ tailWord_3191350) baseStart_3191350 baseEnd_3191350 := by
    simpa [prefixWord, tailWord_3191350, baseEnd_3191350] using wordTrace_append hprefix tailTrace_3191350
  have hstable : (prefixWord ++ tailWord_3191350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191350).length < 2 ^ (prefixWord ++ tailWord_3191350).sum := by decide
  have hdescent : baseEnd_3191350 < baseStart_3191350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191352 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 3, 1, 6]
def baseStart_3191352 : Nat := 118140960795 + 3191352 * 2 ^ 59
def prefixEnd_3191352 : Nat := 4983230072969 + 3 ^ 40 * 3191352 * 2
def baseEnd_3191352 : Nat := 1638697513687503054323245

theorem tailTrace_3191352 : CollatzResearch.WordTrace tailWord_3191352 prefixEnd_3191352 1638697513687503054323245 := by
  unfold tailWord_3191352
  simp only [CollatzResearch.WordTrace]
  refine ⟨58199084967142109186948155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77598779956189478915930873 58199084967142109186948155)
  ·
    refine ⟨87298627450713163780422233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58199084967142109186948155 87298627450713163780422233)
    ·
      refine ⟨65473970588034872835316675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87298627450713163780422233 65473970588034872835316675)
      ·
        refine ⟨98210955882052309252975013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65473970588034872835316675 98210955882052309252975013)
        ·
          refine ⟨18414554227884807984932815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98210955882052309252975013 18414554227884807984932815)
          ·
            refine ⟨27621831341827211977399223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18414554227884807984932815 27621831341827211977399223)
            ·
              refine ⟨41432747012740817966098835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27621831341827211977399223 41432747012740817966098835)
              ·
                refine ⟨62149120519111226949148253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41432747012740817966098835 62149120519111226949148253)
                ·
                  refine ⟨23305920194666710105930595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62149120519111226949148253 23305920194666710105930595)
                  ·
                    refine ⟨34958880292000065158895893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23305920194666710105930595 34958880292000065158895893)
                    ·
                      refine ⟨1638697513687503054323245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34958880292000065158895893 1638697513687503054323245)
                      ·
                        rfl

theorem cell23_3191352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_3191352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191352 prefixEnd_3191352 := by exact prefixLift 3191352
  have htrace : WordTrace (prefixWord ++ tailWord_3191352) baseStart_3191352 baseEnd_3191352 := by
    simpa [prefixWord, tailWord_3191352, baseEnd_3191352] using wordTrace_append hprefix tailTrace_3191352
  have hstable : (prefixWord ++ tailWord_3191352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191352).length < 2 ^ (prefixWord ++ tailWord_3191352).sum := by decide
  have hdescent : baseEnd_3191352 < baseStart_3191352 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191359 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 3]
def baseStart_3191359 : Nat := 118140960795 + 3191359 * 2 ^ 59
def prefixEnd_3191359 : Nat := 4983230072969 + 3 ^ 40 * 3191359 * 2
def baseEnd_3191359 : Nat := 1638701108052084526935713

theorem tailTrace_3191359 : CollatzResearch.WordTrace tailWord_3191359 prefixEnd_3191359 1638701108052084526935713 := by
  unfold tailWord_3191359
  simp only [CollatzResearch.WordTrace]
  refine ⟨116398425245258858569401131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77598950163505905712934087 116398425245258858569401131)
  ·
    refine ⟨174597637867888287854101697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116398425245258858569401131 174597637867888287854101697)
    ·
      refine ⟨130948228400916215890576273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174597637867888287854101697 130948228400916215890576273)
      ·
        refine ⟨98211171300687161917932205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130948228400916215890576273 98211171300687161917932205)
        ·
          refine ⟨36829189237757685719224577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98211171300687161917932205 36829189237757685719224577)
          ·
            refine ⟨27621891928318264289418433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36829189237757685719224577 27621891928318264289418433)
            ·
              refine ⟨20716418946238698217063825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27621891928318264289418433 20716418946238698217063825)
              ·
                refine ⟨15537314209679023662797869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20716418946238698217063825 15537314209679023662797869)
                ·
                  refine ⟨5826492828629633873549201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15537314209679023662797869 5826492828629633873549201)
                  ·
                    refine ⟨4369869621472225405161901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5826492828629633873549201 4369869621472225405161901)
                    ·
                      refine ⟨1638701108052084526935713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369869621472225405161901 1638701108052084526935713)
                      ·
                        rfl

theorem cell23_3191359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 3].length) (baseStart_3191359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191359 prefixEnd_3191359 := by exact prefixLift 3191359
  have htrace : WordTrace (prefixWord ++ tailWord_3191359) baseStart_3191359 baseEnd_3191359 := by
    simpa [prefixWord, tailWord_3191359, baseEnd_3191359] using wordTrace_append hprefix tailTrace_3191359
  have hstable : (prefixWord ++ tailWord_3191359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191359).length < 2 ^ (prefixWord ++ tailWord_3191359).sum := by decide
  have hdescent : baseEnd_3191359 < baseStart_3191359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191373 : List Nat := [1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3191373 : Nat := 118140960795 + 3191373 * 2 ^ 59
def prefixEnd_3191373 : Nat := 4983230072969 + 3 ^ 40 * 3191373 * 2
def baseEnd_3191373 : Nat := 1638708296781247472160649

theorem tailTrace_3191373 : CollatzResearch.WordTrace tailWord_3191373 prefixEnd_3191373 1638708296781247472160649 := by
  unfold tailWord_3191373
  simp only [CollatzResearch.WordTrace]
  refine ⟨116398935867208138960410773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77599290578138759306940515 116398935867208138960410773)
  ·
    refine ⟨5456200118775381513769255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116398935867208138960410773 5456200118775381513769255)
    ·
      refine ⟨8184300178163072270653883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5456200118775381513769255 8184300178163072270653883)
      ·
        refine ⟨12276450267244608405980825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8184300178163072270653883 12276450267244608405980825)
        ·
          refine ⟨9207337700433456304485619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12276450267244608405980825 9207337700433456304485619)
          ·
            refine ⟨13811006550650184456728429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9207337700433456304485619 13811006550650184456728429)
            ·
              refine ⟨5179127456493819171273161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13811006550650184456728429 5179127456493819171273161)
              ·
                refine ⟨3884345592370364378454871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5179127456493819171273161 3884345592370364378454871)
                ·
                  refine ⟨5826518388555546567682307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884345592370364378454871 5826518388555546567682307)
                  ·
                    refine ⟨8739777582833319851523461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5826518388555546567682307 8739777582833319851523461)
                    ·
                      refine ⟨1638708296781247472160649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8739777582833319851523461 1638708296781247472160649)
                      ·
                        rfl

theorem cell23_3191373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3191373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191373 prefixEnd_3191373 := by exact prefixLift 3191373
  have htrace : WordTrace (prefixWord ++ tailWord_3191373) baseStart_3191373 baseEnd_3191373 := by
    simpa [prefixWord, tailWord_3191373, baseEnd_3191373] using wordTrace_append hprefix tailTrace_3191373
  have hstable : (prefixWord ++ tailWord_3191373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191373).length < 2 ^ (prefixWord ++ tailWord_3191373).sum := by decide
  have hdescent : baseEnd_3191373 < baseStart_3191373 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191393 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 1, 2, 3]
def baseStart_3191393 : Nat := 118140960795 + 3191393 * 2 ^ 59
def prefixEnd_3191393 : Nat := 4983230072969 + 3 ^ 40 * 3191393 * 2
def baseEnd_3191393 : Nat := 1638718566394337393910557

theorem tailTrace_3191393 : CollatzResearch.WordTrace tailWord_3191393 prefixEnd_3191393 1638718566394337393910557 := by
  unfold tailWord_3191393
  simp only [CollatzResearch.WordTrace]
  refine ⟨116399665327135682376138833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77599776884757121584092555 116399665327135682376138833)
  ·
    refine ⟨87299748995351761782104125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116399665327135682376138833 87299748995351761782104125)
    ·
      refine ⟨32737405873256910668289047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87299748995351761782104125 32737405873256910668289047)
      ·
        refine ⟨49106108809885366002433571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32737405873256910668289047 49106108809885366002433571)
        ·
          refine ⟨73659163214828049003650357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49106108809885366002433571 73659163214828049003650357)
          ·
            refine ⟨6905546551390129594092221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 73659163214828049003650357 6905546551390129594092221)
            ·
              refine ⟨2589579956771298597784583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6905546551390129594092221 2589579956771298597784583)
              ·
                refine ⟨3884369935156947896676875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2589579956771298597784583 3884369935156947896676875)
                ·
                  refine ⟨5826554902735421845015313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3884369935156947896676875 5826554902735421845015313)
                  ·
                    refine ⟨4369916177051566383761485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5826554902735421845015313 4369916177051566383761485)
                    ·
                      refine ⟨1638718566394337393910557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4369916177051566383761485 1638718566394337393910557)
                      ·
                        rfl

theorem cell23_3191393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_3191393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191393 prefixEnd_3191393 := by exact prefixLift 3191393
  have htrace : WordTrace (prefixWord ++ tailWord_3191393) baseStart_3191393 baseEnd_3191393 := by
    simpa [prefixWord, tailWord_3191393, baseEnd_3191393] using wordTrace_append hprefix tailTrace_3191393
  have hstable : (prefixWord ++ tailWord_3191393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191393).length < 2 ^ (prefixWord ++ tailWord_3191393).sum := by decide
  have hdescent : baseEnd_3191393 < baseStart_3191393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191413 : List Nat := [1, 3, 4, 2, 3, 1, 1, 8]
def baseStart_3191413 : Nat := 118140960795 + 3191413 * 2 ^ 59
def prefixEnd_3191413 : Nat := 4983230072969 + 3 ^ 40 * 3191413 * 2
def baseEnd_3191413 : Nat := 60693660592867678357795

theorem tailTrace_3191413 : CollatzResearch.WordTrace tailWord_3191413 prefixEnd_3191413 60693660592867678357795 := by
  unfold tailWord_3191413
  simp only [CollatzResearch.WordTrace]
  refine ⟨116400394787063225791866893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77600263191375483861244595 116400394787063225791866893)
  ·
    refine ⟨43650148045148709671950085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116400394787063225791866893 43650148045148709671950085)
    ·
      refine ⟨8184402758465383063490641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43650148045148709671950085 8184402758465383063490641)
      ·
        refine ⟨6138302068849037297617981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8184402758465383063490641 6138302068849037297617981)
        ·
          refine ⟨2301863275818388986606743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6138302068849037297617981 2301863275818388986606743)
          ·
            refine ⟨3452794913727583479910115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301863275818388986606743 3452794913727583479910115)
            ·
              refine ⟨5179192370591375219865173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452794913727583479910115 5179192370591375219865173)
              ·
                refine ⟨60693660592867678357795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5179192370591375219865173 60693660592867678357795)
                ·
                  rfl

theorem cell23_3191413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 8].length) (baseStart_3191413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191413 prefixEnd_3191413 := by exact prefixLift 3191413
  have htrace : WordTrace (prefixWord ++ tailWord_3191413) baseStart_3191413 baseEnd_3191413 := by
    simpa [prefixWord, tailWord_3191413, baseEnd_3191413] using wordTrace_append hprefix tailTrace_3191413
  have hstable : (prefixWord ++ tailWord_3191413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191413).length < 2 ^ (prefixWord ++ tailWord_3191413).sum := by decide
  have hdescent : baseEnd_3191413 < baseStart_3191413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191457 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 2, 1, 3]
def baseStart_3191457 : Nat := 118140960795 + 3191457 * 2 ^ 59
def prefixEnd_3191457 : Nat := 4983230072969 + 3 ^ 40 * 3191457 * 2
def baseEnd_3191457 : Nat := 1638751429156225143510263

theorem tailTrace_3191457 : CollatzResearch.WordTrace tailWord_3191457 prefixEnd_3191457 1638751429156225143510263 := by
  unfold tailWord_3191457
  simp only [CollatzResearch.WordTrace]
  refine ⟨116401999598903821306468625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77601333065935880870979083 116401999598903821306468625)
  ·
    refine ⟨87301499699177865979851469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116401999598903821306468625 87301499699177865979851469)
    ·
      refine ⟨32738062387191699742444301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87301499699177865979851469 32738062387191699742444301)
      ·
        refine ⟨12276773395196887403416613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32738062387191699742444301 12276773395196887403416613)
        ·
          refine ⟨2301895011599416388140615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12276773395196887403416613 2301895011599416388140615)
          ·
            refine ⟨3452842517399124582210923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301895011599416388140615 3452842517399124582210923)
            ·
              refine ⟨5179263776098686873316385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3452842517399124582210923 5179263776098686873316385)
              ·
                refine ⟨3884447832074015154987289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5179263776098686873316385 3884447832074015154987289)
                ·
                  refine ⟨2913335874055511366240467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3884447832074015154987289 2913335874055511366240467)
                  ·
                    refine ⟨4370003811083267049360701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2913335874055511366240467 4370003811083267049360701)
                    ·
                      refine ⟨1638751429156225143510263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370003811083267049360701 1638751429156225143510263)
                      ·
                        rfl

theorem cell23_3191457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_3191457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191457 prefixEnd_3191457 := by exact prefixLift 3191457
  have htrace : WordTrace (prefixWord ++ tailWord_3191457) baseStart_3191457 baseEnd_3191457 := by
    simpa [prefixWord, tailWord_3191457, baseEnd_3191457] using wordTrace_append hprefix tailTrace_3191457
  have hstable : (prefixWord ++ tailWord_3191457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191457).length < 2 ^ (prefixWord ++ tailWord_3191457).sum := by decide
  have hdescent : baseEnd_3191457 < baseStart_3191457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191536 : List Nat := [2, 1, 1, 1, 3, 1, 4, 1, 1, 6, 2]
def baseStart_3191536 : Nat := 118140960795 + 3191536 * 2 ^ 59
def prefixEnd_3191536 : Nat := 4983230072969 + 3 ^ 40 * 3191536 * 2
def baseEnd_3191536 : Nat := 1638791994127930334422399

theorem tailTrace_3191536 : CollatzResearch.WordTrace tailWord_3191536 prefixEnd_3191536 1638791994127930334422399 := by
  unfold tailWord_3191536
  simp only [CollatzResearch.WordTrace]
  refine ⟨58202440482808808899297231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77603253977078411865729641 58202440482808808899297231)
  ·
    refine ⟨87303660724213213348945847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58202440482808808899297231 87303660724213213348945847)
    ·
      refine ⟨130955491086319820023418771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87303660724213213348945847 130955491086319820023418771)
      ·
        refine ⟨196433236629479730035128157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130955491086319820023418771 196433236629479730035128157)
        ·
          refine ⟨73662463736054898763173059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196433236629479730035128157 73662463736054898763173059)
          ·
            refine ⟨110493695604082348144759589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73662463736054898763173059 110493695604082348144759589)
            ·
              refine ⟨20717567925765440277142423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110493695604082348144759589 20717567925765440277142423)
              ·
                refine ⟨31076351888648160415713635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20717567925765440277142423 31076351888648160415713635)
                ·
                  refine ⟨46614527832972240623570453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31076351888648160415713635 46614527832972240623570453)
                  ·
                    refine ⟨2185055992170573779229865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46614527832972240623570453 2185055992170573779229865)
                    ·
                      refine ⟨1638791994127930334422399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185055992170573779229865 1638791994127930334422399)
                      ·
                        rfl

theorem cell23_3191536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 1, 1, 6, 2].length) (baseStart_3191536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191536 prefixEnd_3191536 := by exact prefixLift 3191536
  have htrace : WordTrace (prefixWord ++ tailWord_3191536) baseStart_3191536 baseEnd_3191536 := by
    simpa [prefixWord, tailWord_3191536, baseEnd_3191536] using wordTrace_append hprefix tailTrace_3191536
  have hstable : (prefixWord ++ tailWord_3191536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191536).length < 2 ^ (prefixWord ++ tailWord_3191536).sum := by decide
  have hdescent : baseEnd_3191536 < baseStart_3191536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191546 : List Nat := [3, 1, 1, 1, 1, 3, 2, 4, 3, 4]
def baseStart_3191546 : Nat := 118140960795 + 3191546 * 2 ^ 59
def prefixEnd_3191546 : Nat := 4983230072969 + 3 ^ 40 * 3191546 * 2
def baseEnd_3191546 : Nat := 546265709644825098432451

theorem tailTrace_3191546 : CollatzResearch.WordTrace tailWord_3191546 prefixEnd_3191546 546265709644825098432451 := by
  unfold tailWord_3191546
  simp only [CollatzResearch.WordTrace]
  refine ⟨29101311423895347376614623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77603497130387593004305661 29101311423895347376614623)
  ·
    refine ⟨43651967135843021064921935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29101311423895347376614623 43651967135843021064921935)
    ·
      refine ⟨65477950703764531597382903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43651967135843021064921935 65477950703764531597382903)
      ·
        refine ⟨98216926055646797396074355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65477950703764531597382903 98216926055646797396074355)
        ·
          refine ⟨147325389083470196094111533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98216926055646797396074355 147325389083470196094111533)
          ·
            refine ⟨55247020906301323535291825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147325389083470196094111533 55247020906301323535291825)
            ·
              refine ⟨41435265679725992651468869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55247020906301323535291825 41435265679725992651468869)
              ·
                refine ⟨7769112314948623622150413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41435265679725992651468869 7769112314948623622150413)
                ·
                  refine ⟨2913417118105733858306405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7769112314948623622150413 2913417118105733858306405)
                  ·
                    refine ⟨546265709644825098432451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913417118105733858306405 546265709644825098432451)
                    ·
                      rfl

theorem cell23_3191546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 4, 3, 4].length) (baseStart_3191546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191546 prefixEnd_3191546 := by exact prefixLift 3191546
  have htrace : WordTrace (prefixWord ++ tailWord_3191546) baseStart_3191546 baseEnd_3191546 := by
    simpa [prefixWord, tailWord_3191546, baseEnd_3191546] using wordTrace_append hprefix tailTrace_3191546
  have hstable : (prefixWord ++ tailWord_3191546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191546).length < 2 ^ (prefixWord ++ tailWord_3191546).sum := by decide
  have hdescent : baseEnd_3191546 < baseStart_3191546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191563 : List Nat := [1, 1, 1, 1, 5, 1, 1, 7, 1, 4]
def baseStart_3191563 : Nat := 118140960795 + 3191563 * 2 ^ 59
def prefixEnd_3191563 : Nat := 4983230072969 + 3 ^ 40 * 3191563 * 2
def baseEnd_3191563 : Nat := 546268619368533909594925

theorem tailTrace_3191563 : CollatzResearch.WordTrace tailWord_3191563 prefixEnd_3191563 546268619368533909594925 := by
  unfold tailWord_3191563
  simp only [CollatzResearch.WordTrace]
  refine ⟨116405865736519801409827343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77603910491013200939884895 116405865736519801409827343)
  ·
    refine ⟨174608798604779702114741015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116405865736519801409827343 174608798604779702114741015)
    ·
      refine ⟨261913197907169553172111523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174608798604779702114741015 261913197907169553172111523)
      ·
        refine ⟨392869796860754329758167285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261913197907169553172111523 392869796860754329758167285)
        ·
          refine ⟨36831543455695718414828183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 392869796860754329758167285 36831543455695718414828183)
          ·
            refine ⟨55247315183543577622242275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36831543455695718414828183 55247315183543577622242275)
            ·
              refine ⟨82870972775315366433363413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55247315183543577622242275 82870972775315366433363413)
              ·
                refine ⟨1942288424421453900781955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 82870972775315366433363413 1942288424421453900781955)
                ·
                  refine ⟨2913432636632180851172933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942288424421453900781955 2913432636632180851172933)
                  ·
                    refine ⟨546268619368533909594925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913432636632180851172933 546268619368533909594925)
                    ·
                      rfl

theorem cell23_3191563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 7, 1, 4].length) (baseStart_3191563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191563 prefixEnd_3191563 := by exact prefixLift 3191563
  have htrace : WordTrace (prefixWord ++ tailWord_3191563) baseStart_3191563 baseEnd_3191563 := by
    simpa [prefixWord, tailWord_3191563, baseEnd_3191563] using wordTrace_append hprefix tailTrace_3191563
  have hstable : (prefixWord ++ tailWord_3191563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191563).length < 2 ^ (prefixWord ++ tailWord_3191563).sum := by decide
  have hdescent : baseEnd_3191563 < baseStart_3191563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191580 : List Nat := [2, 2, 3, 1, 1, 4, 1, 4, 1, 4]
def baseStart_3191580 : Nat := 118140960795 + 3191580 * 2 ^ 59
def prefixEnd_3191580 : Nat := 4983230072969 + 3 ^ 40 * 3191580 * 2
def baseEnd_3191580 : Nat := 546271529092242720757399

theorem tailTrace_3191580 : CollatzResearch.WordTrace tailWord_3191580 prefixEnd_3191580 546271529092242720757399 := by
  unfold tailWord_3191580
  simp only [CollatzResearch.WordTrace]
  refine ⟨58203242888729106656598097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77604323851638808875464129 58203242888729106656598097)
  ·
    refine ⟨43652432166546829992448573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58203242888729106656598097 43652432166546829992448573)
    ·
      refine ⟨16369662062455061247168215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43652432166546829992448573 16369662062455061247168215)
      ·
        refine ⟨24554493093682591870752323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16369662062455061247168215 24554493093682591870752323)
        ·
          refine ⟨36831739640523887806128485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24554493093682591870752323 36831739640523887806128485)
          ·
            refine ⟨6905951182598228963649091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36831739640523887806128485 6905951182598228963649091)
            ·
              refine ⟨10358926773897343445473637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6905951182598228963649091 10358926773897343445473637)
              ·
                refine ⟨1942298770105751896026307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10358926773897343445473637 1942298770105751896026307)
                ·
                  refine ⟨2913448155158627844039461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1942298770105751896026307 2913448155158627844039461)
                  ·
                    refine ⟨546271529092242720757399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913448155158627844039461 546271529092242720757399)
                    ·
                      rfl

theorem cell23_3191580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_3191580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191580 prefixEnd_3191580 := by exact prefixLift 3191580
  have htrace : WordTrace (prefixWord ++ tailWord_3191580) baseStart_3191580 baseEnd_3191580 := by
    simpa [prefixWord, tailWord_3191580, baseEnd_3191580] using wordTrace_append hprefix tailTrace_3191580
  have hstable : (prefixWord ++ tailWord_3191580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191580).length < 2 ^ (prefixWord ++ tailWord_3191580).sum := by decide
  have hdescent : baseEnd_3191580 < baseStart_3191580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191597 : List Nat := [1, 5, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_3191597 : Nat := 118140960795 + 3191597 * 2 ^ 59
def prefixEnd_3191597 : Nat := 4983230072969 + 3 ^ 40 * 3191597 * 2
def baseEnd_3191597 : Nat := 546274438815951531919873

theorem tailTrace_3191597 : CollatzResearch.WordTrace tailWord_3191597 prefixEnd_3191597 546274438815951531919873 := by
  unfold tailWord_3191597
  simp only [CollatzResearch.WordTrace]
  refine ⟨116407105818396625216565045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77604737212264416811043363 116407105818396625216565045)
  ·
    refine ⟨10913166170474683614052973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116407105818396625216565045 10913166170474683614052973)
    ·
      refine ⟨4092437313928006355269865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10913166170474683614052973 4092437313928006355269865)
      ·
        refine ⟨3069327985446004766452399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4092437313928006355269865 3069327985446004766452399)
        ·
          refine ⟨4603991978169007149678599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3069327985446004766452399 4603991978169007149678599)
          ·
            refine ⟨6905987967253510724517899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4603991978169007149678599 6905987967253510724517899)
            ·
              refine ⟨10358981950880266086776849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6905987967253510724517899 10358981950880266086776849)
              ·
                refine ⟨7769236463160199565082637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10358981950880266086776849 7769236463160199565082637)
                ·
                  refine ⟨2913463673685074836905989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7769236463160199565082637 2913463673685074836905989)
                  ·
                    refine ⟨546274438815951531919873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913463673685074836905989 546274438815951531919873)
                    ·
                      rfl

theorem cell23_3191597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_3191597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191597 prefixEnd_3191597 := by exact prefixLift 3191597
  have htrace : WordTrace (prefixWord ++ tailWord_3191597) baseStart_3191597 baseEnd_3191597 := by
    simpa [prefixWord, tailWord_3191597, baseEnd_3191597] using wordTrace_append hprefix tailTrace_3191597
  have hstable : (prefixWord ++ tailWord_3191597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191597).length < 2 ^ (prefixWord ++ tailWord_3191597).sum := by decide
  have hdescent : baseEnd_3191597 < baseStart_3191597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191603 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 3]
def baseStart_3191603 : Nat := 118140960795 + 3191603 * 2 ^ 59
def prefixEnd_3191603 : Nat := 4983230072969 + 3 ^ 40 * 3191603 * 2
def baseEnd_3191603 : Nat := 1638826397331781572284591

theorem tailTrace_3191603 : CollatzResearch.WordTrace tailWord_3191603 prefixEnd_3191603 1638826397331781572284591 := by
  unfold tailWord_3191603
  simp only [CollatzResearch.WordTrace]
  refine ⟨116407324656374888241283463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77604883104249925494188975 116407324656374888241283463)
  ·
    refine ⟨174610986984562332361925195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116407324656374888241283463 174610986984562332361925195)
    ·
      refine ⟨261916480476843498542887793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174610986984562332361925195 261916480476843498542887793)
      ·
        refine ⟨196437360357632623907165845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261916480476843498542887793 196437360357632623907165845)
        ·
          refine ⟨9208001266764029245648399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 196437360357632623907165845 9208001266764029245648399)
          ·
            refine ⟨13812001900146043868472599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208001266764029245648399 13812001900146043868472599)
            ·
              refine ⟨20718002850219065802708899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13812001900146043868472599 20718002850219065802708899)
              ·
                refine ⟨31077004275328598704063349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20718002850219065802708899 31077004275328598704063349)
                ·
                  refine ⟨2913469150812056128505939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31077004275328598704063349 2913469150812056128505939)
                  ·
                    refine ⟨4370203726218084192758909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2913469150812056128505939 4370203726218084192758909)
                    ·
                      refine ⟨1638826397331781572284591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370203726218084192758909 1638826397331781572284591)
                      ·
                        rfl

theorem cell23_3191603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_3191603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191603 prefixEnd_3191603 := by exact prefixLift 3191603
  have htrace : WordTrace (prefixWord ++ tailWord_3191603) baseStart_3191603 baseEnd_3191603 := by
    simpa [prefixWord, tailWord_3191603, baseEnd_3191603] using wordTrace_append hprefix tailTrace_3191603
  have hstable : (prefixWord ++ tailWord_3191603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191603).length < 2 ^ (prefixWord ++ tailWord_3191603).sum := by decide
  have hdescent : baseEnd_3191603 < baseStart_3191603 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191626 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_3191626 : Nat := 118140960795 + 3191626 * 2 ^ 59
def prefixEnd_3191626 : Nat := 4983230072969 + 3 ^ 40 * 3191626 * 2
def baseEnd_3191626 : Nat := 1638838207386834982296985

theorem tailTrace_3191626 : CollatzResearch.WordTrace tailWord_3191626 prefixEnd_3191626 1638838207386834982296985 := by
  unfold tailWord_3191626
  simp only [CollatzResearch.WordTrace]
  refine ⟨29102040883822890792342683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77605442356861042112913821 29102040883822890792342683)
  ·
    refine ⟨43653061325734336188514025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29102040883822890792342683 43653061325734336188514025)
    ·
      refine ⟨32739795994300752141385519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43653061325734336188514025 32739795994300752141385519)
      ·
        refine ⟨49109693991451128212078279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32739795994300752141385519 49109693991451128212078279)
        ·
          refine ⟨73664540987176692318117419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49109693991451128212078279 73664540987176692318117419)
          ·
            refine ⟨110496811480765038477176129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73664540987176692318117419 110496811480765038477176129)
            ·
              refine ⟨82872608610573778857882097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110496811480765038477176129 82872608610573778857882097)
              ·
                refine ⟨62154456457930334143411573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82872608610573778857882097 62154456457930334143411573)
                ·
                  refine ⟨5826980292930968825944835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62154456457930334143411573 5826980292930968825944835)
                  ·
                    refine ⟨8740470439396453238917253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5826980292930968825944835 8740470439396453238917253)
                    ·
                      refine ⟨1638838207386834982296985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8740470439396453238917253 1638838207386834982296985)
                      ·
                        rfl

theorem cell23_3191626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_3191626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191626 prefixEnd_3191626 := by exact prefixLift 3191626
  have htrace : WordTrace (prefixWord ++ tailWord_3191626) baseStart_3191626 baseEnd_3191626 := by
    simpa [prefixWord, tailWord_3191626, baseEnd_3191626] using wordTrace_append hprefix tailTrace_3191626
  have hstable : (prefixWord ++ tailWord_3191626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191626).length < 2 ^ (prefixWord ++ tailWord_3191626).sum := by decide
  have hdescent : baseEnd_3191626 < baseStart_3191626 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191653 : List Nat := [1, 3, 1, 3, 1, 1, 2, 5, 2, 4]
def baseStart_3191653 : Nat := 118140960795 + 3191653 * 2 ^ 59
def prefixEnd_3191653 : Nat := 4983230072969 + 3 ^ 40 * 3191653 * 2
def baseEnd_3191653 : Nat := 546284023788168792219787

theorem tailTrace_3191653 : CollatzResearch.WordTrace tailWord_3191653 prefixEnd_3191653 546284023788168792219787 := by
  unfold tailWord_3191653
  simp only [CollatzResearch.WordTrace]
  refine ⟨116409148306193746780603613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77606098870795831187069075 116409148306193746780603613)
  ·
    refine ⟨43653430614822655042726355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116409148306193746780603613 43653430614822655042726355)
    ·
      refine ⟨65480145922233982564089533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43653430614822655042726355 65480145922233982564089533)
      ·
        refine ⟨24555054720837743461533575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65480145922233982564089533 24555054720837743461533575)
        ·
          refine ⟨36832582081256615192300363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24555054720837743461533575 36832582081256615192300363)
          ·
            refine ⟨55248873121884922788450545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36832582081256615192300363 55248873121884922788450545)
            ·
              refine ⟨41436654841413692091337909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55248873121884922788450545 41436654841413692091337909)
              ·
                refine ⟨3884686391382533633562929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41436654841413692091337909 3884686391382533633562929)
                ·
                  refine ⟨2913514793536900225172197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3884686391382533633562929 2913514793536900225172197)
                  ·
                    refine ⟨546284023788168792219787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913514793536900225172197 546284023788168792219787)
                    ·
                      rfl

theorem cell23_3191653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_3191653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191653 prefixEnd_3191653 := by exact prefixLift 3191653
  have htrace : WordTrace (prefixWord ++ tailWord_3191653) baseStart_3191653 baseEnd_3191653 := by
    simpa [prefixWord, tailWord_3191653, baseEnd_3191653] using wordTrace_append hprefix tailTrace_3191653
  have hstable : (prefixWord ++ tailWord_3191653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191653).length < 2 ^ (prefixWord ++ tailWord_3191653).sum := by decide
  have hdescent : baseEnd_3191653 < baseStart_3191653 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191660 : List Nat := [2, 2, 1, 1, 4, 1, 1, 4, 3, 2, 2]
def baseStart_3191660 : Nat := 118140960795 + 3191660 * 2 ^ 59
def prefixEnd_3191660 : Nat := 4983230072969 + 3 ^ 40 * 3191660 * 2
def baseEnd_3191660 : Nat := 1638855665729087849271829

theorem tailTrace_3191660 : CollatzResearch.WordTrace tailWord_3191660 prefixEnd_3191660 1638855665729087849271829 := by
  unfold tailWord_3191660
  simp only [CollatzResearch.WordTrace]
  refine ⟨58204701808584193488054217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77606269078112257984072289 58204701808584193488054217)
  ·
    refine ⟨43653526356438145116040663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58204701808584193488054217 43653526356438145116040663)
    ·
      refine ⟨65480289534657217674060995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43653526356438145116040663 65480289534657217674060995)
      ·
        refine ⟨98220434301985826511091493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65480289534657217674060995 98220434301985826511091493)
        ·
          refine ⟨18416331431622342470829655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98220434301985826511091493 18416331431622342470829655)
          ·
            refine ⟨27624497147433513706244483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18416331431622342470829655 27624497147433513706244483)
            ·
              refine ⟨41436745721150270559366725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27624497147433513706244483 41436745721150270559366725)
              ·
                refine ⟨7769389822715675729881261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41436745721150270559366725 7769389822715675729881261)
                ·
                  refine ⟨2913521183518378398705473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7769389822715675729881261 2913521183518378398705473)
                  ·
                    refine ⟨2185140887638783799029105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2913521183518378398705473 2185140887638783799029105)
                    ·
                      refine ⟨1638855665729087849271829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185140887638783799029105 1638855665729087849271829)
                      ·
                        rfl

theorem cell23_3191660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_3191660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191660 prefixEnd_3191660 := by exact prefixLift 3191660
  have htrace : WordTrace (prefixWord ++ tailWord_3191660) baseStart_3191660 baseEnd_3191660 := by
    simpa [prefixWord, tailWord_3191660, baseEnd_3191660] using wordTrace_append hprefix tailTrace_3191660
  have hstable : (prefixWord ++ tailWord_3191660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191660).length < 2 ^ (prefixWord ++ tailWord_3191660).sum := by decide
  have hdescent : baseEnd_3191660 < baseStart_3191660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191670 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 4, 4]
def baseStart_3191670 : Nat := 118140960795 + 3191670 * 2 ^ 59
def prefixEnd_3191670 : Nat := 4983230072969 + 3 ^ 40 * 3191670 * 2
def baseEnd_3191670 : Nat := 546286933511877603382261

theorem tailTrace_3191670 : CollatzResearch.WordTrace tailWord_3191670 prefixEnd_3191670 546286933511877603382261 := by
  unfold tailWord_3191670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7275610521695759917748279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77606512231421439122648309 7275610521695759917748279)
  ·
    refine ⟨10913415782543639876622419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7275610521695759917748279 10913415782543639876622419)
    ·
      refine ⟨16370123673815459814933629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10913415782543639876622419 16370123673815459814933629)
      ·
        refine ⟨6138796377680797430600111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16370123673815459814933629 6138796377680797430600111)
        ·
          refine ⟨9208194566521196145900167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6138796377680797430600111 9208194566521196145900167)
          ·
            refine ⟨13812291849781794218850251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208194566521196145900167 13812291849781794218850251)
            ·
              refine ⟨20718437774672691328275377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13812291849781794218850251 20718437774672691328275377)
              ·
                refine ⟨15538828331004518496206533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20718437774672691328275377 15538828331004518496206533)
                ·
                  refine ⟨2913530312063347218038725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15538828331004518496206533 2913530312063347218038725)
                  ·
                    refine ⟨546286933511877603382261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2913530312063347218038725 546286933511877603382261)
                    ·
                      rfl

theorem cell23_3191670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_3191670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191670 prefixEnd_3191670 := by exact prefixLift 3191670
  have htrace : WordTrace (prefixWord ++ tailWord_3191670) baseStart_3191670 baseEnd_3191670 := by
    simpa [prefixWord, tailWord_3191670, baseEnd_3191670] using wordTrace_append hprefix tailTrace_3191670
  have hstable : (prefixWord ++ tailWord_3191670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191670).length < 2 ^ (prefixWord ++ tailWord_3191670).sum := by decide
  have hdescent : baseEnd_3191670 < baseStart_3191670 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191773 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 9]
def baseStart_3191773 : Nat := 118140960795 + 3191773 * 2 ^ 59
def prefixEnd_3191773 : Nat := 4983230072969 + 3 ^ 40 * 3191773 * 2
def baseEnd_3191773 : Nat := 182101521004782878573201

theorem tailTrace_3191773 : CollatzResearch.WordTrace tailWord_3191773 prefixEnd_3191773 182101521004782878573201 := by
  unfold tailWord_3191773
  simp only [CollatzResearch.WordTrace]
  refine ⟨116413525065759007274971973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77609016710506004849981315 116413525065759007274971973)
  ·
    refine ⟨21827535949829813864057245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116413525065759007274971973 21827535949829813864057245)
    ·
      refine ⟨8185325981186180199021467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21827535949829813864057245 8185325981186180199021467)
      ·
        refine ⟨12277988971779270298532201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8185325981186180199021467 12277988971779270298532201)
        ·
          refine ⟨9208491728834452723899151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12277988971779270298532201 9208491728834452723899151)
          ·
            refine ⟨13812737593251679085848727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9208491728834452723899151 13812737593251679085848727)
            ·
              refine ⟨20719106389877518628773091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13812737593251679085848727 20719106389877518628773091)
              ·
                refine ⟨31078659584816277943159637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20719106389877518628773091 31078659584816277943159637)
                ·
                  refine ⟨182101521004782878573201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 31078659584816277943159637 182101521004782878573201)
                  ·
                    rfl

theorem cell23_3191773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 9].length) (baseStart_3191773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191773 prefixEnd_3191773 := by exact prefixLift 3191773
  have htrace : WordTrace (prefixWord ++ tailWord_3191773) baseStart_3191773 baseEnd_3191773 := by
    simpa [prefixWord, tailWord_3191773, baseEnd_3191773] using wordTrace_append hprefix tailTrace_3191773
  have hstable : (prefixWord ++ tailWord_3191773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191773).length < 2 ^ (prefixWord ++ tailWord_3191773).sum := by decide
  have hdescent : baseEnd_3191773 < baseStart_3191773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191863 : List Nat := [1, 1, 3, 1, 2, 2, 1, 6, 6]
def baseStart_3191863 : Nat := 118140960795 + 3191863 * 2 ^ 59
def prefixEnd_3191863 : Nat := 4983230072969 + 3 ^ 40 * 3191863 * 2
def baseEnd_3191863 : Nat := 182106655811327839448155

theorem tailTrace_3191863 : CollatzResearch.WordTrace tailWord_3191863 prefixEnd_3191863 182106655811327839448155 := by
  unfold tailWord_3191863
  simp only [CollatzResearch.WordTrace]
  refine ⟨116416807635432952645748243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77611205090288635097165495 116416807635432952645748243)
  ·
    refine ⟨174625211453149428968622365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116416807635432952645748243 174625211453149428968622365)
    ·
      refine ⟨65484454294931035863233387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174625211453149428968622365 65484454294931035863233387)
      ·
        refine ⟨98226681442396553794850081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65484454294931035863233387 98226681442396553794850081)
        ·
          refine ⟨73670011081797415346137561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98226681442396553794850081 73670011081797415346137561)
          ·
            refine ⟨55252508311348061509603171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73670011081797415346137561 55252508311348061509603171)
            ·
              refine ⟨82878762467022092264404757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55252508311348061509603171 82878762467022092264404757)
              ·
                refine ⟨3884941990641660574893973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 82878762467022092264404757 3884941990641660574893973)
                ·
                  refine ⟨182106655811327839448155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3884941990641660574893973 182106655811327839448155)
                  ·
                    rfl

theorem cell23_3191863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 6, 6].length) (baseStart_3191863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191863 prefixEnd_3191863 := by exact prefixLift 3191863
  have htrace : WordTrace (prefixWord ++ tailWord_3191863) baseStart_3191863 baseEnd_3191863 := by
    simpa [prefixWord, tailWord_3191863, baseEnd_3191863] using wordTrace_append hprefix tailTrace_3191863
  have hstable : (prefixWord ++ tailWord_3191863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191863).length < 2 ^ (prefixWord ++ tailWord_3191863).sum := by decide
  have hdescent : baseEnd_3191863 < baseStart_3191863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191940 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 1, 6]
def baseStart_3191940 : Nat := 118140960795 + 3191940 * 2 ^ 59
def prefixEnd_3191940 : Nat := 4983230072969 + 3 ^ 40 * 3191940 * 2
def baseEnd_3191940 : Nat := 546333146770782251256847

theorem tailTrace_3191940 : CollatzResearch.WordTrace tailWord_3191940 prefixEnd_3191940 546333146770782251256847 := by
  unfold tailWord_3191940
  simp only [CollatzResearch.WordTrace]
  refine ⟨58209808028076997398150637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77613077370769329864200849 58209808028076997398150637)
  ·
    refine ⟨21828678010528874024306489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58209808028076997398150637 21828678010528874024306489)
    ·
      refine ⟨16371508507896655518229867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21828678010528874024306489 16371508507896655518229867)
      ·
        refine ⟨24557262761844983277344801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16371508507896655518229867 24557262761844983277344801)
        ·
          refine ⟨18417947071383737458008601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24557262761844983277344801 18417947071383737458008601)
          ·
            refine ⟨13813460303537803093506451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18417947071383737458008601 13813460303537803093506451)
            ·
              refine ⟨20720190455306704640259677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13813460303537803093506451 20720190455306704640259677)
              ·
                refine ⟨7770071420740014240097379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20720190455306704640259677 7770071420740014240097379)
                ·
                  refine ⟨11655107131110021360146069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770071420740014240097379 11655107131110021360146069)
                  ·
                    refine ⟨546333146770782251256847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11655107131110021360146069 546333146770782251256847)
                    ·
                      rfl

theorem cell23_3191940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 1, 6].length) (baseStart_3191940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191940 prefixEnd_3191940 := by exact prefixLift 3191940
  have htrace : WordTrace (prefixWord ++ tailWord_3191940) baseStart_3191940 baseEnd_3191940 := by
    simpa [prefixWord, tailWord_3191940, baseEnd_3191940] using wordTrace_append hprefix tailTrace_3191940
  have hstable : (prefixWord ++ tailWord_3191940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191940).length < 2 ^ (prefixWord ++ tailWord_3191940).sum := by decide
  have hdescent : baseEnd_3191940 < baseStart_3191940 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191964 : List Nat := [2, 2, 3, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_3191964 : Nat := 118140960795 + 3191964 * 2 ^ 59
def prefixEnd_3191964 : Nat := 4983230072969 + 3 ^ 40 * 3191964 * 2
def baseEnd_3191964 : Nat := 1639011763848054659870431

theorem tailTrace_3191964 : CollatzResearch.WordTrace tailWord_3191964 prefixEnd_3191964 1639011763848054659870431 := by
  unfold tailWord_3191964
  simp only [CollatzResearch.WordTrace]
  refine ⟨58210245704033523447587473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77613660938711364596783297 58210245704033523447587473)
  ·
    refine ⟨43657684278025142585690605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58210245704033523447587473 43657684278025142585690605)
    ·
      refine ⟨16371631604259428469633977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43657684278025142585690605 16371631604259428469633977)
      ·
        refine ⟨12278723703194571352225483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16371631604259428469633977 12278723703194571352225483)
        ·
          refine ⟨18418085554791857028338225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12278723703194571352225483 18418085554791857028338225)
          ·
            refine ⟨13813564166093892771253669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18418085554791857028338225 13813564166093892771253669)
            ·
              refine ⟨2590043281142604894610063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13813564166093892771253669 2590043281142604894610063)
              ·
                refine ⟨3885064921713907341915095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590043281142604894610063 3885064921713907341915095)
                ·
                  refine ⟨5827597382570861012872643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885064921713907341915095 5827597382570861012872643)
                  ·
                    refine ⟨8741396073856291519308965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5827597382570861012872643 8741396073856291519308965)
                    ·
                      refine ⟨1639011763848054659870431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8741396073856291519308965 1639011763848054659870431)
                      ·
                        rfl

theorem cell23_3191964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_3191964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191964 prefixEnd_3191964 := by exact prefixLift 3191964
  have htrace : WordTrace (prefixWord ++ tailWord_3191964) baseStart_3191964 baseEnd_3191964 := by
    simpa [prefixWord, tailWord_3191964, baseEnd_3191964] using wordTrace_append hprefix tailTrace_3191964
  have hstable : (prefixWord ++ tailWord_3191964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191964).length < 2 ^ (prefixWord ++ tailWord_3191964).sum := by decide
  have hdescent : baseEnd_3191964 < baseStart_3191964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191983 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 1, 9]
def baseStart_3191983 : Nat := 118140960795 + 3191983 * 2 ^ 59
def prefixEnd_3191983 : Nat := 4983230072969 + 3 ^ 40 * 3191983 * 2
def baseEnd_3191983 : Nat := 546340506660163361844281

theorem tailTrace_3191983 : CollatzResearch.WordTrace tailWord_3191983 prefixEnd_3191983 546340506660163361844281 := by
  unfold tailWord_3191983
  simp only [CollatzResearch.WordTrace]
  refine ⟨116421184394998213140116603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77614122929998808760077735 116421184394998213140116603)
  ·
    refine ⟨174631776592497319710174905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116421184394998213140116603 174631776592497319710174905)
    ·
      refine ⟨130973832444372989782631179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174631776592497319710174905 130973832444372989782631179)
      ·
        refine ⟨196460748666559484673946769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130973832444372989782631179 196460748666559484673946769)
        ·
          refine ⟨147345561499919613505460077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196460748666559484673946769 147345561499919613505460077)
          ·
            refine ⟨55254585562469855064547529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147345561499919613505460077 55254585562469855064547529)
            ·
              refine ⟨41440939171852391298410647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55254585562469855064547529 41440939171852391298410647)
              ·
                refine ⟨62161408757778586947615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41440939171852391298410647 62161408757778586947615971)
                ·
                  refine ⟨93242113136667880421423957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62161408757778586947615971 93242113136667880421423957)
                  ·
                    refine ⟨546340506660163361844281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 93242113136667880421423957 546340506660163361844281)
                    ·
                      rfl

theorem cell23_3191983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 9].length) (baseStart_3191983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191983 prefixEnd_3191983 := by exact prefixLift 3191983
  have htrace : WordTrace (prefixWord ++ tailWord_3191983) baseStart_3191983 baseEnd_3191983 := by
    simpa [prefixWord, tailWord_3191983, baseEnd_3191983] using wordTrace_append hprefix tailTrace_3191983
  have hstable : (prefixWord ++ tailWord_3191983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191983).length < 2 ^ (prefixWord ++ tailWord_3191983).sum := by decide
  have hdescent : baseEnd_3191983 < baseStart_3191983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3191997 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 3]
def baseStart_3191997 : Nat := 118140960795 + 3191997 * 2 ^ 59
def prefixEnd_3191997 : Nat := 4983230072969 + 3 ^ 40 * 3191997 * 2
def baseEnd_3191997 : Nat := 1639028708709653030757779

theorem tailTrace_3191997 : CollatzResearch.WordTrace tailWord_3191997 prefixEnd_3191997 1639028708709653030757779 := by
  unfold tailWord_3191997
  simp only [CollatzResearch.WordTrace]
  refine ⟨116421695016947493531126245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77614463344631662354084163 116421695016947493531126245)
  ·
    refine ⟨21829067815677655037086171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116421695016947493531126245 21829067815677655037086171)
    ·
      refine ⟨32743601723516482555629257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21829067815677655037086171 32743601723516482555629257)
      ·
        refine ⟨24557701292637361916721943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32743601723516482555629257 24557701292637361916721943)
        ·
          refine ⟨36836551938956042875082915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24557701292637361916721943 36836551938956042875082915)
          ·
            refine ⟨55254827908434064312624373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36836551938956042875082915 55254827908434064312624373)
            ·
              refine ⟨5180140116415693529308535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55254827908434064312624373 5180140116415693529308535)
              ·
                refine ⟨7770210174623540293962803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180140116415693529308535 7770210174623540293962803)
                ·
                  refine ⟨11655315261935310440944205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770210174623540293962803 11655315261935310440944205)
                  ·
                    refine ⟨4370743223225741415354077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11655315261935310440944205 4370743223225741415354077)
                    ·
                      refine ⟨1639028708709653030757779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370743223225741415354077 1639028708709653030757779)
                      ·
                        rfl

theorem cell23_3191997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_3191997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3191997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3191997 prefixEnd_3191997 := by exact prefixLift 3191997
  have htrace : WordTrace (prefixWord ++ tailWord_3191997) baseStart_3191997 baseEnd_3191997 := by
    simpa [prefixWord, tailWord_3191997, baseEnd_3191997] using wordTrace_append hprefix tailTrace_3191997
  have hstable : (prefixWord ++ tailWord_3191997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3191997).length < 2 ^ (prefixWord ++ tailWord_3191997).sum := by decide
  have hdescent : baseEnd_3191997 < baseStart_3191997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3191997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192001 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 3]
def baseStart_3192001 : Nat := 118140960795 + 3192001 * 2 ^ 59
def prefixEnd_3192001 : Nat := 4983230072969 + 3 ^ 40 * 3192001 * 2
def baseEnd_3192001 : Nat := 1639030762632271015107761

theorem tailTrace_3192001 : CollatzResearch.WordTrace tailWord_3192001 prefixEnd_3192001 1639030762632271015107761 := by
  unfold tailWord_3192001
  simp only [CollatzResearch.WordTrace]
  refine ⟨116421840908933002214271857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77614560605955334809514571 116421840908933002214271857)
  ·
    refine ⟨87316380681699751660703893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116421840908933002214271857 87316380681699751660703893)
    ·
      refine ⟨4092955344454675859095495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 87316380681699751660703893 4092955344454675859095495)
      ·
        refine ⟨6139433016682013788643243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4092955344454675859095495 6139433016682013788643243)
        ·
          refine ⟨9209149525023020682964865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6139433016682013788643243 9209149525023020682964865)
          ·
            refine ⟨6906862143767265512223649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209149525023020682964865 6906862143767265512223649)
            ·
              refine ⟨5180146607825449134167737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6906862143767265512223649 5180146607825449134167737)
              ·
                refine ⟨3885109955869086850625803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180146607825449134167737 3885109955869086850625803)
                ·
                  refine ⟨5827664933803630275938705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885109955869086850625803 5827664933803630275938705)
                  ·
                    refine ⟨4370748700352722706954029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827664933803630275938705 4370748700352722706954029)
                    ·
                      refine ⟨1639030762632271015107761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370748700352722706954029 1639030762632271015107761)
                      ·
                        rfl

theorem cell23_3192001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_3192001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192001 prefixEnd_3192001 := by exact prefixLift 3192001
  have htrace : WordTrace (prefixWord ++ tailWord_3192001) baseStart_3192001 baseEnd_3192001 := by
    simpa [prefixWord, tailWord_3192001, baseEnd_3192001] using wordTrace_append hprefix tailTrace_3192001
  have hstable : (prefixWord ++ tailWord_3192001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192001).length < 2 ^ (prefixWord ++ tailWord_3192001).sum := by decide
  have hdescent : baseEnd_3192001 < baseStart_3192001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192003 : List Nat := [1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8]
def baseStart_3192003 : Nat := 118140960795 + 3192003 * 2 ^ 59
def prefixEnd_3192003 : Nat := 4983230072969 + 3 ^ 40 * 3192003 * 2
def baseEnd_3192003 : Nat := 1639031789593580007282751

theorem tailTrace_3192003 : CollatzResearch.WordTrace tailWord_3192003 prefixEnd_3192003 1639031789593580007282751 := by
  unfold tailWord_3192003
  simp only [CollatzResearch.WordTrace]
  refine ⟨116421913854925756555844663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77614609236617171037229775 116421913854925756555844663)
  ·
    refine ⟨174632870782388634833766995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116421913854925756555844663 174632870782388634833766995)
    ·
      refine ⟨261949306173582952250650493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174632870782388634833766995 261949306173582952250650493)
      ·
        refine ⟨98230989815093607093993935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 261949306173582952250650493 98230989815093607093993935)
        ·
          refine ⟨147346484722640410640990903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98230989815093607093993935 147346484722640410640990903)
          ·
            refine ⟨221019727083960615961486355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147346484722640410640990903 221019727083960615961486355)
            ·
              refine ⟨331529590625940923942229533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221019727083960615961486355 331529590625940923942229533)
              ·
                refine ⟨124323596484727846478336075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331529590625940923942229533 124323596484727846478336075)
                ·
                  refine ⟨186485394727091769717504113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124323596484727846478336075 186485394727091769717504113)
                  ·
                    refine ⟨139864046045318827288128085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 186485394727091769717504113 139864046045318827288128085)
                    ·
                      refine ⟨1639031789593580007282751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 139864046045318827288128085 1639031789593580007282751)
                      ·
                        rfl

theorem cell23_3192003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_3192003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192003 prefixEnd_3192003 := by exact prefixLift 3192003
  have htrace : WordTrace (prefixWord ++ tailWord_3192003) baseStart_3192003 baseEnd_3192003 := by
    simpa [prefixWord, tailWord_3192003, baseEnd_3192003] using wordTrace_append hprefix tailTrace_3192003
  have hstable : (prefixWord ++ tailWord_3192003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192003).length < 2 ^ (prefixWord ++ tailWord_3192003).sum := by decide
  have hdescent : baseEnd_3192003 < baseStart_3192003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192004 : List Nat := [2, 3, 3, 1, 3, 2, 2, 7]
def baseStart_3192004 : Nat := 118140960795 + 3192004 * 2 ^ 59
def prefixEnd_3192004 : Nat := 4983230072969 + 3 ^ 40 * 3192004 * 2
def baseEnd_3192004 : Nat := 60704900113860537161861

theorem tailTrace_3192004 : CollatzResearch.WordTrace tailWord_3192004 prefixEnd_3192004 60704900113860537161861 := by
  unfold tailWord_3192004
  simp only [CollatzResearch.WordTrace]
  refine ⟨58210975163961066863315533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77614633551948089151087377 58210975163961066863315533)
  ·
    refine ⟨21829115686485400073743325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58210975163961066863315533 21829115686485400073743325)
    ·
      refine ⟨8185918382432025027653747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21829115686485400073743325 8185918382432025027653747)
      ·
        refine ⟨12278877573648037541480621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8185918382432025027653747 12278877573648037541480621)
        ·
          refine ⟨4604579090118014078055233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12278877573648037541480621 4604579090118014078055233)
          ·
            refine ⟨3453434317588510558541425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4604579090118014078055233 3453434317588510558541425)
            ·
              refine ⟨2590075738191382918906069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3453434317588510558541425 2590075738191382918906069)
              ·
                refine ⟨60704900113860537161861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2590075738191382918906069 60704900113860537161861)
                ·
                  rfl

theorem cell23_3192004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 7].length) (baseStart_3192004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192004 prefixEnd_3192004 := by exact prefixLift 3192004
  have htrace : WordTrace (prefixWord ++ tailWord_3192004) baseStart_3192004 baseEnd_3192004 := by
    simpa [prefixWord, tailWord_3192004, baseEnd_3192004] using wordTrace_append hprefix tailTrace_3192004
  have hstable : (prefixWord ++ tailWord_3192004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192004).length < 2 ^ (prefixWord ++ tailWord_3192004).sum := by decide
  have hdescent : baseEnd_3192004 < baseStart_3192004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192007 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 3, 3, 2]
def baseStart_3192007 : Nat := 118140960795 + 3192007 * 2 ^ 59
def prefixEnd_3192007 : Nat := 4983230072969 + 3 ^ 40 * 3192007 * 2
def baseEnd_3192007 : Nat := 1639033843516197991632733

theorem tailTrace_3192007 : CollatzResearch.WordTrace tailWord_3192007 prefixEnd_3192007 1639033843516197991632733 := by
  unfold tailWord_3192007
  simp only [CollatzResearch.WordTrace]
  refine ⟨116422059746911265238990275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77614706497940843492660183 116422059746911265238990275)
  ·
    refine ⟨174633089620366897858485413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116422059746911265238990275 174633089620366897858485413)
    ·
      refine ⟨32743704303818793348466015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 174633089620366897858485413 32743704303818793348466015)
      ·
        refine ⟨49115556455728190022699023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32743704303818793348466015 49115556455728190022699023)
        ·
          refine ⟨73673334683592285034048535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49115556455728190022699023 73673334683592285034048535)
          ·
            refine ⟨110510002025388427551072803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73673334683592285034048535 110510002025388427551072803)
            ·
              refine ⟨165765003038082641326609205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110510002025388427551072803 165765003038082641326609205)
              ·
                refine ⟨15540469034820247624369613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 165765003038082641326609205 15540469034820247624369613)
                ·
                  refine ⟨5827675888057592859138605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15540469034820247624369613 5827675888057592859138605)
                  ·
                    refine ⟨2185378458021597322176977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5827675888057592859138605 2185378458021597322176977)
                    ·
                      refine ⟨1639033843516197991632733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185378458021597322176977 1639033843516197991632733)
                      ·
                        rfl

theorem cell23_3192007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 3, 2].length) (baseStart_3192007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192007 prefixEnd_3192007 := by exact prefixLift 3192007
  have htrace : WordTrace (prefixWord ++ tailWord_3192007) baseStart_3192007 baseEnd_3192007 := by
    simpa [prefixWord, tailWord_3192007, baseEnd_3192007] using wordTrace_append hprefix tailTrace_3192007
  have hstable : (prefixWord ++ tailWord_3192007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192007).length < 2 ^ (prefixWord ++ tailWord_3192007).sum := by decide
  have hdescent : baseEnd_3192007 < baseStart_3192007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192010 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5]
def baseStart_3192010 : Nat := 118140960795 + 3192010 * 2 ^ 59
def prefixEnd_3192010 : Nat := 4983230072969 + 3 ^ 40 * 3192010 * 2
def baseEnd_3192010 : Nat := 1639035383958161479895219

theorem tailTrace_3192010 : CollatzResearch.WordTrace tailWord_3192010 prefixEnd_3192010 1639035383958161479895219 := by
  unfold tailWord_3192010
  simp only [CollatzResearch.WordTrace]
  refine ⟨29105542291475099187837371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77614779443933597834232989 29105542291475099187837371)
  ·
    refine ⟨43658313437212648781756057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29105542291475099187837371 43658313437212648781756057)
    ·
      refine ⟨32743735077909486586317043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43658313437212648781756057 32743735077909486586317043)
      ·
        refine ⟨49115602616864229879475565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32743735077909486586317043 49115602616864229879475565)
        ·
          refine ⟨18418350981324086204803337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49115602616864229879475565 18418350981324086204803337)
          ·
            refine ⟨13813763235993064653602503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18418350981324086204803337 13813763235993064653602503)
            ·
              refine ⟨20720644853989596980403755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13813763235993064653602503 20720644853989596980403755)
              ·
                refine ⟨31080967280984395470605633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20720644853989596980403755 31080967280984395470605633)
                ·
                  refine ⟨23310725460738296602954225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31080967280984395470605633 23310725460738296602954225)
                  ·
                    refine ⟨17483044095553722452215669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23310725460738296602954225 17483044095553722452215669)
                    ·
                      refine ⟨1639035383958161479895219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17483044095553722452215669 1639035383958161479895219)
                      ·
                        rfl

theorem cell23_3192010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_3192010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192010 prefixEnd_3192010 := by exact prefixLift 3192010
  have htrace : WordTrace (prefixWord ++ tailWord_3192010) baseStart_3192010 baseEnd_3192010 := by
    simpa [prefixWord, tailWord_3192010, baseEnd_3192010] using wordTrace_append hprefix tailTrace_3192010
  have hstable : (prefixWord ++ tailWord_3192010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192010).length < 2 ^ (prefixWord ++ tailWord_3192010).sum := by decide
  have hdescent : baseEnd_3192010 < baseStart_3192010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192040 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3192040 : Nat := 118140960795 + 3192040 * 2 ^ 59
def prefixEnd_3192040 : Nat := 4983230072969 + 3 ^ 40 * 3192040 * 2
def baseEnd_3192040 : Nat := 1639050788377796362520081

theorem tailTrace_3192040 : CollatzResearch.WordTrace tailWord_3192040 prefixEnd_3192040 1639050788377796362520081 := by
  unfold tailWord_3192040
  simp only [CollatzResearch.WordTrace]
  refine ⟨58211631677895855937470787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77615508903861141249961049 58211631677895855937470787)
  ·
    refine ⟨87317447516843783906206181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58211631677895855937470787 87317447516843783906206181)
    ·
      refine ⟨16372021409408209482413659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87317447516843783906206181 16372021409408209482413659)
      ·
        refine ⟨24558032114112314223620489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16372021409408209482413659 24558032114112314223620489)
        ·
          refine ⟨18418524085584235667715367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24558032114112314223620489 18418524085584235667715367)
          ·
            refine ⟨27627786128376353501573051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18418524085584235667715367 27627786128376353501573051)
            ·
              refine ⟨41441679192564530252359577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27627786128376353501573051 41441679192564530252359577)
              ·
                refine ⟨31081259394423397689269683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41441679192564530252359577 31081259394423397689269683)
                ·
                  refine ⟨46621889091635096533904525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31081259394423397689269683 46621889091635096533904525)
                  ·
                    refine ⟨17483208409363161200214197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46621889091635096533904525 17483208409363161200214197)
                    ·
                      refine ⟨1639050788377796362520081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17483208409363161200214197 1639050788377796362520081)
                      ·
                        rfl

theorem cell23_3192040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3192040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192040 prefixEnd_3192040 := by exact prefixLift 3192040
  have htrace : WordTrace (prefixWord ++ tailWord_3192040) baseStart_3192040 baseEnd_3192040 := by
    simpa [prefixWord, tailWord_3192040, baseEnd_3192040] using wordTrace_append hprefix tailTrace_3192040
  have hstable : (prefixWord ++ tailWord_3192040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192040).length < 2 ^ (prefixWord ++ tailWord_3192040).sum := by decide
  have hdescent : baseEnd_3192040 < baseStart_3192040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192052 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 1, 2, 3]
def baseStart_3192052 : Nat := 118140960795 + 3192052 * 2 ^ 59
def prefixEnd_3192052 : Nat := 4983230072969 + 3 ^ 40 * 3192052 * 2
def baseEnd_3192052 : Nat := 1639056950145650315570027

theorem tailTrace_3192052 : CollatzResearch.WordTrace tailWord_3192052 prefixEnd_3192052 1639056950145650315570027 := by
  unfold tailWord_3192052
  simp only [CollatzResearch.WordTrace]
  refine ⟨58211850515874118962189205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77615800687832158616252273 58211850515874118962189205)
  ·
    refine ⟨2728680492931599326352619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58211850515874118962189205 2728680492931599326352619)
    ·
      refine ⟨4093020739397398989528929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2728680492931599326352619 4093020739397398989528929)
      ·
        refine ⟨3069765554548049242146697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4093020739397398989528929 3069765554548049242146697)
        ·
          refine ⟨2302324165911036931610023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3069765554548049242146697 2302324165911036931610023)
          ·
            refine ⟨3453486248866555397415035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2302324165911036931610023 3453486248866555397415035)
            ·
              refine ⟨5180229373299833096122553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453486248866555397415035 5180229373299833096122553)
              ·
                refine ⟨3885172029974874822091915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5180229373299833096122553 3885172029974874822091915)
                ·
                  refine ⟨5827758044962312233137873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885172029974874822091915 5827758044962312233137873)
                  ·
                    refine ⟨4370818533721734174853405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827758044962312233137873 4370818533721734174853405)
                    ·
                      refine ⟨1639056950145650315570027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370818533721734174853405 1639056950145650315570027)
                      ·
                        rfl

theorem cell23_3192052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_3192052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192052 prefixEnd_3192052 := by exact prefixLift 3192052
  have htrace : WordTrace (prefixWord ++ tailWord_3192052) baseStart_3192052 baseEnd_3192052 := by
    simpa [prefixWord, tailWord_3192052, baseEnd_3192052] using wordTrace_append hprefix tailTrace_3192052
  have hstable : (prefixWord ++ tailWord_3192052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192052).length < 2 ^ (prefixWord ++ tailWord_3192052).sum := by decide
  have hdescent : baseEnd_3192052 < baseStart_3192052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192054 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2]
def baseStart_3192054 : Nat := 118140960795 + 3192054 * 2 ^ 59
def prefixEnd_3192054 : Nat := 4983230072969 + 3 ^ 40 * 3192054 * 2
def baseEnd_3192054 : Nat := 1639057977106959307745017

theorem tailTrace_3192054 : CollatzResearch.WordTrace tailWord_3192054 prefixEnd_3192054 1639057977106959307745017 := by
  unfold tailWord_3192054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276485873608812016621951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77615849318493994843967477 7276485873608812016621951)
  ·
    refine ⟨10914728810413218024932927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7276485873608812016621951 10914728810413218024932927)
    ·
      refine ⟨16372093215619827037399391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10914728810413218024932927 16372093215619827037399391)
      ·
        refine ⟨24558139823429740556099087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16372093215619827037399391 24558139823429740556099087)
        ·
          refine ⟨36837209735144610834148631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24558139823429740556099087 36837209735144610834148631)
          ·
            refine ⟨55255814602716916251222947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36837209735144610834148631 55255814602716916251222947)
            ·
              refine ⟨82883721904075374376834421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55255814602716916251222947 82883721904075374376834421)
              ·
                refine ⟨7770348928507066347828227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 82883721904075374376834421 7770348928507066347828227)
                ·
                  refine ⟨11655523392760599521742341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770348928507066347828227 11655523392760599521742341)
                  ·
                    refine ⟨2185410636142612410326689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11655523392760599521742341 2185410636142612410326689)
                    ·
                      refine ⟨1639057977106959307745017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185410636142612410326689 1639057977106959307745017)
                      ·
                        rfl

theorem cell23_3192054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2].length) (baseStart_3192054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192054 prefixEnd_3192054 := by exact prefixLift 3192054
  have htrace : WordTrace (prefixWord ++ tailWord_3192054) baseStart_3192054 baseEnd_3192054 := by
    simpa [prefixWord, tailWord_3192054, baseEnd_3192054] using wordTrace_append hprefix tailTrace_3192054
  have hstable : (prefixWord ++ tailWord_3192054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192054).length < 2 ^ (prefixWord ++ tailWord_3192054).sum := by decide
  have hdescent : baseEnd_3192054 < baseStart_3192054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192087 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 3]
def baseStart_3192087 : Nat := 118140960795 + 3192087 * 2 ^ 59
def prefixEnd_3192087 : Nat := 4983230072969 + 3 ^ 40 * 3192087 * 2
def baseEnd_3192087 : Nat := 1639074921968557678632365

theorem tailTrace_3192087 : CollatzResearch.WordTrace tailWord_3192087 prefixEnd_3192087 1639074921968557678632365 := by
  unfold tailWord_3192087
  simp only [CollatzResearch.WordTrace]
  refine ⟨116424977586621438901902515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77616651724414292601268343 116424977586621438901902515)
  ·
    refine ⟨174637466379932158352853773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116424977586621438901902515 174637466379932158352853773)
    ·
      refine ⟨65489049892474559382320165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174637466379932158352853773 65489049892474559382320165)
      ·
        refine ⟨12279196854838979884185031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65489049892474559382320165 12279196854838979884185031)
        ·
          refine ⟨18418795282258469826277547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12279196854838979884185031 18418795282258469826277547)
          ·
            refine ⟨27628192923387704739416321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18418795282258469826277547 27628192923387704739416321)
            ·
              refine ⟨20721144692540778554562241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27628192923387704739416321 20721144692540778554562241)
              ·
                refine ⟨15540858519405583915921681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20721144692540778554562241 15540858519405583915921681)
                ·
                  refine ⟨11655643889554187936941261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15540858519405583915921681 11655643889554187936941261)
                  ·
                    refine ⟨4370866458582820476352973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11655643889554187936941261 4370866458582820476352973)
                    ·
                      refine ⟨1639074921968557678632365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370866458582820476352973 1639074921968557678632365)
                      ·
                        rfl

theorem cell23_3192087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_3192087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192087 prefixEnd_3192087 := by exact prefixLift 3192087
  have htrace : WordTrace (prefixWord ++ tailWord_3192087) baseStart_3192087 baseEnd_3192087 := by
    simpa [prefixWord, tailWord_3192087, baseEnd_3192087] using wordTrace_append hprefix tailTrace_3192087
  have hstable : (prefixWord ++ tailWord_3192087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192087).length < 2 ^ (prefixWord ++ tailWord_3192087).sum := by decide
  have hdescent : baseEnd_3192087 < baseStart_3192087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192104 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_3192104 : Nat := 118140960795 + 3192104 * 2 ^ 59
def prefixEnd_3192104 : Nat := 4983230072969 + 3 ^ 40 * 3192104 * 2
def baseEnd_3192104 : Nat := 1639083651139684112119787

theorem tailTrace_3192104 : CollatzResearch.WordTrace tailWord_3192104 prefixEnd_3192104 1639083651139684112119787 := by
  unfold tailWord_3192104
  simp only [CollatzResearch.WordTrace]
  refine ⟨58212798813779925402635683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77617065085039900536847577 58212798813779925402635683)
  ·
    refine ⟨87319198220669888103953525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58212798813779925402635683 87319198220669888103953525)
    ·
      refine ⟨8186174833187802009745643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87319198220669888103953525 8186174833187802009745643)
      ·
        refine ⟨12279262249781703014618465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8186174833187802009745643 12279262249781703014618465)
        ·
          refine ⟨9209446687336277260963849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12279262249781703014618465 9209446687336277260963849)
          ·
            refine ⟨6907085015502207945722887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9209446687336277260963849 6907085015502207945722887)
            ·
              refine ⟨10360627523253311918584331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907085015502207945722887 10360627523253311918584331)
              ·
                refine ⟨15540941284879967877876497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10360627523253311918584331 15540941284879967877876497)
                ·
                  refine ⟨11655705963659975908407373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15540941284879967877876497 11655705963659975908407373)
                  ·
                    refine ⟨4370889736372490965652765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11655705963659975908407373 4370889736372490965652765)
                    ·
                      refine ⟨1639083651139684112119787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370889736372490965652765 1639083651139684112119787)
                      ·
                        rfl

theorem cell23_3192104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_3192104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192104 prefixEnd_3192104 := by exact prefixLift 3192104
  have htrace : WordTrace (prefixWord ++ tailWord_3192104) baseStart_3192104 baseEnd_3192104 := by
    simpa [prefixWord, tailWord_3192104, baseEnd_3192104] using wordTrace_append hprefix tailTrace_3192104
  have hstable : (prefixWord ++ tailWord_3192104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192104).length < 2 ^ (prefixWord ++ tailWord_3192104).sum := by decide
  have hdescent : baseEnd_3192104 < baseStart_3192104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192124 : List Nat := [2, 2, 2, 2, 1, 5, 1, 1, 2, 5]
def baseStart_3192124 : Nat := 118140960795 + 3192124 * 2 ^ 59
def prefixEnd_3192124 : Nat := 4983230072969 + 3 ^ 40 * 3192124 * 2
def baseEnd_3192124 : Nat := 546364640250924677956565

theorem tailTrace_3192124 : CollatzResearch.WordTrace tailWord_3192124 prefixEnd_3192124 546364640250924677956565 := by
  unfold tailWord_3192124
  simp only [CollatzResearch.WordTrace]
  refine ⟨58213163543743697110499713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77617551391658262813999617 58213163543743697110499713)
  ·
    refine ⟨43659872657807772832874785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58213163543743697110499713 43659872657807772832874785)
    ·
      refine ⟨32744904493355829624656089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43659872657807772832874785 32744904493355829624656089)
      ·
        refine ⟨24558678370016872218492067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32744904493355829624656089 24558678370016872218492067)
        ·
          refine ⟨36838017555025308327738101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24558678370016872218492067 36838017555025308327738101)
          ·
            refine ⟨3453564145783622655725447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36838017555025308327738101 3453564145783622655725447)
            ·
              refine ⟨5180346218675433983588171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3453564145783622655725447 5180346218675433983588171)
              ·
                refine ⟨7770519328013150975382257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5180346218675433983588171 7770519328013150975382257)
                ·
                  refine ⟨5827889496009863231536693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7770519328013150975382257 5827889496009863231536693)
                  ·
                    refine ⟨546364640250924677956565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5827889496009863231536693 546364640250924677956565)
                    ·
                      rfl

theorem cell23_3192124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_3192124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192124 prefixEnd_3192124 := by exact prefixLift 3192124
  have htrace : WordTrace (prefixWord ++ tailWord_3192124) baseStart_3192124 baseEnd_3192124 := by
    simpa [prefixWord, tailWord_3192124, baseEnd_3192124] using wordTrace_append hprefix tailTrace_3192124
  have hstable : (prefixWord ++ tailWord_3192124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192124).length < 2 ^ (prefixWord ++ tailWord_3192124).sum := by decide
  have hdescent : baseEnd_3192124 < baseStart_3192124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192127 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 4]
def baseStart_3192127 : Nat := 118140960795 + 3192127 * 2 ^ 59
def prefixEnd_3192127 : Nat := 4983230072969 + 3 ^ 40 * 3192127 * 2
def baseEnd_3192127 : Nat := 1639095461194737522132181

theorem tailTrace_3192127 : CollatzResearch.WordTrace tailWord_3192127 prefixEnd_3192127 1639095461194737522132181 := by
  unfold tailWord_3192127
  simp only [CollatzResearch.WordTrace]
  refine ⟨116426436506476525733358635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77617624337651017155572423 116426436506476525733358635)
  ·
    refine ⟨174639654759714788600037953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116426436506476525733358635 174639654759714788600037953)
    ·
      refine ⟨130979741069786091450028465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174639654759714788600037953 130979741069786091450028465)
      ·
        refine ⟨98234805802339568587521349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 130979741069786091450028465 98234805802339568587521349)
        ·
          refine ⟨18419026087938669110160253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98234805802339568587521349 18419026087938669110160253)
          ·
            refine ⟨6907134782977000916310095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18419026087938669110160253 6907134782977000916310095)
            ·
              refine ⟨10360702174465501374465143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907134782977000916310095 10360702174465501374465143)
              ·
                refine ⟨15541053261698252061697715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10360702174465501374465143 15541053261698252061697715)
                ·
                  refine ⟨23311579892547378092546573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15541053261698252061697715 23311579892547378092546573)
                  ·
                    refine ⟨8741842459705266784704965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23311579892547378092546573 8741842459705266784704965)
                    ·
                      refine ⟨1639095461194737522132181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8741842459705266784704965 1639095461194737522132181)
                      ·
                        rfl

theorem cell23_3192127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_3192127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192127 prefixEnd_3192127 := by exact prefixLift 3192127
  have htrace : WordTrace (prefixWord ++ tailWord_3192127) baseStart_3192127 baseEnd_3192127 := by
    simpa [prefixWord, tailWord_3192127, baseEnd_3192127] using wordTrace_append hprefix tailTrace_3192127
  have hstable : (prefixWord ++ tailWord_3192127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192127).length < 2 ^ (prefixWord ++ tailWord_3192127).sum := by decide
  have hdescent : baseEnd_3192127 < baseStart_3192127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192147 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 3]
def baseStart_3192147 : Nat := 118140960795 + 3192147 * 2 ^ 59
def prefixEnd_3192147 : Nat := 4983230072969 + 3 ^ 40 * 3192147 * 2
def baseEnd_3192147 : Nat := 1639105730807827443882089

theorem tailTrace_3192147 : CollatzResearch.WordTrace tailWord_3192147 prefixEnd_3192147 1639105730807827443882089 := by
  unfold tailWord_3192147
  simp only [CollatzResearch.WordTrace]
  refine ⟨116427165966404069149086695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77618110644269379432724463 116427165966404069149086695)
  ·
    refine ⟨174640748949606103723630043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116427165966404069149086695 174640748949606103723630043)
    ·
      refine ⟨261961123424409155585445065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174640748949606103723630043 261961123424409155585445065)
      ·
        refine ⟨196470842568306866689083799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261961123424409155585445065 196470842568306866689083799)
        ·
          refine ⟨294706263852460300033625699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 196470842568306866689083799 294706263852460300033625699)
          ·
            refine ⟨442059395778690450050438549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294706263852460300033625699 442059395778690450050438549)
            ·
              refine ⟨20721534177126114846114307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 442059395778690450050438549 20721534177126114846114307)
              ·
                refine ⟨31082301265689172269171461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20721534177126114846114307 31082301265689172269171461)
                ·
                  refine ⟨5827931487316719800469649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31082301265689172269171461 5827931487316719800469649)
                  ·
                    refine ⟨4370948615487539850352237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5827931487316719800469649 4370948615487539850352237)
                    ·
                      refine ⟨1639105730807827443882089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4370948615487539850352237 1639105730807827443882089)
                      ·
                        rfl

theorem cell23_3192147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_3192147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192147 prefixEnd_3192147 := by exact prefixLift 3192147
  have htrace : WordTrace (prefixWord ++ tailWord_3192147) baseStart_3192147 baseEnd_3192147 := by
    simpa [prefixWord, tailWord_3192147, baseEnd_3192147] using wordTrace_append hprefix tailTrace_3192147
  have hstable : (prefixWord ++ tailWord_3192147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192147).length < 2 ^ (prefixWord ++ tailWord_3192147).sum := by decide
  have hdescent : baseEnd_3192147 < baseStart_3192147 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192227 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 1, 6]
def baseStart_3192227 : Nat := 118140960795 + 3192227 * 2 ^ 59
def prefixEnd_3192227 : Nat := 4983230072969 + 3 ^ 40 * 3192227 * 2
def baseEnd_3192227 : Nat := 546382269753395710293907

theorem tailTrace_3192227 : CollatzResearch.WordTrace tailWord_3192227 prefixEnd_3192227 546382269753395710293907 := by
  unfold tailWord_3192227
  simp only [CollatzResearch.WordTrace]
  refine ⟨116430083806114242811998935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77620055870742828541332623 116430083806114242811998935)
  ·
    refine ⟨174645125709171364217998403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116430083806114242811998935 174645125709171364217998403)
    ·
      refine ⟨261967688563757046326997605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174645125709171364217998403 261967688563757046326997605)
      ·
        refine ⟨49118941605704446186312051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261967688563757046326997605 49118941605704446186312051)
        ·
          refine ⟨73678412408556669279468077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49118941605704446186312051 73678412408556669279468077)
          ·
            refine ⟨27629404653208750979800529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73678412408556669279468077 27629404653208750979800529)
            ·
              refine ⟨20722053489906563234850397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27629404653208750979800529 20722053489906563234850397)
              ·
                refine ⟨7770770058714961213068899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20722053489906563234850397 7770770058714961213068899)
                ·
                  refine ⟨11656155088072441819603349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7770770058714961213068899 11656155088072441819603349)
                  ·
                    refine ⟨546382269753395710293907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11656155088072441819603349 546382269753395710293907)
                    ·
                      rfl

theorem cell23_3192227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 1, 6].length) (baseStart_3192227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192227 prefixEnd_3192227 := by exact prefixLift 3192227
  have htrace : WordTrace (prefixWord ++ tailWord_3192227) baseStart_3192227 baseEnd_3192227 := by
    simpa [prefixWord, tailWord_3192227, baseEnd_3192227] using wordTrace_append hprefix tailTrace_3192227
  have hstable : (prefixWord ++ tailWord_3192227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192227).length < 2 ^ (prefixWord ++ tailWord_3192227).sum := by decide
  have hdescent : baseEnd_3192227 < baseStart_3192227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192278 : List Nat := [5, 2, 1, 1, 1, 2, 2, 3, 2, 4]
def baseStart_3192278 : Nat := 118140960795 + 3192278 * 2 ^ 59
def prefixEnd_3192278 : Nat := 4983230072969 + 3 ^ 40 * 3192278 * 2
def baseEnd_3192278 : Nat := 546390998924522143781329

theorem tailTrace_3192278 : CollatzResearch.WordTrace tailWord_3192278 prefixEnd_3192278 546390998924522143781329 := by
  unfold tailWord_3192278
  simp only [CollatzResearch.WordTrace]
  refine ⟨7276996495558092407631593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77621295952619652348070325 7276996495558092407631593)
  ·
    refine ⟨5457747371668569305723695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7276996495558092407631593 5457747371668569305723695)
    ·
      refine ⟨8186621057502853958585543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5457747371668569305723695 8186621057502853958585543)
      ·
        refine ⟨12279931586254280937878315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8186621057502853958585543 12279931586254280937878315)
        ·
          refine ⟨18419897379381421406817473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12279931586254280937878315 18419897379381421406817473)
          ·
            refine ⟨13814923034536066055113105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18419897379381421406817473 13814923034536066055113105)
            ·
              refine ⟨10361192275902049541334829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13814923034536066055113105 10361192275902049541334829)
              ·
                refine ⟨3885447103463268578000561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10361192275902049541334829 3885447103463268578000561)
                ·
                  refine ⟨2914085327597451433500421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885447103463268578000561 2914085327597451433500421)
                  ·
                    refine ⟨546390998924522143781329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914085327597451433500421 546390998924522143781329)
                    ·
                      rfl

theorem cell23_3192278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_3192278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192278 prefixEnd_3192278 := by exact prefixLift 3192278
  have htrace : WordTrace (prefixWord ++ tailWord_3192278) baseStart_3192278 baseEnd_3192278 := by
    simpa [prefixWord, tailWord_3192278, baseEnd_3192278] using wordTrace_append hprefix tailTrace_3192278
  have hstable : (prefixWord ++ tailWord_3192278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192278).length < 2 ^ (prefixWord ++ tailWord_3192278).sum := by decide
  have hdescent : baseEnd_3192278 < baseStart_3192278 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192287 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 2, 7]
def baseStart_3192287 : Nat := 118140960795 + 3192287 * 2 ^ 59
def prefixEnd_3192287 : Nat := 4983230072969 + 3 ^ 40 * 3192287 * 2
def baseEnd_3192287 : Nat := 546392539366485632043815

theorem tailTrace_3192287 : CollatzResearch.WordTrace tailWord_3192287 prefixEnd_3192287 546392539366485632043815 := by
  unfold tailWord_3192287
  simp only [CollatzResearch.WordTrace]
  refine ⟨116432272185896873059183115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77621514790597915372788743 116432272185896873059183115)
  ·
    refine ⟨174648408278845309588774673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116432272185896873059183115 174648408278845309588774673)
    ·
      refine ⟨130986306209133982191581005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174648408278845309588774673 130986306209133982191581005)
      ·
        refine ⟨49119864828425243321842877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130986306209133982191581005 49119864828425243321842877)
        ·
          refine ⟨18419949310659466245691079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49119864828425243321842877 18419949310659466245691079)
          ·
            refine ⟨27629923965989199368536619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18419949310659466245691079 27629923965989199368536619)
            ·
              refine ⟨41444885948983799052804929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27629923965989199368536619 41444885948983799052804929)
              ·
                refine ⟨31083664461737849289603697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41444885948983799052804929 31083664461737849289603697)
                ·
                  refine ⟨23312748346303386967202773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31083664461737849289603697 23312748346303386967202773)
                  ·
                    refine ⟨546392539366485632043815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23312748346303386967202773 546392539366485632043815)
                    ·
                      rfl

theorem cell23_3192287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 2, 7].length) (baseStart_3192287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192287 prefixEnd_3192287 := by exact prefixLift 3192287
  have htrace : WordTrace (prefixWord ++ tailWord_3192287) baseStart_3192287 baseEnd_3192287 := by
    simpa [prefixWord, tailWord_3192287, baseEnd_3192287] using wordTrace_append hprefix tailTrace_3192287
  have hstable : (prefixWord ++ tailWord_3192287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192287).length < 2 ^ (prefixWord ++ tailWord_3192287).sum := by decide
  have hdescent : baseEnd_3192287 < baseStart_3192287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192307 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4]
def baseStart_3192307 : Nat := 118140960795 + 3192307 * 2 ^ 59
def prefixEnd_3192307 : Nat := 4983230072969 + 3 ^ 40 * 3192307 * 2
def baseEnd_3192307 : Nat := 1639187887712546817881353

theorem tailTrace_3192307 : CollatzResearch.WordTrace tailWord_3192307 prefixEnd_3192307 1639187887712546817881353 := by
  unfold tailWord_3192307
  simp only [CollatzResearch.WordTrace]
  refine ⟨116433001645824416474911175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77622001097216277649940783 116433001645824416474911175)
  ·
    refine ⟨174649502468736624712366763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116433001645824416474911175 174649502468736624712366763)
    ·
      refine ⟨261974253703104937068550145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174649502468736624712366763 261974253703104937068550145)
      ·
        refine ⟨196480690277328702801412609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 261974253703104937068550145 196480690277328702801412609)
        ·
          refine ⟨147360517707996527101059457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196480690277328702801412609 147360517707996527101059457)
          ·
            refine ⟨110520388280997395325794593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147360517707996527101059457 110520388280997395325794593)
            ·
              refine ⟨82890291210748046494345945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110520388280997395325794593 82890291210748046494345945)
              ·
                refine ⟨62167718408061034870759459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82890291210748046494345945 62167718408061034870759459)
                ·
                  refine ⟨93251577612091552306139189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62167718408061034870759459 93251577612091552306139189)
                  ·
                    refine ⟨8742335401133583028700549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 93251577612091552306139189 8742335401133583028700549)
                    ·
                      refine ⟨1639187887712546817881353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8742335401133583028700549 1639187887712546817881353)
                      ·
                        rfl

theorem cell23_3192307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_3192307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192307 prefixEnd_3192307 := by exact prefixLift 3192307
  have htrace : WordTrace (prefixWord ++ tailWord_3192307) baseStart_3192307 baseEnd_3192307 := by
    simpa [prefixWord, tailWord_3192307, baseEnd_3192307] using wordTrace_append hprefix tailTrace_3192307
  have hstable : (prefixWord ++ tailWord_3192307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192307).length < 2 ^ (prefixWord ++ tailWord_3192307).sum := by decide
  have hdescent : baseEnd_3192307 < baseStart_3192307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192354 : List Nat := [3, 3, 1, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3192354 : Nat := 118140960795 + 3192354 * 2 ^ 59
def prefixEnd_3192354 : Nat := 4983230072969 + 3 ^ 40 * 3192354 * 2
def baseEnd_3192354 : Nat := 1639212021303308133993637

theorem tailTrace_3192354 : CollatzResearch.WordTrace tailWord_3192354 prefixEnd_3192354 1639212021303308133993637 := by
  unfold tailWord_3192354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29108678969163535875468029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77623143917769429001248077 29108678969163535875468029)
  ·
    refine ⟨10915754613436325953300511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29108678969163535875468029 10915754613436325953300511)
    ·
      refine ⟨16373631920154488929950767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10915754613436325953300511 16373631920154488929950767)
      ·
        refine ⟨24560447880231733394926151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16373631920154488929950767 24560447880231733394926151)
        ·
          refine ⟨36840671820347600092389227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24560447880231733394926151 36840671820347600092389227)
          ·
            refine ⟨55261007730521400138583841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36840671820347600092389227 55261007730521400138583841)
            ·
              refine ⟨41445755797891050103937881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55261007730521400138583841 41445755797891050103937881)
              ·
                refine ⟨31084316848418287577953411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41445755797891050103937881 31084316848418287577953411)
                ·
                  refine ⟨46626475272627431366930117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31084316848418287577953411 46626475272627431366930117)
                  ·
                    refine ⟨8742464113617643381299397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46626475272627431366930117 8742464113617643381299397)
                    ·
                      refine ⟨1639212021303308133993637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8742464113617643381299397 1639212021303308133993637)
                      ·
                        rfl

theorem cell23_3192354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3192354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192354 prefixEnd_3192354 := by exact prefixLift 3192354
  have htrace : WordTrace (prefixWord ++ tailWord_3192354) baseStart_3192354 baseEnd_3192354 := by
    simpa [prefixWord, tailWord_3192354, baseEnd_3192354] using wordTrace_append hprefix tailTrace_3192354
  have hstable : (prefixWord ++ tailWord_3192354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192354).length < 2 ^ (prefixWord ++ tailWord_3192354).sum := by decide
  have hdescent : baseEnd_3192354 < baseStart_3192354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192367 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 6]
def baseStart_3192367 : Nat := 118140960795 + 3192367 * 2 ^ 59
def prefixEnd_3192367 : Nat := 4983230072969 + 3 ^ 40 * 3192367 * 2
def baseEnd_3192367 : Nat := 1639218696551816583131077

theorem tailTrace_3192367 : CollatzResearch.WordTrace tailWord_3192367 prefixEnd_3192367 1639218696551816583131077 := by
  unfold tailWord_3192367
  simp only [CollatzResearch.WordTrace]
  refine ⟨116435190025607046722095355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77623460017071364481396903 116435190025607046722095355)
  ·
    refine ⟨174652785038410570083143033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116435190025607046722095355 174652785038410570083143033)
    ·
      refine ⟨130989588778807927562357275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174652785038410570083143033 130989588778807927562357275)
      ·
        refine ⟨196484383168211891343535913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130989588778807927562357275 196484383168211891343535913)
        ·
          refine ⟨147363287376158918507651935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 196484383168211891343535913 147363287376158918507651935)
          ·
            refine ⟨221044931064238377761477903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147363287376158918507651935 221044931064238377761477903)
            ·
              refine ⟨331567396596357566642216855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221044931064238377761477903 331567396596357566642216855)
              ·
                refine ⟨497351094894536349963325283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 331567396596357566642216855 497351094894536349963325283)
                ·
                  refine ⟨746026642341804524944987925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 497351094894536349963325283 746026642341804524944987925)
                  ·
                    refine ⟨34969998859772087106796309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 746026642341804524944987925 34969998859772087106796309)
                    ·
                      refine ⟨1639218696551816583131077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 34969998859772087106796309 1639218696551816583131077)
                      ·
                        rfl

theorem cell23_3192367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_3192367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192367 prefixEnd_3192367 := by exact prefixLift 3192367
  have htrace : WordTrace (prefixWord ++ tailWord_3192367) baseStart_3192367 baseEnd_3192367 := by
    simpa [prefixWord, tailWord_3192367, baseEnd_3192367] using wordTrace_append hprefix tailTrace_3192367
  have hstable : (prefixWord ++ tailWord_3192367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192367).length < 2 ^ (prefixWord ++ tailWord_3192367).sum := by decide
  have hdescent : baseEnd_3192367 < baseStart_3192367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192394 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 4, 5]
def baseStart_3192394 : Nat := 118140960795 + 3192394 * 2 ^ 59
def prefixEnd_3192394 : Nat := 4983230072969 + 3 ^ 40 * 3192394 * 2
def baseEnd_3192394 : Nat := 546410853509829325831151

theorem tailTrace_3192394 : CollatzResearch.WordTrace tailWord_3192394 prefixEnd_3192394 546410853509829325831151 := by
  unfold tailWord_3192394
  simp only [CollatzResearch.WordTrace]
  refine ⟨29109043699127307583332059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77624116531006153555552157 29109043699127307583332059)
  ·
    refine ⟨43663565548690961374998089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29109043699127307583332059 43663565548690961374998089)
    ·
      refine ⟨32747674161518221031248567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43663565548690961374998089 32747674161518221031248567)
      ·
        refine ⟨49121511242277331546872851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32747674161518221031248567 49121511242277331546872851)
        ·
          refine ⟨73682266863415997320309277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49121511242277331546872851 73682266863415997320309277)
          ·
            refine ⟨27630850073780998995115979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73682266863415997320309277 27630850073780998995115979)
            ·
              refine ⟨41446275110671498492673969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27630850073780998995115979 41446275110671498492673969)
              ·
                refine ⟨31084706333003623869505477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41446275110671498492673969 31084706333003623869505477)
                ·
                  refine ⟨5828382437438179475532277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31084706333003623869505477 5828382437438179475532277)
                  ·
                    refine ⟨546410853509829325831151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5828382437438179475532277 546410853509829325831151)
                    ·
                      rfl

theorem cell23_3192394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 4, 5].length) (baseStart_3192394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192394 prefixEnd_3192394 := by exact prefixLift 3192394
  have htrace : WordTrace (prefixWord ++ tailWord_3192394) baseStart_3192394 baseEnd_3192394 := by
    simpa [prefixWord, tailWord_3192394, baseEnd_3192394] using wordTrace_append hprefix tailTrace_3192394
  have hstable : (prefixWord ++ tailWord_3192394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192394).length < 2 ^ (prefixWord ++ tailWord_3192394).sum := by decide
  have hdescent : baseEnd_3192394 < baseStart_3192394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192404 : List Nat := [2, 4, 1, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3192404 : Nat := 118140960795 + 3192404 * 2 ^ 59
def prefixEnd_3192404 : Nat := 4983230072969 + 3 ^ 40 * 3192404 * 2
def baseEnd_3192404 : Nat := 1639237695336032938368407

theorem tailTrace_3192404 : CollatzResearch.WordTrace tailWord_3192404 prefixEnd_3192404 1639237695336032938368407 := by
  unfold tailWord_3192404
  simp only [CollatzResearch.WordTrace]
  refine ⟨58218269763236501020596133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77624359684315334694128177 58218269763236501020596133)
  ·
    refine ⟨10915925580606843941361775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58218269763236501020596133 10915925580606843941361775)
    ·
      refine ⟨16373888370910265912042663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10915925580606843941361775 16373888370910265912042663)
      ·
        refine ⟨24560832556365398868063995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16373888370910265912042663 24560832556365398868063995)
        ·
          refine ⟨36841248834548098302095993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24560832556365398868063995 36841248834548098302095993)
          ·
            refine ⟨27630936625911073726571995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36841248834548098302095993 27630936625911073726571995)
            ·
              refine ⟨41446404938866610589857993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27630936625911073726571995 41446404938866610589857993)
              ·
                refine ⟨31084803704149957942393495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41446404938866610589857993 31084803704149957942393495)
                ·
                  refine ⟨46627205556224936913590243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31084803704149957942393495 46627205556224936913590243)
                  ·
                    refine ⟨69940808334337405370385365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46627205556224936913590243 69940808334337405370385365)
                    ·
                      refine ⟨1639237695336032938368407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 69940808334337405370385365 1639237695336032938368407)
                      ·
                        rfl

theorem cell23_3192404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3192404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192404 prefixEnd_3192404 := by exact prefixLift 3192404
  have htrace : WordTrace (prefixWord ++ tailWord_3192404) baseStart_3192404 baseEnd_3192404 := by
    simpa [prefixWord, tailWord_3192404, baseEnd_3192404] using wordTrace_append hprefix tailTrace_3192404
  have hstable : (prefixWord ++ tailWord_3192404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192404).length < 2 ^ (prefixWord ++ tailWord_3192404).sum := by decide
  have hdescent : baseEnd_3192404 < baseStart_3192404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192431 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 2, 4, 2]
def baseStart_3192431 : Nat := 118140960795 + 3192431 * 2 ^ 59
def prefixEnd_3192431 : Nat := 4983230072969 + 3 ^ 40 * 3192431 * 2
def baseEnd_3192431 : Nat := 1639251559313704332730783

theorem tailTrace_3192431 : CollatzResearch.WordTrace tailWord_3192431 prefixEnd_3192431 1639251559313704332730783 := by
  unfold tailWord_3192431
  simp only [CollatzResearch.WordTrace]
  refine ⟨116437524297375185652425147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77625016198250123768283431 116437524297375185652425147)
  ·
    refine ⟨174656286446062778478637721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116437524297375185652425147 174656286446062778478637721)
    ·
      refine ⟨130992214834547083858978291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 174656286446062778478637721 130992214834547083858978291)
      ·
        refine ⟨196488322251820625788467437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 130992214834547083858978291 196488322251820625788467437)
        ·
          refine ⟨73683120844432734670675289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 196488322251820625788467437 73683120844432734670675289)
          ·
            refine ⟨55262340633324551003006467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73683120844432734670675289 55262340633324551003006467)
            ·
              refine ⟨82893510949986826504509701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55262340633324551003006467 82893510949986826504509701)
              ·
                refine ⟨15542533303122529969595569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82893510949986826504509701 15542533303122529969595569)
                ·
                  refine ⟨11656899977341897477196677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15542533303122529969595569 11656899977341897477196677)
                  ·
                    refine ⟨2185668745751605776974377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11656899977341897477196677 2185668745751605776974377)
                    ·
                      refine ⟨1639251559313704332730783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185668745751605776974377 1639251559313704332730783)
                      ·
                        rfl

theorem cell23_3192431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 4, 2].length) (baseStart_3192431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192431 prefixEnd_3192431 := by exact prefixLift 3192431
  have htrace : WordTrace (prefixWord ++ tailWord_3192431) baseStart_3192431 baseEnd_3192431 := by
    simpa [prefixWord, tailWord_3192431, baseEnd_3192431] using wordTrace_append hprefix tailTrace_3192431
  have hstable : (prefixWord ++ tailWord_3192431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192431).length < 2 ^ (prefixWord ++ tailWord_3192431).sum := by decide
  have hdescent : baseEnd_3192431 < baseStart_3192431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192441 : List Nat := [1, 2, 1, 3, 3, 1, 2, 3, 3, 4]
def baseStart_3192441 : Nat := 118140960795 + 3192441 * 2 ^ 59
def prefixEnd_3192441 : Nat := 4983230072969 + 3 ^ 40 * 3192441 * 2
def baseEnd_3192441 : Nat := 546418898040083097868579

theorem tailTrace_3192441 : CollatzResearch.WordTrace tailWord_3192441 prefixEnd_3192441 546418898040083097868579 := by
  unfold tailWord_3192441
  simp only [CollatzResearch.WordTrace]
  refine ⟨116437889027338957360289177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77625259351559304906859451 116437889027338957360289177)
  ·
    refine ⟨87328416770504218020216883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116437889027338957360289177 87328416770504218020216883)
    ·
      refine ⟨130992625155756327030325325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87328416770504218020216883 130992625155756327030325325)
      ·
        refine ⟨49122234433408622636371997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130992625155756327030325325 49122234433408622636371997)
        ·
          refine ⟨18420837912528233488639499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49122234433408622636371997 18420837912528233488639499)
          ·
            refine ⟨27631256868792350232959249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18420837912528233488639499 27631256868792350232959249)
            ·
              refine ⟨20723442651594262674719437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27631256868792350232959249 20723442651594262674719437)
              ·
                refine ⟨7771290994347848503019789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20723442651594262674719437 7771290994347848503019789)
                ·
                  refine ⟨2914234122880443188632421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7771290994347848503019789 2914234122880443188632421)
                  ·
                    refine ⟨546418898040083097868579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914234122880443188632421 546418898040083097868579)
                    ·
                      rfl

theorem cell23_3192441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 3, 4].length) (baseStart_3192441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192441 prefixEnd_3192441 := by exact prefixLift 3192441
  have htrace : WordTrace (prefixWord ++ tailWord_3192441) baseStart_3192441 baseEnd_3192441 := by
    simpa [prefixWord, tailWord_3192441, baseEnd_3192441] using wordTrace_append hprefix tailTrace_3192441
  have hstable : (prefixWord ++ tailWord_3192441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192441).length < 2 ^ (prefixWord ++ tailWord_3192441).sum := by decide
  have hdescent : baseEnd_3192441 < baseStart_3192441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192444 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3192444 : Nat := 118140960795 + 3192444 * 2 ^ 59
def prefixEnd_3192444 : Nat := 4983230072969 + 3 ^ 40 * 3192444 * 2
def baseEnd_3192444 : Nat := 1639258234562212781868223

theorem tailTrace_3192444 : CollatzResearch.WordTrace tailWord_3192444 prefixEnd_3192444 1639258234562212781868223 := by
  unfold tailWord_3192444
  simp only [CollatzResearch.WordTrace]
  refine ⟨58218999223164044436324193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77625332297552059248432257 58218999223164044436324193)
  ·
    refine ⟨43664249417373033327243145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58218999223164044436324193 43664249417373033327243145)
    ·
      refine ⟨32748187063029774995432359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43664249417373033327243145 32748187063029774995432359)
      ·
        refine ⟨49122280594544662493148539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32748187063029774995432359 49122280594544662493148539)
        ·
          refine ⟨73683420891816993739722809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49122280594544662493148539 73683420891816993739722809)
          ·
            refine ⟨55262565668862745304792107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73683420891816993739722809 55262565668862745304792107)
            ·
              refine ⟨82893848503294117957188161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55262565668862745304792107 82893848503294117957188161)
              ·
                refine ⟨62170386377470588467891121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 82893848503294117957188161 62170386377470588467891121)
                ·
                  refine ⟨46627789783102941350918341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62170386377470588467891121 46627789783102941350918341)
                  ·
                    refine ⟨8742710584331801503297189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46627789783102941350918341 8742710584331801503297189)
                    ·
                      refine ⟨1639258234562212781868223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8742710584331801503297189 1639258234562212781868223)
                      ·
                        rfl

theorem cell23_3192444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3192444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192444 prefixEnd_3192444 := by exact prefixLift 3192444
  have htrace : WordTrace (prefixWord ++ tailWord_3192444) baseStart_3192444 baseEnd_3192444 := by
    simpa [prefixWord, tailWord_3192444, baseEnd_3192444] using wordTrace_append hprefix tailTrace_3192444
  have hstable : (prefixWord ++ tailWord_3192444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192444).length < 2 ^ (prefixWord ++ tailWord_3192444).sum := by decide
  have hdescent : baseEnd_3192444 < baseStart_3192444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192458 : List Nat := [3, 1, 2, 3, 2, 2, 1, 2, 3, 4]
def baseStart_3192458 : Nat := 118140960795 + 3192458 * 2 ^ 59
def prefixEnd_3192458 : Nat := 4983230072969 + 3 ^ 40 * 3192458 * 2
def baseEnd_3192458 : Nat := 546421807763791909031053

theorem tailTrace_3192458 : CollatzResearch.WordTrace tailWord_3192458 prefixEnd_3192458 546421807763791909031053 := by
  unfold tailWord_3192458
  simp only [CollatzResearch.WordTrace]
  refine ⟨29109627267069342315914507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77625672712184912842438685 29109627267069342315914507)
  ·
    refine ⟨43664440900604013473871761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29109627267069342315914507 43664440900604013473871761)
    ·
      refine ⟨32748330675453010105403821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43664440900604013473871761 32748330675453010105403821)
      ·
        refine ⟨12280624003294878789526433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32748330675453010105403821 12280624003294878789526433)
        ·
          refine ⟨9210468002471159092144825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12280624003294878789526433 9210468002471159092144825)
          ·
            refine ⟨6907851001853369319108619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9210468002471159092144825 6907851001853369319108619)
            ·
              refine ⟨10361776502780053978662929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6907851001853369319108619 10361776502780053978662929)
              ·
                refine ⟨7771332377085040483997197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10361776502780053978662929 7771332377085040483997197)
                ·
                  refine ⟨2914249641406890181498949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7771332377085040483997197 2914249641406890181498949)
                  ·
                    refine ⟨546421807763791909031053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914249641406890181498949 546421807763791909031053)
                    ·
                      rfl

theorem cell23_3192458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3, 4].length) (baseStart_3192458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192458 prefixEnd_3192458 := by exact prefixLift 3192458
  have htrace : WordTrace (prefixWord ++ tailWord_3192458) baseStart_3192458 baseEnd_3192458 := by
    simpa [prefixWord, tailWord_3192458, baseEnd_3192458] using wordTrace_append hprefix tailTrace_3192458
  have hstable : (prefixWord ++ tailWord_3192458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192458).length < 2 ^ (prefixWord ++ tailWord_3192458).sum := by decide
  have hdescent : baseEnd_3192458 < baseStart_3192458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192498 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3]
def baseStart_3192498 : Nat := 118140960795 + 3192498 * 2 ^ 59
def prefixEnd_3192498 : Nat := 4983230072969 + 3 ^ 40 * 3192498 * 2
def baseEnd_3192498 : Nat := 1639285962517555570592975

theorem tailTrace_3192498 : CollatzResearch.WordTrace tailWord_3192498 prefixEnd_3192498 1639285962517555570592975 := by
  unfold tailWord_3192498
  simp only [CollatzResearch.WordTrace]
  refine ⟨29109991997033114023778537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77626645325421637396742765 29109991997033114023778537)
  ·
    refine ⟨21832493997774835517833903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29109991997033114023778537 21832493997774835517833903)
    ·
      refine ⟨32748740996662253276750855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21832493997774835517833903 32748740996662253276750855)
      ·
        refine ⟨49123111494993379915126283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32748740996662253276750855 49123111494993379915126283)
        ·
          refine ⟨73684667242490069872689425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49123111494993379915126283 73684667242490069872689425)
          ·
            refine ⟨55263500431867552404517069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73684667242490069872689425 55263500431867552404517069)
            ·
              refine ⟨20723812661950332151693901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55263500431867552404517069 20723812661950332151693901)
              ·
                refine ⟨7771429748231374556885213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20723812661950332151693901 7771429748231374556885213)
                ·
                  refine ⟨2914286155586765458831955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7771429748231374556885213 2914286155586765458831955)
                  ·
                    refine ⟨4371429233380148188247933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2914286155586765458831955 4371429233380148188247933)
                    ·
                      refine ⟨1639285962517555570592975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4371429233380148188247933 1639285962517555570592975)
                      ·
                        rfl

theorem cell23_3192498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_3192498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192498 prefixEnd_3192498 := by exact prefixLift 3192498
  have htrace : WordTrace (prefixWord ++ tailWord_3192498) baseStart_3192498 baseEnd_3192498 := by
    simpa [prefixWord, tailWord_3192498, baseEnd_3192498] using wordTrace_append hprefix tailTrace_3192498
  have hstable : (prefixWord ++ tailWord_3192498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192498).length < 2 ^ (prefixWord ++ tailWord_3192498).sum := by decide
  have hdescent : baseEnd_3192498 < baseStart_3192498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192508 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_3192508 : Nat := 118140960795 + 3192508 * 2 ^ 59
def prefixEnd_3192508 : Nat := 4983230072969 + 3 ^ 40 * 3192508 * 2
def baseEnd_3192508 : Nat := 1639291097324100531467929

theorem tailTrace_3192508 : CollatzResearch.WordTrace tailWord_3192508 prefixEnd_3192508 1639291097324100531467929 := by
  unfold tailWord_3192508
  simp only [CollatzResearch.WordTrace]
  refine ⟨58220166359048113901489089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77626888478730818535318785 58220166359048113901489089)
  ·
    refine ⟨43665124769286085426116817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58220166359048113901489089 43665124769286085426116817)
    ·
      refine ⟨32748843576964564069587613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43665124769286085426116817 32748843576964564069587613)
      ·
        refine ⟨12280816341361711526095355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32748843576964564069587613 12280816341361711526095355)
        ·
          refine ⟨18421224512042567289143033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12280816341361711526095355 18421224512042567289143033)
          ·
            refine ⟨13815918384031925466857275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18421224512042567289143033 13815918384031925466857275)
            ·
              refine ⟨20723877576047888200285913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13815918384031925466857275 20723877576047888200285913)
              ·
                refine ⟨15542908182035916150214435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20723877576047888200285913 15542908182035916150214435)
                ·
                  refine ⟨23314362273053874225321653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15542908182035916150214435 23314362273053874225321653)
                  ·
                    refine ⟨2185721463098800708623905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23314362273053874225321653 2185721463098800708623905)
                    ·
                      refine ⟨1639291097324100531467929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185721463098800708623905 1639291097324100531467929)
                      ·
                        rfl

theorem cell23_3192508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_3192508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192508 prefixEnd_3192508 := by exact prefixLift 3192508
  have htrace : WordTrace (prefixWord ++ tailWord_3192508) baseStart_3192508 baseEnd_3192508 := by
    simpa [prefixWord, tailWord_3192508, baseEnd_3192508] using wordTrace_append hprefix tailTrace_3192508
  have hstable : (prefixWord ++ tailWord_3192508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192508).length < 2 ^ (prefixWord ++ tailWord_3192508).sum := by decide
  have hdescent : baseEnd_3192508 < baseStart_3192508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192538 : List Nat := [3, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4]
def baseStart_3192538 : Nat := 118140960795 + 3192538 * 2 ^ 59
def prefixEnd_3192538 : Nat := 4983230072969 + 3 ^ 40 * 3192538 * 2
def baseEnd_3192538 : Nat := 1639306501743735414092791

theorem tailTrace_3192538 : CollatzResearch.WordTrace tailWord_3192538 prefixEnd_3192538 1639306501743735414092791 := by
  unfold tailWord_3192538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29110356726996885731642567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77627617938658361951046845 29110356726996885731642567)
  ·
    refine ⟨43665535090495328597463851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29110356726996885731642567 43665535090495328597463851)
    ·
      refine ⟨65498302635742992896195777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43665535090495328597463851 65498302635742992896195777)
      ·
        refine ⟨49123726976807244672146833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65498302635742992896195777 49123726976807244672146833)
        ·
          refine ⟨36842795232605433504110125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49123726976807244672146833 36842795232605433504110125)
          ·
            refine ⟨13816048212227037564041297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36842795232605433504110125 13816048212227037564041297)
            ·
              refine ⟨10362036159170278173030973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13816048212227037564041297 10362036159170278173030973)
              ·
                refine ⟨3885763559688854314886615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10362036159170278173030973 3885763559688854314886615)
                ·
                  refine ⟨5828645339533281472329923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3885763559688854314886615 5828645339533281472329923)
                  ·
                    refine ⟨8742968009299922208494885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5828645339533281472329923 8742968009299922208494885)
                    ·
                      refine ⟨1639306501743735414092791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8742968009299922208494885 1639306501743735414092791)
                      ·
                        rfl

theorem cell23_3192538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_3192538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192538 prefixEnd_3192538 := by exact prefixLift 3192538
  have htrace : WordTrace (prefixWord ++ tailWord_3192538) baseStart_3192538 baseEnd_3192538 := by
    simpa [prefixWord, tailWord_3192538, baseEnd_3192538] using wordTrace_append hprefix tailTrace_3192538
  have hstable : (prefixWord ++ tailWord_3192538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192538).length < 2 ^ (prefixWord ++ tailWord_3192538).sum := by decide
  have hdescent : baseEnd_3192538 < baseStart_3192538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192544 : List Nat := [2, 1, 1, 3, 1, 2, 13]
def baseStart_3192544 : Nat := 118140960795 + 3192544 * 2 ^ 59
def prefixEnd_3192544 : Nat := 4983230072969 + 3 ^ 40 * 3192544 * 2
def baseEnd_3192544 : Nat := 20238389908983486303923

theorem tailTrace_3192544 : CollatzResearch.WordTrace tailWord_3192544 prefixEnd_3192544 20238389908983486303923 := by
  unfold tailWord_3192544
  simp only [CollatzResearch.WordTrace]
  refine ⟨58220822872982902975644343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77627763830643870634192457 58220822872982902975644343)
  ·
    refine ⟨87331234309474354463466515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58220822872982902975644343 87331234309474354463466515)
    ·
      refine ⟨130996851464211531695199773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87331234309474354463466515 130996851464211531695199773)
      ·
        refine ⟨49123819299079324385699915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 130996851464211531695199773 49123819299079324385699915)
        ·
          refine ⟨73685728948618986578549873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49123819299079324385699915 73685728948618986578549873)
          ·
            refine ⟨55264296711464239933912405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73685728948618986578549873 55264296711464239933912405)
            ·
              refine ⟨20238389908983486303923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 55264296711464239933912405 20238389908983486303923)
              ·
                rfl

theorem cell23_3192544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 13].length) (baseStart_3192544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192544 prefixEnd_3192544 := by exact prefixLift 3192544
  have htrace : WordTrace (prefixWord ++ tailWord_3192544) baseStart_3192544 baseEnd_3192544 := by
    simpa [prefixWord, tailWord_3192544, baseEnd_3192544] using wordTrace_append hprefix tailTrace_3192544
  have hstable : (prefixWord ++ tailWord_3192544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192544).length < 2 ^ (prefixWord ++ tailWord_3192544).sum := by decide
  have hdescent : baseEnd_3192544 < baseStart_3192544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192548 : List Nat := [2, 3, 1, 1, 1, 3, 2, 4, 2, 4]
def baseStart_3192548 : Nat := 118140960795 + 3192548 * 2 ^ 59
def prefixEnd_3192548 : Nat := 4983230072969 + 3 ^ 40 * 3192548 * 2
def baseEnd_3192548 : Nat := 546437212183426791655915

theorem tailTrace_3192548 : CollatzResearch.WordTrace tailWord_3192548 prefixEnd_3192548 546437212183426791655915 := by
  unfold tailWord_3192548
  simp only [CollatzResearch.WordTrace]
  refine ⟨58220895818975657317217149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77627861091967543089622865 58220895818975657317217149)
  ·
    refine ⟨21832835932115871493956431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58220895818975657317217149 21832835932115871493956431)
    ·
      refine ⟨32749253898173807240934647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21832835932115871493956431 32749253898173807240934647)
      ·
        refine ⟨49123880847260710861401971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32749253898173807240934647 49123880847260710861401971)
        ·
          refine ⟨73685821270891066292102957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49123880847260710861401971 73685821270891066292102957)
          ·
            refine ⟨27632182976584149859538609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73685821270891066292102957 27632182976584149859538609)
            ·
              refine ⟨20724137232438112394653957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27632182976584149859538609 20724137232438112394653957)
              ·
                refine ⟨3885775731082146073997617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20724137232438112394653957 3885775731082146073997617)
                ·
                  refine ⟨2914331798311609555498213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885775731082146073997617 2914331798311609555498213)
                  ·
                    refine ⟨546437212183426791655915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2914331798311609555498213 546437212183426791655915)
                    ·
                      rfl

theorem cell23_3192548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2, 4].length) (baseStart_3192548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192548 prefixEnd_3192548 := by exact prefixLift 3192548
  have htrace : WordTrace (prefixWord ++ tailWord_3192548) baseStart_3192548 baseEnd_3192548 := by
    simpa [prefixWord, tailWord_3192548, baseEnd_3192548] using wordTrace_append hprefix tailTrace_3192548
  have hstable : (prefixWord ++ tailWord_3192548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192548).length < 2 ^ (prefixWord ++ tailWord_3192548).sum := by decide
  have hdescent : baseEnd_3192548 < baseStart_3192548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192555 : List Nat := [1, 1, 1, 1, 2, 4, 5, 1, 3, 2, 2]
def baseStart_3192555 : Nat := 118140960795 + 3192555 * 2 ^ 59
def prefixEnd_3192555 : Nat := 4983230072969 + 3 ^ 40 * 3192555 * 2
def baseEnd_3192555 : Nat := 1639315230914861847580213

theorem tailTrace_3192555 : CollatzResearch.WordTrace tailWord_3192555 prefixEnd_3192555 1639315230914861847580213 := by
  unfold tailWord_3192555
  simp only [CollatzResearch.WordTrace]
  refine ⟨116442046948925954829939119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77628031299283969886626079 116442046948925954829939119)
  ·
    refine ⟨174663070423388932244908679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116442046948925954829939119 174663070423388932244908679)
    ·
      refine ⟨261994605635083398367363019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174663070423388932244908679 261994605635083398367363019)
      ·
        refine ⟨392991908452625097551044529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261994605635083398367363019 392991908452625097551044529)
        ·
          refine ⟨294743931339468823163283397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392991908452625097551044529 294743931339468823163283397)
          ·
            refine ⟨55264487126150404343115637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 294743931339468823163283397 55264487126150404343115637)
            ·
              refine ⟨5181045668076600407167091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55264487126150404343115637 5181045668076600407167091)
              ·
                refine ⟨7771568502114900610750637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181045668076600407167091 7771568502114900610750637)
                ·
                  refine ⟨2914338188293087729031489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7771568502114900610750637 2914338188293087729031489)
                  ·
                    refine ⟨2185753641219815796773617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914338188293087729031489 2185753641219815796773617)
                    ·
                      refine ⟨1639315230914861847580213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185753641219815796773617 1639315230914861847580213)
                      ·
                        rfl

theorem cell23_3192555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 2, 2].length) (baseStart_3192555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192555 prefixEnd_3192555 := by exact prefixLift 3192555
  have htrace : WordTrace (prefixWord ++ tailWord_3192555) baseStart_3192555 baseEnd_3192555 := by
    simpa [prefixWord, tailWord_3192555, baseEnd_3192555] using wordTrace_append hprefix tailTrace_3192555
  have hstable : (prefixWord ++ tailWord_3192555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192555).length < 2 ^ (prefixWord ++ tailWord_3192555).sum := by decide
  have hdescent : baseEnd_3192555 < baseStart_3192555 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192558 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3]
def baseStart_3192558 : Nat := 118140960795 + 3192558 * 2 ^ 59
def prefixEnd_3192558 : Nat := 4983230072969 + 3 ^ 40 * 3192558 * 2
def baseEnd_3192558 : Nat := 1639316771356825335842699

theorem tailTrace_3192558 : CollatzResearch.WordTrace tailWord_3192558 prefixEnd_3192558 1639316771356825335842699 := by
  unfold tailWord_3192558
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555269545989385792787291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77628104245276724228198885 14555269545989385792787291)
  ·
    refine ⟨21832904318984078689180937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14555269545989385792787291 21832904318984078689180937)
    ·
      refine ⟨16374678239238059016885703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21832904318984078689180937 16374678239238059016885703)
      ·
        refine ⟨24562017358857088525328555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16374678239238059016885703 24562017358857088525328555)
        ·
          refine ⟨36843026038285632787992833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24562017358857088525328555 36843026038285632787992833)
          ·
            refine ⟨27632269528714224590994625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36843026038285632787992833 27632269528714224590994625)
            ·
              refine ⟨20724202146535668443245969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27632269528714224590994625 20724202146535668443245969)
              ·
                refine ⟨15543151609901751332434477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20724202146535668443245969 15543151609901751332434477)
                ·
                  refine ⟨5828681853713156749662929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15543151609901751332434477 5828681853713156749662929)
                  ·
                    refine ⟨4371511390284867562247197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5828681853713156749662929 4371511390284867562247197)
                    ·
                      refine ⟨1639316771356825335842699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4371511390284867562247197 1639316771356825335842699)
                      ·
                        rfl

theorem cell23_3192558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_3192558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192558 prefixEnd_3192558 := by exact prefixLift 3192558
  have htrace : WordTrace (prefixWord ++ tailWord_3192558) baseStart_3192558 baseEnd_3192558 := by
    simpa [prefixWord, tailWord_3192558, baseEnd_3192558] using wordTrace_append hprefix tailTrace_3192558
  have hstable : (prefixWord ++ tailWord_3192558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192558).length < 2 ^ (prefixWord ++ tailWord_3192558).sum := by decide
  have hdescent : baseEnd_3192558 < baseStart_3192558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192561 : List Nat := [1, 2, 2, 2, 2, 4, 2, 8]
def baseStart_3192561 : Nat := 118140960795 + 3192561 * 2 ^ 59
def prefixEnd_3192561 : Nat := 4983230072969 + 3 ^ 40 * 3192561 * 2
def baseEnd_3192561 : Nat := 60715493029584771263155

theorem tailTrace_3192561 : CollatzResearch.WordTrace tailWord_3192561 prefixEnd_3192561 60715493029584771263155 := by
  unfold tailWord_3192561
  simp only [CollatzResearch.WordTrace]
  refine ⟨116442265786904217854657537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77628177191269478569771691 116442265786904217854657537)
  ·
    refine ⟨87331699340178163390993153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116442265786904217854657537 87331699340178163390993153)
    ·
      refine ⟨65498774505133622543244865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87331699340178163390993153 65498774505133622543244865)
      ·
        refine ⟨49124080878850216907433649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65498774505133622543244865 49124080878850216907433649)
        ·
          refine ⟨36843060659137662680575237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49124080878850216907433649 36843060659137662680575237)
          ·
            refine ⟨6908073873588311752607857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36843060659137662680575237 6908073873588311752607857)
            ·
              refine ⟨5181055405191233814455893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6908073873588311752607857 5181055405191233814455893)
              ·
                refine ⟨60715493029584771263155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5181055405191233814455893 60715493029584771263155)
                ·
                  rfl

theorem cell23_3192561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 8].length) (baseStart_3192561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192561 prefixEnd_3192561 := by exact prefixLift 3192561
  have htrace : WordTrace (prefixWord ++ tailWord_3192561) baseStart_3192561 baseEnd_3192561 := by
    simpa [prefixWord, tailWord_3192561, baseEnd_3192561] using wordTrace_append hprefix tailTrace_3192561
  have hstable : (prefixWord ++ tailWord_3192561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192561).length < 2 ^ (prefixWord ++ tailWord_3192561).sum := by decide
  have hdescent : baseEnd_3192561 < baseStart_3192561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192588 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 6, 1, 3]
def baseStart_3192588 : Nat := 118140960795 + 3192588 * 2 ^ 59
def prefixEnd_3192588 : Nat := 4983230072969 + 3 ^ 40 * 3192588 * 2
def baseEnd_3192588 : Nat := 1639332175776460218467561

theorem tailTrace_3192588 : CollatzResearch.WordTrace tailWord_3192588 prefixEnd_3192588 1639332175776460218467561 := by
  unfold tailWord_3192588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58221625278903200732945209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77628833705204267643926945 58221625278903200732945209)
  ·
    refine ⟨43666218959177400549708907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58221625278903200732945209 43666218959177400549708907)
    ·
      refine ⟨65499328438766100824563361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43666218959177400549708907 65499328438766100824563361)
      ·
        refine ⟨49124496329074575618422521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65499328438766100824563361 49124496329074575618422521)
        ·
          refine ⟨36843372246805931713816891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49124496329074575618422521 36843372246805931713816891)
          ·
            refine ⟨55265058370208897570725337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36843372246805931713816891 55265058370208897570725337)
            ·
              refine ⟨41448793777656673178044003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55265058370208897570725337 41448793777656673178044003)
              ·
                refine ⟨62173190666485009767066005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41448793777656673178044003 62173190666485009767066005)
                ·
                  refine ⟨2914368312491484832831219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62173190666485009767066005 2914368312491484832831219)
                  ·
                    refine ⟨4371552468737227249246829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2914368312491484832831219 4371552468737227249246829)
                    ·
                      refine ⟨1639332175776460218467561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4371552468737227249246829 1639332175776460218467561)
                      ·
                        rfl

theorem cell23_3192588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_3192588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192588 prefixEnd_3192588 := by exact prefixLift 3192588
  have htrace : WordTrace (prefixWord ++ tailWord_3192588) baseStart_3192588 baseEnd_3192588 := by
    simpa [prefixWord, tailWord_3192588, baseEnd_3192588] using wordTrace_append hprefix tailTrace_3192588
  have hstable : (prefixWord ++ tailWord_3192588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192588).length < 2 ^ (prefixWord ++ tailWord_3192588).sum := by decide
  have hdescent : baseEnd_3192588 < baseStart_3192588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192611 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4]
def baseStart_3192611 : Nat := 118140960795 + 3192611 * 2 ^ 59
def prefixEnd_3192611 : Nat := 4983230072969 + 3 ^ 40 * 3192611 * 2
def baseEnd_3192611 : Nat := 1639343985831513628479955

theorem tailTrace_3192611 : CollatzResearch.WordTrace tailWord_3192611 prefixEnd_3192611 1639343985831513628479955 := by
  unfold tailWord_3192611
  simp only [CollatzResearch.WordTrace]
  refine ⟨116444089436723076393977687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77629392957815384262651791 116444089436723076393977687)
  ·
    refine ⟨174666134155084614590966531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116444089436723076393977687 174666134155084614590966531)
    ·
      refine ⟨261999201232626921886449797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 174666134155084614590966531 261999201232626921886449797)
      ·
        refine ⟨49124850231117547853709337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 261999201232626921886449797 49124850231117547853709337)
        ·
          refine ⟨36843637673338160890282003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49124850231117547853709337 36843637673338160890282003)
          ·
            refine ⟨55265456510007241335423005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36843637673338160890282003 55265456510007241335423005)
            ·
              refine ⟨20724546191252715500783627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55265456510007241335423005 20724546191252715500783627)
              ·
                refine ⟨31086819286879073251175441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20724546191252715500783627 31086819286879073251175441)
                ·
                  refine ⟨23315114465159304938381581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31086819286879073251175441 23315114465159304938381581)
                  ·
                    refine ⟨8743167924434739351893093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23315114465159304938381581 8743167924434739351893093)
                    ·
                      refine ⟨1639343985831513628479955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8743167924434739351893093 1639343985831513628479955)
                      ·
                        rfl

theorem cell23_3192611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_3192611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192611 prefixEnd_3192611 := by exact prefixLift 3192611
  have htrace : WordTrace (prefixWord ++ tailWord_3192611) baseStart_3192611 baseEnd_3192611 := by
    simpa [prefixWord, tailWord_3192611, baseEnd_3192611] using wordTrace_append hprefix tailTrace_3192611
  have hstable : (prefixWord ++ tailWord_3192611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192611).length < 2 ^ (prefixWord ++ tailWord_3192611).sum := by decide
  have hdescent : baseEnd_3192611 < baseStart_3192611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192622 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3]
def baseStart_3192622 : Nat := 118140960795 + 3192622 * 2 ^ 59
def prefixEnd_3192622 : Nat := 4983230072969 + 3 ^ 40 * 3192622 * 2
def baseEnd_3192622 : Nat := 1639349634118713085442405

theorem tailTrace_3192622 : CollatzResearch.WordTrace tailWord_3192622 prefixEnd_3192622 1639349634118713085442405 := by
  unfold tailWord_3192622
  simp only [CollatzResearch.WordTrace]
  refine ⟨14555561329960403159078515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77629660426455483515085413 14555561329960403159078515)
  ·
    refine ⟨21833341994940604738617773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14555561329960403159078515 21833341994940604738617773)
    ·
      refine ⟨8187503248102726776981665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21833341994940604738617773 8187503248102726776981665)
      ·
        refine ⟨6140627436077045082736249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8187503248102726776981665 6140627436077045082736249)
        ·
          refine ⟨4605470577057783812052187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6140627436077045082736249 4605470577057783812052187)
          ·
            refine ⟨6908205865586675718078281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4605470577057783812052187 6908205865586675718078281)
            ·
              refine ⟨5181154399190006788558711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6908205865586675718078281 5181154399190006788558711)
              ·
                refine ⟨7771731598785010182838067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5181154399190006788558711 7771731598785010182838067)
                ·
                  refine ⟨11657597398177515274257101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7771731598785010182838067 11657597398177515274257101)
                  ·
                    refine ⟨4371599024316568227846413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11657597398177515274257101 4371599024316568227846413)
                    ·
                      refine ⟨1639349634118713085442405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4371599024316568227846413 1639349634118713085442405)
                      ·
                        rfl

theorem cell23_3192622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_3192622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192622 prefixEnd_3192622 := by exact prefixLift 3192622
  have htrace : WordTrace (prefixWord ++ tailWord_3192622) baseStart_3192622 baseEnd_3192622 := by
    simpa [prefixWord, tailWord_3192622, baseEnd_3192622] using wordTrace_append hprefix tailTrace_3192622
  have hstable : (prefixWord ++ tailWord_3192622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192622).length < 2 ^ (prefixWord ++ tailWord_3192622).sum := by decide
  have hdescent : baseEnd_3192622 < baseStart_3192622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192631 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 5]
def baseStart_3192631 : Nat := 118140960795 + 3192631 * 2 ^ 59
def prefixEnd_3192631 : Nat := 4983230072969 + 3 ^ 40 * 3192631 * 2
def baseEnd_3192631 : Nat := 1639354255444603550229863

theorem tailTrace_3192631 : CollatzResearch.WordTrace tailWord_3192631 prefixEnd_3192631 1639354255444603550229863 := by
  unfold tailWord_3192631
  simp only [CollatzResearch.WordTrace]
  refine ⟨116444818896650619809705747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77629879264433746539803831 116444818896650619809705747)
  ·
    refine ⟨174667228344975929714558621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116444818896650619809705747 174667228344975929714558621)
    ·
      refine ⟨65500210629365973642959483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 174667228344975929714558621 65500210629365973642959483)
      ·
        refine ⟨98250315944048960464439225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65500210629365973642959483 98250315944048960464439225)
        ·
          refine ⟨73687736958036720348329419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98250315944048960464439225 73687736958036720348329419)
          ·
            refine ⟨110531605437055080522494129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73687736958036720348329419 110531605437055080522494129)
            ·
              refine ⟨82898704077791310391870597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110531605437055080522494129 82898704077791310391870597)
              ·
                refine ⟨15543507014585870698475737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 82898704077791310391870597 15543507014585870698475737)
                ·
                  refine ⟨11657630260939403023856803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15543507014585870698475737 11657630260939403023856803)
                  ·
                    refine ⟨17486445391409104535785205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11657630260939403023856803 17486445391409104535785205)
                    ·
                      refine ⟨1639354255444603550229863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17486445391409104535785205 1639354255444603550229863)
                      ·
                        rfl

theorem cell23_3192631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 2, 1, 5].length) (baseStart_3192631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192631 prefixEnd_3192631 := by exact prefixLift 3192631
  have htrace : WordTrace (prefixWord ++ tailWord_3192631) baseStart_3192631 baseEnd_3192631 := by
    simpa [prefixWord, tailWord_3192631, baseEnd_3192631] using wordTrace_append hprefix tailTrace_3192631
  have hstable : (prefixWord ++ tailWord_3192631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192631).length < 2 ^ (prefixWord ++ tailWord_3192631).sum := by decide
  have hdescent : baseEnd_3192631 < baseStart_3192631 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192645 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 4, 2, 2]
def baseStart_3192645 : Nat := 118140960795 + 3192645 * 2 ^ 59
def prefixEnd_3192645 : Nat := 4983230072969 + 3 ^ 40 * 3192645 * 2
def baseEnd_3192645 : Nat := 1639361444173766495454799

theorem tailTrace_3192645 : CollatzResearch.WordTrace tailWord_3192645 prefixEnd_3192645 1639361444173766495454799 := by
  unfold tailWord_3192645
  simp only [CollatzResearch.WordTrace]
  refine ⟨116445329518599900200715389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77630219679066600133810259 116445329518599900200715389)
  ·
    refine ⟨43666998569474962575268271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116445329518599900200715389 43666998569474962575268271)
    ·
      refine ⟨65500497854212443862902407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43666998569474962575268271 65500497854212443862902407)
      ·
        refine ⟨98250746781318665794353611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65500497854212443862902407 98250746781318665794353611)
        ·
          refine ⟨147376120171977998691530417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98250746781318665794353611 147376120171977998691530417)
          ·
            refine ⟨110532090128983499018647813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147376120171977998691530417 110532090128983499018647813)
            ·
              refine ⟨20724766899184406065996465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110532090128983499018647813 20724766899184406065996465)
              ·
                refine ⟨15543575174388304549497349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20724766899184406065996465 15543575174388304549497349)
                ·
                  refine ⟨2914420345197807103030753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15543575174388304549497349 2914420345197807103030753)
                  ·
                    refine ⟨2185815258898355327273065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914420345197807103030753 2185815258898355327273065)
                    ·
                      refine ⟨1639361444173766495454799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185815258898355327273065 1639361444173766495454799)
                      ·
                        rfl

theorem cell23_3192645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 4, 2, 2].length) (baseStart_3192645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192645 prefixEnd_3192645 := by exact prefixLift 3192645
  have htrace : WordTrace (prefixWord ++ tailWord_3192645) baseStart_3192645 baseEnd_3192645 := by
    simpa [prefixWord, tailWord_3192645, baseEnd_3192645] using wordTrace_append hprefix tailTrace_3192645
  have hstable : (prefixWord ++ tailWord_3192645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192645).length < 2 ^ (prefixWord ++ tailWord_3192645).sum := by decide
  have hdescent : baseEnd_3192645 < baseStart_3192645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192658 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3192658 : Nat := 118140960795 + 3192658 * 2 ^ 59
def prefixEnd_3192658 : Nat := 4983230072969 + 3 ^ 40 * 3192658 * 2
def baseEnd_3192658 : Nat := 1639368119422274944592239

theorem tailTrace_3192658 : CollatzResearch.WordTrace tailWord_3192658 prefixEnd_3192658 1639368119422274944592239 := by
  unfold tailWord_3192658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29111450916888200855234657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77630535778368535613959085 29111450916888200855234657)
  ·
    refine ⟨21833588187666150641425993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29111450916888200855234657 21833588187666150641425993)
    ·
      refine ⟨16375191140749612981069495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21833588187666150641425993 16375191140749612981069495)
      ·
        refine ⟨24562786711124419471604243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16375191140749612981069495 24562786711124419471604243)
        ·
          refine ⟨36844180066686629207406365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24562786711124419471604243 36844180066686629207406365)
          ·
            refine ⟨13816567525007485952777387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36844180066686629207406365 13816567525007485952777387)
            ·
              refine ⟨20724851287511228929166081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13816567525007485952777387 20724851287511228929166081)
              ·
                refine ⟨15543638465633421696874561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20724851287511228929166081 15543638465633421696874561)
                ·
                  refine ⟨11657728849225066272655921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15543638465633421696874561 11657728849225066272655921)
                  ·
                    refine ⟨8743296636918799704491941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11657728849225066272655921 8743296636918799704491941)
                    ·
                      refine ⟨1639368119422274944592239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8743296636918799704491941 1639368119422274944592239)
                      ·
                        rfl

theorem cell23_3192658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3192658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192658 prefixEnd_3192658 := by exact prefixLift 3192658
  have htrace : WordTrace (prefixWord ++ tailWord_3192658) baseStart_3192658 baseEnd_3192658 := by
    simpa [prefixWord, tailWord_3192658, baseEnd_3192658] using wordTrace_append hprefix tailTrace_3192658
  have hstable : (prefixWord ++ tailWord_3192658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192658).length < 2 ^ (prefixWord ++ tailWord_3192658).sum := by decide
  have hdescent : baseEnd_3192658 < baseStart_3192658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3192679 : List Nat := [1, 1, 5, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_3192679 : Nat := 118140960795 + 3192679 * 2 ^ 59
def prefixEnd_3192679 : Nat := 4983230072969 + 3 ^ 40 * 3192679 * 2
def baseEnd_3192679 : Nat := 1639378902516019362429643

theorem tailTrace_3192679 : CollatzResearch.WordTrace tailWord_3192679 prefixEnd_3192679 1639378902516019362429643 := by
  unfold tailWord_3192679
  simp only [CollatzResearch.WordTrace]
  refine ⟨116446569600476724007453091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77631046400317816004968727 116446569600476724007453091)
  ·
    refine ⟨174669854400715086011179637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116446569600476724007453091 174669854400715086011179637)
    ·
      refine ⟨16375298850067039313548091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 174669854400715086011179637 16375298850067039313548091)
      ·
        refine ⟨24562948275100558970322137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16375298850067039313548091 24562948275100558970322137)
        ·
          refine ⟨18422211206325419227741603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24562948275100558970322137 18422211206325419227741603)
          ·
            refine ⟨27633316809488128841612405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18422211206325419227741603 27633316809488128841612405)
            ·
              refine ⟨2590623450889512078901163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27633316809488128841612405 2590623450889512078901163)
              ·
                refine ⟨3885935176334268118351745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2590623450889512078901163 3885935176334268118351745)
                ·
                  refine ⟨2914451382250701088763809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3885935176334268118351745 2914451382250701088763809)
                  ·
                    refine ⟨2185838536688025816572857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2914451382250701088763809 2185838536688025816572857)
                    ·
                      refine ⟨1639378902516019362429643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2185838536688025816572857 1639378902516019362429643)
                      ·
                        rfl

theorem cell23_3192679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_3192679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3192679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3192679 prefixEnd_3192679 := by exact prefixLift 3192679
  have htrace : WordTrace (prefixWord ++ tailWord_3192679) baseStart_3192679 baseEnd_3192679 := by
    simpa [prefixWord, tailWord_3192679, baseEnd_3192679] using wordTrace_append hprefix tailTrace_3192679
  have hstable : (prefixWord ++ tailWord_3192679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3192679).length < 2 ^ (prefixWord ++ tailWord_3192679).sum := by decide
  have hdescent : baseEnd_3192679 < baseStart_3192679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3192679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
