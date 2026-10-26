import V185TrunkScan23Chunk1298

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7693043 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 3]
def baseStart_7693043 : Nat := 118140960795 + 7693043 * 2 ^ 59
def prefixEnd_7693043 : Nat := 4983230072969 + 3 ^ 40 * 7693043 * 2
def baseEnd_7693043 : Nat := 3950228754706649667582845

theorem tailTrace_7693043 : CollatzResearch.WordTrace tailWord_7693043 prefixEnd_7693043 3950228754706649667582845 := by
  unfold tailWord_7693043
  simp only [CollatzResearch.WordTrace]
  refine ⟨280588329468426552987203783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187058886312284368658135855 280588329468426552987203783)
  ·
    refine ⟨420882494202639829480805675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280588329468426552987203783 420882494202639829480805675)
    ·
      refine ⟨631323741303959744221208513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420882494202639829480805675 631323741303959744221208513)
      ·
        refine ⟨473492805977969808165906385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631323741303959744221208513 473492805977969808165906385)
        ·
          refine ⟨355119604483477356124429789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473492805977969808165906385 355119604483477356124429789)
          ·
            refine ⟨133169851681304008546661171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355119604483477356124429789 133169851681304008546661171)
            ·
              refine ⟨199754777521956012819991757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133169851681304008546661171 199754777521956012819991757)
              ·
                refine ⟨74908041570733504807496909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199754777521956012819991757 74908041570733504807496909)
                ·
                  refine ⟨28090515589025064302811341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74908041570733504807496909 28090515589025064302811341)
                  ·
                    refine ⟨10533943345884399113554253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28090515589025064302811341 10533943345884399113554253)
                    ·
                      refine ⟨3950228754706649667582845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10533943345884399113554253 3950228754706649667582845)
                      ·
                        rfl

theorem cell23_7693043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_7693043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693043 prefixEnd_7693043 := by exact prefixLift 7693043
  have htrace : WordTrace (prefixWord ++ tailWord_7693043) baseStart_7693043 baseEnd_7693043 := by
    simpa [prefixWord, tailWord_7693043, baseEnd_7693043] using wordTrace_append hprefix tailTrace_7693043
  have hstable : (prefixWord ++ tailWord_7693043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693043).length < 2 ^ (prefixWord ++ tailWord_7693043).sum := by decide
  have hdescent : baseEnd_7693043 < baseStart_7693043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693070 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_7693070 : Nat := 118140960795 + 7693070 * 2 ^ 59
def prefixEnd_7693070 : Nat := 4983230072969 + 3 ^ 40 * 7693070 * 2
def baseEnd_7693070 : Nat := 3950242618684321061945221

theorem tailTrace_7693070 : CollatzResearch.WordTrace tailWord_7693070 prefixEnd_7693070 3950242618684321061945221 := by
  unfold tailWord_7693070
  simp only [CollatzResearch.WordTrace]
  refine ⟨35073664279916092074804583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187059542826219157732291109 35073664279916092074804583)
  ·
    refine ⟨52610496419874138112206875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35073664279916092074804583 52610496419874138112206875)
    ·
      refine ⟨78915744629811207168310313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52610496419874138112206875 78915744629811207168310313)
      ·
        refine ⟨59186808472358405376232735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78915744629811207168310313 59186808472358405376232735)
        ·
          refine ⟨88780212708537608064349103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59186808472358405376232735 88780212708537608064349103)
          ·
            refine ⟨133170319062806412096523655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88780212708537608064349103 133170319062806412096523655)
            ·
              refine ⟨199755478594209618144785483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133170319062806412096523655 199755478594209618144785483)
              ·
                refine ⟨299633217891314427217178225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199755478594209618144785483 299633217891314427217178225)
                ·
                  refine ⟨224724913418485820412883669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299633217891314427217178225 224724913418485820412883669)
                  ·
                    refine ⟨5266990158245761415926961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 224724913418485820412883669 5266990158245761415926961)
                    ·
                      refine ⟨3950242618684321061945221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5266990158245761415926961 3950242618684321061945221)
                      ·
                        rfl

theorem cell23_7693070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_7693070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693070 prefixEnd_7693070 := by exact prefixLift 7693070
  have htrace : WordTrace (prefixWord ++ tailWord_7693070) baseStart_7693070 baseEnd_7693070 := by
    simpa [prefixWord, tailWord_7693070, baseEnd_7693070] using wordTrace_append hprefix tailTrace_7693070
  have hstable : (prefixWord ++ tailWord_7693070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693070).length < 2 ^ (prefixWord ++ tailWord_7693070).sum := by decide
  have hdescent : baseEnd_7693070 < baseStart_7693070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693077 : List Nat := [1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_7693077 : Nat := 118140960795 + 7693077 * 2 ^ 59
def prefixEnd_7693077 : Nat := 4983230072969 + 3 ^ 40 * 7693077 * 2
def baseEnd_7693077 : Nat := 3950246213048902534557689

theorem tailTrace_7693077 : CollatzResearch.WordTrace tailWord_7693077 prefixEnd_7693077 3950246213048902534557689 := by
  unfold tailWord_7693077
  simp only [CollatzResearch.WordTrace]
  refine ⟨280589569550303376793941485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187059713033535584529294323 280589569550303376793941485)
  ·
    refine ⟨105221088581363766297728057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280589569550303376793941485 105221088581363766297728057)
    ·
      refine ⟨78915816436022824723296043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105221088581363766297728057 78915816436022824723296043)
      ·
        refine ⟨118373724654034237084944065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78915816436022824723296043 118373724654034237084944065)
        ·
          refine ⟨88780293490525677813708049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118373724654034237084944065 88780293490525677813708049)
          ·
            refine ⟨66585220117894258360281037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88780293490525677813708049 66585220117894258360281037)
            ·
              refine ⟨24969457544210346885105389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66585220117894258360281037 24969457544210346885105389)
              ·
                refine ⟨9363546579078880081914521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24969457544210346885105389 9363546579078880081914521)
                ·
                  refine ⟨7022659934309160061435891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9363546579078880081914521 7022659934309160061435891)
                  ·
                    refine ⟨10533989901463740092153837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7022659934309160061435891 10533989901463740092153837)
                    ·
                      refine ⟨3950246213048902534557689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10533989901463740092153837 3950246213048902534557689)
                      ·
                        rfl

theorem cell23_7693077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_7693077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693077 prefixEnd_7693077 := by exact prefixLift 7693077
  have htrace : WordTrace (prefixWord ++ tailWord_7693077) baseStart_7693077 baseEnd_7693077 := by
    simpa [prefixWord, tailWord_7693077, baseEnd_7693077] using wordTrace_append hprefix tailTrace_7693077
  have hstable : (prefixWord ++ tailWord_7693077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693077).length < 2 ^ (prefixWord ++ tailWord_7693077).sum := by decide
  have hdescent : baseEnd_7693077 < baseStart_7693077 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693087 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 3, 3, 2]
def baseStart_7693087 : Nat := 118140960795 + 7693087 * 2 ^ 59
def prefixEnd_7693087 : Nat := 4983230072969 + 3 ^ 40 * 7693087 * 2
def baseEnd_7693087 : Nat := 3950251347855447495432643

theorem tailTrace_7693087 : CollatzResearch.WordTrace tailWord_7693087 prefixEnd_7693087 3950251347855447495432643 := by
  unfold tailWord_7693087
  simp only [CollatzResearch.WordTrace]
  refine ⟨280589934280267148501805515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187059956186844765667870343 280589934280267148501805515)
  ·
    refine ⟨420884901420400722752708273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280589934280267148501805515 420884901420400722752708273)
    ·
      refine ⟨315663676065300542064531205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420884901420400722752708273 315663676065300542064531205)
      ·
        refine ⟨59186939262243851637099601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315663676065300542064531205 59186939262243851637099601)
        ·
          refine ⟨44390204446682888727824701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59186939262243851637099601 44390204446682888727824701)
          ·
            refine ⟨16646326667506083272934263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44390204446682888727824701 16646326667506083272934263)
            ·
              refine ⟨24969490001259124909401395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16646326667506083272934263 24969490001259124909401395)
              ·
                refine ⟨37454235001888687364102093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24969490001259124909401395 37454235001888687364102093)
                ·
                  refine ⟨14045338125708257761538285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37454235001888687364102093 14045338125708257761538285)
                  ·
                    refine ⟨5267001797140596660576857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14045338125708257761538285 5267001797140596660576857)
                    ·
                      refine ⟨3950251347855447495432643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267001797140596660576857 3950251347855447495432643)
                      ·
                        rfl

theorem cell23_7693087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_7693087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693087 prefixEnd_7693087 := by exact prefixLift 7693087
  have htrace : WordTrace (prefixWord ++ tailWord_7693087) baseStart_7693087 baseEnd_7693087 := by
    simpa [prefixWord, tailWord_7693087, baseEnd_7693087] using wordTrace_append hprefix tailTrace_7693087
  have hstable : (prefixWord ++ tailWord_7693087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693087).length < 2 ^ (prefixWord ++ tailWord_7693087).sum := by decide
  have hdescent : baseEnd_7693087 < baseStart_7693087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693103 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_7693103 : Nat := 118140960795 + 7693103 * 2 ^ 59
def prefixEnd_7693103 : Nat := 4983230072969 + 3 ^ 40 * 7693103 * 2
def baseEnd_7693103 : Nat := 3950259563545919432832569

theorem tailTrace_7693103 : CollatzResearch.WordTrace tailWord_7693103 prefixEnd_7693103 3950259563545919432832569 := by
  unfold tailWord_7693103
  simp only [CollatzResearch.WordTrace]
  refine ⟨280590517848209183234387963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187060345232139455489591975 280590517848209183234387963)
  ·
    refine ⟨420885776772313774851581945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280590517848209183234387963 420885776772313774851581945)
    ·
      refine ⟨315664332579235331138686459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420885776772313774851581945 315664332579235331138686459)
      ·
        refine ⟨473496498868852996708029689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315664332579235331138686459 473496498868852996708029689)
        ·
          refine ⟨355122374151639747531022267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473496498868852996708029689 355122374151639747531022267)
          ·
            refine ⟨532683561227459621296533401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355122374151639747531022267 532683561227459621296533401)
            ·
              refine ⟨399512670920594715972400051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532683561227459621296533401 399512670920594715972400051)
              ·
                refine ⟨599269006380892073958600077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399512670920594715972400051 599269006380892073958600077)
                ·
                  refine ⟨224725877392834527734475029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599269006380892073958600077 224725877392834527734475029)
                  ·
                    refine ⟨10534025502789118487553517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 224725877392834527734475029 10534025502789118487553517)
                    ·
                      refine ⟨3950259563545919432832569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534025502789118487553517 3950259563545919432832569)
                      ·
                        rfl

theorem cell23_7693103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_7693103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693103 prefixEnd_7693103 := by exact prefixLift 7693103
  have htrace : WordTrace (prefixWord ++ tailWord_7693103) baseStart_7693103 baseEnd_7693103 := by
    simpa [prefixWord, tailWord_7693103, baseEnd_7693103] using wordTrace_append hprefix tailTrace_7693103
  have hstable : (prefixWord ++ tailWord_7693103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693103).length < 2 ^ (prefixWord ++ tailWord_7693103).sum := by decide
  have hdescent : baseEnd_7693103 < baseStart_7693103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693123 : List Nat := [1, 1, 1, 3, 1, 4, 2, 3, 7]
def baseStart_7693123 : Nat := 118140960795 + 7693123 * 2 ^ 59
def prefixEnd_7693123 : Nat := 4983230072969 + 3 ^ 40 * 7693123 * 2
def baseEnd_7693123 : Nat := 438918870351001039398053

theorem tailTrace_7693123 : CollatzResearch.WordTrace tailWord_7693123 prefixEnd_7693123 438918870351001039398053 := by
  unfold tailWord_7693123
  simp only [CollatzResearch.WordTrace]
  refine ⟨280591247308136726650116023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187060831538757817766744015 280591247308136726650116023)
  ·
    refine ⟨420886870962205089975174035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280591247308136726650116023 420886870962205089975174035)
    ·
      refine ⟨631330306443307634962761053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420886870962205089975174035 631330306443307634962761053)
      ·
        refine ⟨236748864916240363111035395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631330306443307634962761053 236748864916240363111035395)
        ·
          refine ⟨355123297374360544666553093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236748864916240363111035395 355123297374360544666553093)
          ·
            refine ⟨66585618257692602124978705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355123297374360544666553093 66585618257692602124978705)
            ·
              refine ⟨49939213693269451593734029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66585618257692602124978705 49939213693269451593734029)
              ·
                refine ⟨18727205134976044347650261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49939213693269451593734029 18727205134976044347650261)
                ·
                  refine ⟨438918870351001039398053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18727205134976044347650261 438918870351001039398053)
                  ·
                    rfl

theorem cell23_7693123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 3, 7].length) (baseStart_7693123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693123 prefixEnd_7693123 := by exact prefixLift 7693123
  have htrace : WordTrace (prefixWord ++ tailWord_7693123) baseStart_7693123 baseEnd_7693123 := by
    simpa [prefixWord, tailWord_7693123, baseEnd_7693123] using wordTrace_append hprefix tailTrace_7693123
  have hstable : (prefixWord ++ tailWord_7693123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693123).length < 2 ^ (prefixWord ++ tailWord_7693123).sum := by decide
  have hdescent : baseEnd_7693123 < baseStart_7693123 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693163 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_7693163 : Nat := 118140960795 + 7693163 * 2 ^ 59
def prefixEnd_7693163 : Nat := 4983230072969 + 3 ^ 40 * 7693163 * 2
def baseEnd_7693163 : Nat := 3950290372385189198082293

theorem tailTrace_7693163 : CollatzResearch.WordTrace tailWord_7693163 prefixEnd_7693163 3950290372385189198082293 := by
  unfold tailWord_7693163
  simp only [CollatzResearch.WordTrace]
  refine ⟨280592706227991813481572143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187061804151994542321048095 280592706227991813481572143)
  ·
    refine ⟨420889059341987720222358215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280592706227991813481572143 420889059341987720222358215)
    ·
      refine ⟨631333589012981580333537323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420889059341987720222358215 631333589012981580333537323)
      ·
        refine ⟨947000383519472370500305985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631333589012981580333537323 947000383519472370500305985)
        ·
          refine ⟨710250287639604277875229489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947000383519472370500305985 710250287639604277875229489)
          ·
            refine ⟨532687715729703208406422117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710250287639604277875229489 532687715729703208406422117)
            ·
              refine ⟨99878946699319351576204147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 532687715729703208406422117 99878946699319351576204147)
              ·
                refine ⟨149818420048979027364306221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99878946699319351576204147 149818420048979027364306221)
                ·
                  refine ⟨56181907518367135261614833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149818420048979027364306221 56181907518367135261614833)
                  ·
                    refine ⟨42136430638775351446211125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56181907518367135261614833 42136430638775351446211125)
                    ·
                      refine ⟨3950290372385189198082293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42136430638775351446211125 3950290372385189198082293)
                      ·
                        rfl

theorem cell23_7693163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_7693163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693163 prefixEnd_7693163 := by exact prefixLift 7693163
  have htrace : WordTrace (prefixWord ++ tailWord_7693163) baseStart_7693163 baseEnd_7693163 := by
    simpa [prefixWord, tailWord_7693163, baseEnd_7693163] using wordTrace_append hprefix tailTrace_7693163
  have hstable : (prefixWord ++ tailWord_7693163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693163).length < 2 ^ (prefixWord ++ tailWord_7693163).sum := by decide
  have hdescent : baseEnd_7693163 < baseStart_7693163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693170 : List Nat := [3, 2, 1, 2, 1, 1, 2, 4, 2, 5]
def baseStart_7693170 : Nat := 118140960795 + 7693170 * 2 ^ 59
def prefixEnd_7693170 : Nat := 4983230072969 + 3 ^ 40 * 7693170 * 2
def baseEnd_7693170 : Nat := 1316764655583256890231587

theorem tailTrace_7693170 : CollatzResearch.WordTrace tailWord_7693170 prefixEnd_7693170 1316764655583256890231587 := by
  unfold tailWord_7693170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70148240384741613419269241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187061974359310969118051309 70148240384741613419269241)
  ·
    refine ⟨52611180288556210064451931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70148240384741613419269241 52611180288556210064451931)
    ·
      refine ⟨78916770432834315096677897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52611180288556210064451931 78916770432834315096677897)
      ·
        refine ⟨59187577824625736322508423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78916770432834315096677897 59187577824625736322508423)
        ·
          refine ⟨88781366736938604483762635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59187577824625736322508423 88781366736938604483762635)
          ·
            refine ⟨133172050105407906725643953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88781366736938604483762635 133172050105407906725643953)
            ·
              refine ⟨99879037579055930044232965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133172050105407906725643953 99879037579055930044232965)
              ·
                refine ⟨18727319546072986883293681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99879037579055930044232965 18727319546072986883293681)
                ·
                  refine ⟨14045489659554740162470261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18727319546072986883293681 14045489659554740162470261)
                  ·
                    refine ⟨1316764655583256890231587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14045489659554740162470261 1316764655583256890231587)
                    ·
                      rfl

theorem cell23_7693170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 4, 2, 5].length) (baseStart_7693170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693170 prefixEnd_7693170 := by exact prefixLift 7693170
  have htrace : WordTrace (prefixWord ++ tailWord_7693170) baseStart_7693170 baseEnd_7693170 := by
    simpa [prefixWord, tailWord_7693170, baseEnd_7693170] using wordTrace_append hprefix tailTrace_7693170
  have hstable : (prefixWord ++ tailWord_7693170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693170).length < 2 ^ (prefixWord ++ tailWord_7693170).sum := by decide
  have hdescent : baseEnd_7693170 < baseStart_7693170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693174 : List Nat := [5, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_7693174 : Nat := 118140960795 + 7693174 * 2 ^ 59
def prefixEnd_7693174 : Nat := 4983230072969 + 3 ^ 40 * 7693174 * 2
def baseEnd_7693174 : Nat := 438921780074709850560527

theorem tailTrace_7693174 : CollatzResearch.WordTrace tailWord_7693174 prefixEnd_7693174 438921780074709850560527 := by
  unfold tailWord_7693174
  simp only [CollatzResearch.WordTrace]
  refine ⟨17537069214434497647513911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187062071620634641573481717 17537069214434497647513911)
  ·
    refine ⟨26305603821651746471270867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17537069214434497647513911 26305603821651746471270867)
    ·
      refine ⟨39458405732477619706906301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26305603821651746471270867 39458405732477619706906301)
      ·
        refine ⟨14796902149679107390089863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39458405732477619706906301 14796902149679107390089863)
        ·
          refine ⟨22195353224518661085134795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14796902149679107390089863 22195353224518661085134795)
          ·
            refine ⟨33293029836777991627702193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22195353224518661085134795 33293029836777991627702193)
            ·
              refine ⟨24969772377583493720776645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33293029836777991627702193 24969772377583493720776645)
              ·
                refine ⟨4681832320796905072645621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24969772377583493720776645 4681832320796905072645621)
                ·
                  refine ⟨438921780074709850560527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4681832320796905072645621 438921780074709850560527)
                  ·
                    rfl

theorem cell23_7693174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_7693174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693174 prefixEnd_7693174 := by exact prefixLift 7693174
  have htrace : WordTrace (prefixWord ++ tailWord_7693174) baseStart_7693174 baseEnd_7693174 := by
    simpa [prefixWord, tailWord_7693174, baseEnd_7693174] using wordTrace_append hprefix tailTrace_7693174
  have hstable : (prefixWord ++ tailWord_7693174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693174).length < 2 ^ (prefixWord ++ tailWord_7693174).sum := by decide
  have hdescent : baseEnd_7693174 < baseStart_7693174 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693203 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_7693203 : Nat := 118140960795 + 7693203 * 2 ^ 59
def prefixEnd_7693203 : Nat := 4983230072969 + 3 ^ 40 * 7693203 * 2
def baseEnd_7693203 : Nat := 3950310911611369041582109

theorem tailTrace_7693203 : CollatzResearch.WordTrace tailWord_7693203 prefixEnd_7693203 3950310911611369041582109 := by
  unfold tailWord_7693203
  simp only [CollatzResearch.WordTrace]
  refine ⟨280594165147846900313028263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187062776765231266875352175 280594165147846900313028263)
  ·
    refine ⟨420891247721770350469542395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280594165147846900313028263 420891247721770350469542395)
    ·
      refine ⟨631336871582655525704313593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420891247721770350469542395 631336871582655525704313593)
      ·
        refine ⟨473502653686991644278235195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631336871582655525704313593 473502653686991644278235195)
        ·
          refine ⟨710253980530487466417352793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473502653686991644278235195 710253980530487466417352793)
          ·
            refine ⟨532690485397865599813014595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710253980530487466417352793 532690485397865599813014595)
            ·
              refine ⟨799035728096798399719521893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532690485397865599813014595 799035728096798399719521893)
              ·
                refine ⟨149819199018149699947410355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799035728096798399719521893 149819199018149699947410355)
                ·
                  refine ⟨224728798527224549921115533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149819199018149699947410355 224728798527224549921115533)
                  ·
                    refine ⟨84273299447709206220418325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224728798527224549921115533 84273299447709206220418325)
                    ·
                      refine ⟨3950310911611369041582109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84273299447709206220418325 3950310911611369041582109)
                      ·
                        rfl

theorem cell23_7693203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_7693203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693203 prefixEnd_7693203 := by exact prefixLift 7693203
  have htrace : WordTrace (prefixWord ++ tailWord_7693203) baseStart_7693203 baseEnd_7693203 := by
    simpa [prefixWord, tailWord_7693203, baseEnd_7693203] using wordTrace_append hprefix tailTrace_7693203
  have hstable : (prefixWord ++ tailWord_7693203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693203).length < 2 ^ (prefixWord ++ tailWord_7693203).sum := by decide
  have hdescent : baseEnd_7693203 < baseStart_7693203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693285 : List Nat := [1, 3, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_7693285 : Nat := 118140960795 + 7693285 * 2 ^ 59
def prefixEnd_7693285 : Nat := 4983230072969 + 3 ^ 40 * 7693285 * 2
def baseEnd_7693285 : Nat := 1316784339008345906918911

theorem tailTrace_7693285 : CollatzResearch.WordTrace tailWord_7693285 prefixEnd_7693285 1316784339008345906918911 := by
  unfold tailWord_7693285
  simp only [CollatzResearch.WordTrace]
  refine ⟨280597155933549828317513309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187064770622366552211675539 280597155933549828317513309)
  ·
    refine ⟨105223933475081185619067491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280597155933549828317513309 105223933475081185619067491)
    ·
      refine ⟨157835900212621778428601237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105223933475081185619067491 157835900212621778428601237)
      ·
        refine ⟨7398557822466645863840683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157835900212621778428601237 7398557822466645863840683)
        ·
          refine ⟨11097836733699968795761025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398557822466645863840683 11097836733699968795761025)
          ·
            refine ⟨8323377550274976596820769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11097836733699968795761025 8323377550274976596820769)
            ·
              refine ⟨6242533162706232447615577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8323377550274976596820769 6242533162706232447615577)
              ·
                refine ⟨4681899872029674335711683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6242533162706232447615577 4681899872029674335711683)
                ·
                  refine ⟨7022849808044511503567525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681899872029674335711683 7022849808044511503567525)
                  ·
                    refine ⟨1316784339008345906918911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7022849808044511503567525 1316784339008345906918911)
                    ·
                      rfl

theorem cell23_7693285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_7693285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693285 prefixEnd_7693285 := by exact prefixLift 7693285
  have htrace : WordTrace (prefixWord ++ tailWord_7693285) baseStart_7693285 baseEnd_7693285 := by
    simpa [prefixWord, tailWord_7693285, baseEnd_7693285] using wordTrace_append hprefix tailTrace_7693285
  have hstable : (prefixWord ++ tailWord_7693285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693285).length < 2 ^ (prefixWord ++ tailWord_7693285).sum := by decide
  have hdescent : baseEnd_7693285 < baseStart_7693285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693297 : List Nat := [1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_7693297 : Nat := 118140960795 + 7693297 * 2 ^ 59
def prefixEnd_7693297 : Nat := 4983230072969 + 3 ^ 40 * 7693297 * 2
def baseEnd_7693297 : Nat := 3950359178792891673806677

theorem tailTrace_7693297 : CollatzResearch.WordTrace tailWord_7693297 prefixEnd_7693297 3950359178792891673806677 := by
  unfold tailWord_7693297
  simp only [CollatzResearch.WordTrace]
  refine ⟨280597593609506354366950145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187065062406337569577966763 280597593609506354366950145)
  ·
    refine ⟨210448195207129765775212609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280597593609506354366950145 210448195207129765775212609)
    ·
      refine ⟨157836146405347324331409457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210448195207129765775212609 157836146405347324331409457)
      ·
        refine ⟨118377109804010493248557093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157836146405347324331409457 118377109804010493248557093)
        ·
          refine ⟨22195708088251967484104455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118377109804010493248557093 22195708088251967484104455)
          ·
            refine ⟨33293562132377951226156683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22195708088251967484104455 33293562132377951226156683)
            ·
              refine ⟨49940343198566926839235025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33293562132377951226156683 49940343198566926839235025)
              ·
                refine ⟨37455257398925195129426269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49940343198566926839235025 37455257398925195129426269)
                ·
                  refine ⟨14045721524596948173534851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37455257398925195129426269 14045721524596948173534851)
                  ·
                    refine ⟨21068582286895422260302277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14045721524596948173534851 21068582286895422260302277)
                    ·
                      refine ⟨3950359178792891673806677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21068582286895422260302277 3950359178792891673806677)
                      ·
                        rfl

theorem cell23_7693297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_7693297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693297 prefixEnd_7693297 := by exact prefixLift 7693297
  have htrace : WordTrace (prefixWord ++ tailWord_7693297) baseStart_7693297 baseEnd_7693297 := by
    simpa [prefixWord, tailWord_7693297, baseEnd_7693297] using wordTrace_append hprefix tailTrace_7693297
  have hstable : (prefixWord ++ tailWord_7693297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693297).length < 2 ^ (prefixWord ++ tailWord_7693297).sum := by decide
  have hdescent : baseEnd_7693297 < baseStart_7693297 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693317 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_7693317 : Nat := 118140960795 + 7693317 * 2 ^ 59
def prefixEnd_7693317 : Nat := 4983230072969 + 3 ^ 40 * 7693317 * 2
def baseEnd_7693317 : Nat := 3950369448405981595556585

theorem tailTrace_7693317 : CollatzResearch.WordTrace tailWord_7693317 prefixEnd_7693317 3950369448405981595556585 := by
  unfold tailWord_7693317
  simp only [CollatzResearch.WordTrace]
  refine ⟨280598323069433897782678205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187065548712955931855118803 280598323069433897782678205)
  ·
    refine ⟨105224371151037711668504327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280598323069433897782678205 105224371151037711668504327)
    ·
      refine ⟨157836556726556567502756491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105224371151037711668504327 157836556726556567502756491)
      ·
        refine ⟨236754835089834851254134737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157836556726556567502756491 236754835089834851254134737)
        ·
          refine ⟨177566126317376138440601053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236754835089834851254134737 177566126317376138440601053)
          ·
            refine ⟨66587297369016051915225395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177566126317376138440601053 66587297369016051915225395)
            ·
              refine ⟨99880946053524077872838093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66587297369016051915225395 99880946053524077872838093)
              ·
                refine ⟨37455354770071529202314285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99880946053524077872838093 37455354770071529202314285)
                ·
                  refine ⟨14045758038776823450867857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37455354770071529202314285 14045758038776823450867857)
                  ·
                    refine ⟨10534318529082617588150893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14045758038776823450867857 10534318529082617588150893)
                    ·
                      refine ⟨3950369448405981595556585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534318529082617588150893 3950369448405981595556585)
                      ·
                        rfl

theorem cell23_7693317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_7693317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693317 prefixEnd_7693317 := by exact prefixLift 7693317
  have htrace : WordTrace (prefixWord ++ tailWord_7693317) baseStart_7693317 baseEnd_7693317 := by
    simpa [prefixWord, tailWord_7693317, baseEnd_7693317] using wordTrace_append hprefix tailTrace_7693317
  have hstable : (prefixWord ++ tailWord_7693317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693317).length < 2 ^ (prefixWord ++ tailWord_7693317).sum := by decide
  have hdescent : baseEnd_7693317 < baseStart_7693317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693348 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7693348 : Nat := 118140960795 + 7693348 * 2 ^ 59
def prefixEnd_7693348 : Nat := 4983230072969 + 3 ^ 40 * 7693348 * 2
def baseEnd_7693348 : Nat := 3950385366306270974268943

theorem tailTrace_7693348 : CollatzResearch.WordTrace tailWord_7693348 prefixEnd_7693348 3950385366306270974268943 := by
  unfold tailWord_7693348
  simp only [CollatzResearch.WordTrace]
  refine ⟨140299726866160795038528349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187066302488214393384704465 140299726866160795038528349)
  ·
    refine ⟨52612397574810298139448131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140299726866160795038528349 52612397574810298139448131)
    ·
      refine ⟨78918596362215447209172197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52612397574810298139448131 78918596362215447209172197)
      ·
        refine ⟨14797236817915396351719787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78918596362215447209172197 14797236817915396351719787)
        ·
          refine ⟨22195855226873094527579681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14797236817915396351719787 22195855226873094527579681)
          ·
            refine ⟨16646891420154820895684761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22195855226873094527579681 16646891420154820895684761)
            ·
              refine ⟨12485168565116115671763571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16646891420154820895684761 12485168565116115671763571)
              ·
                refine ⟨18727752847674173507645357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485168565116115671763571 18727752847674173507645357)
                ·
                  refine ⟨7022907317877815065367009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18727752847674173507645357 7022907317877815065367009)
                  ·
                    refine ⟨5267180488408361299025257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7022907317877815065367009 5267180488408361299025257)
                    ·
                      refine ⟨3950385366306270974268943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267180488408361299025257 3950385366306270974268943)
                      ·
                        rfl

theorem cell23_7693348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7693348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693348 prefixEnd_7693348 := by exact prefixLift 7693348
  have htrace : WordTrace (prefixWord ++ tailWord_7693348) baseStart_7693348 baseEnd_7693348 := by
    simpa [prefixWord, tailWord_7693348, baseEnd_7693348] using wordTrace_append hprefix tailTrace_7693348
  have hstable : (prefixWord ++ tailWord_7693348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693348).length < 2 ^ (prefixWord ++ tailWord_7693348).sum := by decide
  have hdescent : baseEnd_7693348 < baseStart_7693348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693382 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2]
def baseStart_7693382 : Nat := 118140960795 + 7693382 * 2 ^ 59
def prefixEnd_7693382 : Nat := 4983230072969 + 3 ^ 40 * 7693382 * 2
def baseEnd_7693382 : Nat := 3950402824648523841243787

theorem tailTrace_7693382 : CollatzResearch.WordTrace tailWord_7693382 prefixEnd_7693382 3950402824648523841243787 := by
  unfold tailWord_7693382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8768771681693700433868575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187067129209465609255862933 8768771681693700433868575)
  ·
    refine ⟨13153157522540550650802863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8768771681693700433868575 13153157522540550650802863)
    ·
      refine ⟨19729736283810825976204295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13153157522540550650802863 19729736283810825976204295)
      ·
        refine ⟨29594604425716238964306443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19729736283810825976204295 29594604425716238964306443)
        ·
          refine ⟨44391906638574358446459665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29594604425716238964306443 44391906638574358446459665)
          ·
            refine ⟨33293929978930768834844749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44391906638574358446459665 33293929978930768834844749)
            ·
              refine ⟨12485223742099038313066781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33293929978930768834844749 12485223742099038313066781)
              ·
                refine ⟨4681958903287139367400043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12485223742099038313066781 4681958903287139367400043)
                ·
                  refine ⟨7022938354930709051100065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4681958903287139367400043 7022938354930709051100065)
                  ·
                    refine ⟨5267203766198031788325049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7022938354930709051100065 5267203766198031788325049)
                    ·
                      refine ⟨3950402824648523841243787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267203766198031788325049 3950402824648523841243787)
                      ·
                        rfl

theorem cell23_7693382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2].length) (baseStart_7693382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693382 prefixEnd_7693382 := by exact prefixLift 7693382
  have htrace : WordTrace (prefixWord ++ tailWord_7693382) baseStart_7693382 baseEnd_7693382 := by
    simpa [prefixWord, tailWord_7693382, baseEnd_7693382] using wordTrace_append hprefix tailTrace_7693382
  have hstable : (prefixWord ++ tailWord_7693382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693382).length < 2 ^ (prefixWord ++ tailWord_7693382).sum := by decide
  have hdescent : baseEnd_7693382 < baseStart_7693382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693407 : List Nat := [1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_7693407 : Nat := 118140960795 + 7693407 * 2 ^ 59
def prefixEnd_7693407 : Nat := 4983230072969 + 3 ^ 40 * 7693407 * 2
def baseEnd_7693407 : Nat := 3950415661664886243431171

theorem tailTrace_7693407 : CollatzResearch.WordTrace tailWord_7693407 prefixEnd_7693407 3950415661664886243431171 := by
  unfold tailWord_7693407
  simp only [CollatzResearch.WordTrace]
  refine ⟨280601605639107843153454475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187067737092738562102302983 280601605639107843153454475)
  ·
    refine ⟨420902408458661764730181713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280601605639107843153454475 420902408458661764730181713)
    ·
      refine ⟨315676806343996323547636285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420902408458661764730181713 315676806343996323547636285)
      ·
        refine ⟨118378802378998621330363607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315676806343996323547636285 118378802378998621330363607)
        ·
          refine ⟨177568203568497931995545411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118378802378998621330363607 177568203568497931995545411)
          ·
            refine ⟨266352305352746897993318117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177568203568497931995545411 266352305352746897993318117)
            ·
              refine ⟨49941057253640043373747147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266352305352746897993318117 49941057253640043373747147)
              ·
                refine ⟨74911585880460065060620721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49941057253640043373747147 74911585880460065060620721)
                ·
                  refine ⟨56183689410345048795465541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74911585880460065060620721 56183689410345048795465541)
                  ·
                    refine ⟨10534441764439696649149789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56183689410345048795465541 10534441764439696649149789)
                    ·
                      refine ⟨3950415661664886243431171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534441764439696649149789 3950415661664886243431171)
                      ·
                        rfl

theorem cell23_7693407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_7693407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693407 prefixEnd_7693407 := by exact prefixLift 7693407
  have htrace : WordTrace (prefixWord ++ tailWord_7693407) baseStart_7693407 baseEnd_7693407 := by
    simpa [prefixWord, tailWord_7693407, baseEnd_7693407] using wordTrace_append hprefix tailTrace_7693407
  have hstable : (prefixWord ++ tailWord_7693407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693407).length < 2 ^ (prefixWord ++ tailWord_7693407).sum := by decide
  have hdescent : baseEnd_7693407 < baseStart_7693407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693471 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_7693471 : Nat := 118140960795 + 7693471 * 2 ^ 59
def prefixEnd_7693471 : Nat := 4983230072969 + 3 ^ 40 * 7693471 * 2
def baseEnd_7693471 : Nat := 3950448524426773993030877

theorem tailTrace_7693471 : CollatzResearch.WordTrace tailWord_7693471 prefixEnd_7693471 3950448524426773993030877 := by
  unfold tailWord_7693471
  simp only [CollatzResearch.WordTrace]
  refine ⟨280603939910875982083784267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187069293273917321389189511 280603939910875982083784267)
  ·
    refine ⟨420905909866313973125676401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280603939910875982083784267 420905909866313973125676401)
    ·
      refine ⟨315679432399735479844257301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420905909866313973125676401 315679432399735479844257301)
      ·
        refine ⟨14797473393737600617699561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 315679432399735479844257301 14797473393737600617699561)
        ·
          refine ⟨11098105045303200463274671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14797473393737600617699561 11098105045303200463274671)
          ·
            refine ⟨16647157567954800694912007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098105045303200463274671 16647157567954800694912007)
            ·
              refine ⟨24970736351932201042368011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16647157567954800694912007 24970736351932201042368011)
              ·
                refine ⟨37456104527898301563552017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24970736351932201042368011 37456104527898301563552017)
                ·
                  refine ⟨28092078395923726172664013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37456104527898301563552017 28092078395923726172664013)
                  ·
                    refine ⟨10534529398471397314749005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28092078395923726172664013 10534529398471397314749005)
                    ·
                      refine ⟨3950448524426773993030877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534529398471397314749005 3950448524426773993030877)
                      ·
                        rfl

theorem cell23_7693471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_7693471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693471 prefixEnd_7693471 := by exact prefixLift 7693471
  have htrace : WordTrace (prefixWord ++ tailWord_7693471) baseStart_7693471 baseEnd_7693471 := by
    simpa [prefixWord, tailWord_7693471, baseEnd_7693471] using wordTrace_append hprefix tailTrace_7693471
  have hstable : (prefixWord ++ tailWord_7693471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693471).length < 2 ^ (prefixWord ++ tailWord_7693471).sum := by decide
  have hdescent : baseEnd_7693471 < baseStart_7693471 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693506 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_7693506 : Nat := 118140960795 + 7693506 * 2 ^ 59
def prefixEnd_7693506 : Nat := 4983230072969 + 3 ^ 40 * 7693506 * 2
def baseEnd_7693506 : Nat := 3950466496249681356093217

theorem tailTrace_7693506 : CollatzResearch.WordTrace tailWord_7693506 prefixEnd_7693506 3950466496249681356093217 := by
  unfold tailWord_7693506
  simp only [CollatzResearch.WordTrace]
  refine ⟨70151304116437295765327093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187070144310499455374205581 70151304116437295765327093)
  ·
    refine ⟨6576684760915996477999415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70151304116437295765327093 6576684760915996477999415)
    ·
      refine ⟨9865027141373994716999123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6576684760915996477999415 9865027141373994716999123)
      ·
        refine ⟨14797540712060992075498685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9865027141373994716999123 14797540712060992075498685)
        ·
          refine ⟨5549077767022872028312007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14797540712060992075498685 5549077767022872028312007)
          ·
            refine ⟨8323616650534308042468011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5549077767022872028312007 8323616650534308042468011)
            ·
              refine ⟨12485424975801462063702017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8323616650534308042468011 12485424975801462063702017)
              ·
                refine ⟨9364068731851096547776513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12485424975801462063702017 9364068731851096547776513)
                ·
                  refine ⟨7023051548888322410832385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9364068731851096547776513 7023051548888322410832385)
                  ·
                    refine ⟨5267288661666241808124289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7023051548888322410832385 5267288661666241808124289)
                    ·
                      refine ⟨3950466496249681356093217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267288661666241808124289 3950466496249681356093217)
                      ·
                        rfl

theorem cell23_7693506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_7693506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693506 prefixEnd_7693506 := by exact prefixLift 7693506
  have htrace : WordTrace (prefixWord ++ tailWord_7693506) baseStart_7693506 baseEnd_7693506 := by
    simpa [prefixWord, tailWord_7693506, baseEnd_7693506] using wordTrace_append hprefix tailTrace_7693506
  have hstable : (prefixWord ++ tailWord_7693506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693506).length < 2 ^ (prefixWord ++ tailWord_7693506).sum := by decide
  have hdescent : baseEnd_7693506 < baseStart_7693506 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693544 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_7693544 : Nat := 118140960795 + 7693544 * 2 ^ 59
def prefixEnd_7693544 : Nat := 4983230072969 + 3 ^ 40 * 7693544 * 2
def baseEnd_7693544 : Nat := 3950486008514552207418041

theorem tailTrace_7693544 : CollatzResearch.WordTrace tailWord_7693544 prefixEnd_7693544 3950486008514552207418041 := by
  unfold tailWord_7693544
  simp only [CollatzResearch.WordTrace]
  refine ⟨140303301219805757775595843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187071068293074343700794457 140303301219805757775595843)
  ·
    refine ⟨210454951829708636663393765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140303301219805757775595843 210454951829708636663393765)
    ·
      refine ⟨39460303468070369374386331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210454951829708636663393765 39460303468070369374386331)
      ·
        refine ⟨59190455202105554061579497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39460303468070369374386331 59190455202105554061579497)
        ·
          refine ⟨44392841401579165546184623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59190455202105554061579497 44392841401579165546184623)
          ·
            refine ⟨66589262102368748319276935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44392841401579165546184623 66589262102368748319276935)
            ·
              refine ⟨99883893153553122478915403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66589262102368748319276935 99883893153553122478915403)
              ·
                refine ⟨149825839730329683718373105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99883893153553122478915403 149825839730329683718373105)
                ·
                  refine ⟨112369379797747262788779829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149825839730329683718373105 112369379797747262788779829)
                  ·
                    refine ⟨10534629356038805886448109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112369379797747262788779829 10534629356038805886448109)
                    ·
                      refine ⟨3950486008514552207418041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534629356038805886448109 3950486008514552207418041)
                      ·
                        rfl

theorem cell23_7693544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_7693544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693544 prefixEnd_7693544 := by exact prefixLift 7693544
  have htrace : WordTrace (prefixWord ++ tailWord_7693544) baseStart_7693544 baseEnd_7693544 := by
    simpa [prefixWord, tailWord_7693544, baseEnd_7693544] using wordTrace_append hprefix tailTrace_7693544
  have hstable : (prefixWord ++ tailWord_7693544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693544).length < 2 ^ (prefixWord ++ tailWord_7693544).sum := by decide
  have hdescent : baseEnd_7693544 < baseStart_7693544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693571 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 4, 3, 2]
def baseStart_7693571 : Nat := 118140960795 + 7693571 * 2 ^ 59
def prefixEnd_7693571 : Nat := 4983230072969 + 3 ^ 40 * 7693571 * 2
def baseEnd_7693571 : Nat := 3950499872492223601780417

theorem tailTrace_7693571 : CollatzResearch.WordTrace tailWord_7693571 prefixEnd_7693571 3950499872492223601780417 := by
  unfold tailWord_7693571
  simp only [CollatzResearch.WordTrace]
  refine ⟨280607587210513699162424567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187071724807009132774949711 280607587210513699162424567)
  ·
    refine ⟨420911380815770548743636851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280607587210513699162424567 420911380815770548743636851)
    ·
      refine ⟨631367071223655823115455277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420911380815770548743636851 631367071223655823115455277)
      ·
        refine ⟨236762651708870933668295729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 631367071223655823115455277 236762651708870933668295729)
        ·
          refine ⟨177571988781653200251221797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236762651708870933668295729 177571988781653200251221797)
          ·
            refine ⟨33294747896559975047104087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177571988781653200251221797 33294747896559975047104087)
            ·
              refine ⟨49942121844839962570656131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33294747896559975047104087 49942121844839962570656131)
              ·
                refine ⟨74913182767259943855984197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49942121844839962570656131 74913182767259943855984197)
                ·
                  refine ⟨14046221768861239472997037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74913182767259943855984197 14046221768861239472997037)
                  ·
                    refine ⟨5267333163322964802373889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14046221768861239472997037 5267333163322964802373889)
                    ·
                      refine ⟨3950499872492223601780417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267333163322964802373889 3950499872492223601780417)
                      ·
                        rfl

theorem cell23_7693571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_7693571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693571 prefixEnd_7693571 := by exact prefixLift 7693571
  have htrace : WordTrace (prefixWord ++ tailWord_7693571) baseStart_7693571 baseEnd_7693571 := by
    simpa [prefixWord, tailWord_7693571, baseEnd_7693571] using wordTrace_append hprefix tailTrace_7693571
  have hstable : (prefixWord ++ tailWord_7693571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693571).length < 2 ^ (prefixWord ++ tailWord_7693571).sum := by decide
  have hdescent : baseEnd_7693571 < baseStart_7693571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693621 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_7693621 : Nat := 118140960795 + 7693621 * 2 ^ 59
def prefixEnd_7693621 : Nat := 4983230072969 + 3 ^ 40 * 7693621 * 2
def baseEnd_7693621 : Nat := 3950525546524948406155187

theorem tailTrace_7693621 : CollatzResearch.WordTrace tailWord_7693621 prefixEnd_7693621 3950525546524948406155187 := by
  unfold tailWord_7693621
  simp only [CollatzResearch.WordTrace]
  refine ⟨280609410860332557701744717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187072940573555038467829811 280609410860332557701744717)
  ·
    refine ⟨105228529072624709138154269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280609410860332557701744717 105228529072624709138154269)
    ·
      refine ⟨39460698402234265926807851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105228529072624709138154269 39460698402234265926807851)
      ·
        refine ⟨59191047603351398890211777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39460698402234265926807851 59191047603351398890211777)
        ·
          refine ⟨44393285702513549167658833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59191047603351398890211777 44393285702513549167658833)
          ·
            refine ⟨33294964276885161875744125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44393285702513549167658833 33294964276885161875744125)
            ·
              refine ⟨12485611603831935703404047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33294964276885161875744125 12485611603831935703404047)
              ·
                refine ⟨18728417405747903555106071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485611603831935703404047 18728417405747903555106071)
                ·
                  refine ⟨28092626108621855332659107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18728417405747903555106071 28092626108621855332659107)
                  ·
                    refine ⟨42138939162932782998988661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28092626108621855332659107 42138939162932782998988661)
                    ·
                      refine ⟨3950525546524948406155187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42138939162932782998988661 3950525546524948406155187)
                      ·
                        rfl

theorem cell23_7693621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_7693621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693621 prefixEnd_7693621 := by exact prefixLift 7693621
  have htrace : WordTrace (prefixWord ++ tailWord_7693621) baseStart_7693621 baseEnd_7693621 := by
    simpa [prefixWord, tailWord_7693621, baseEnd_7693621] using wordTrace_append hprefix tailTrace_7693621
  have hstable : (prefixWord ++ tailWord_7693621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693621).length < 2 ^ (prefixWord ++ tailWord_7693621).sum := by decide
  have hdescent : baseEnd_7693621 < baseStart_7693621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693628 : List Nat := [2, 2, 2, 2, 1, 4, 2, 2, 2, 4]
def baseStart_7693628 : Nat := 118140960795 + 7693628 * 2 ^ 59
def prefixEnd_7693628 : Nat := 4983230072969 + 3 ^ 40 * 7693628 * 2
def baseEnd_7693628 : Nat := 1316843046963176626255885

theorem tailTrace_7693628 : CollatzResearch.WordTrace tailWord_7693628 prefixEnd_7693628 1316843046963176626255885 := by
  unfold tailWord_7693628
  simp only [CollatzResearch.WordTrace]
  refine ⟨140304833085653598948624769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187073110780871465264833025 140304833085653598948624769)
  ·
    refine ⟨105228624814240199211468577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140304833085653598948624769 105228624814240199211468577)
    ·
      refine ⟨78921468610680149408601433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105228624814240199211468577 78921468610680149408601433)
      ·
        refine ⟨59191101458010112056451075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78921468610680149408601433 59191101458010112056451075)
        ·
          refine ⟨88786652187015168084676613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59191101458010112056451075 88786652187015168084676613)
          ·
            refine ⟨16647497285065344015876865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88786652187015168084676613 16647497285065344015876865)
            ·
              refine ⟨12485622963799008011907649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16647497285065344015876865 12485622963799008011907649)
              ·
                refine ⟨9364217222849256008930737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12485622963799008011907649 9364217222849256008930737)
                ·
                  refine ⟨7023162917136942006698053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9364217222849256008930737 7023162917136942006698053)
                  ·
                    refine ⟨1316843046963176626255885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023162917136942006698053 1316843046963176626255885)
                    ·
                      rfl

theorem cell23_7693628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_7693628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693628 prefixEnd_7693628 := by exact prefixLift 7693628
  have htrace : WordTrace (prefixWord ++ tailWord_7693628) baseStart_7693628 baseEnd_7693628 := by
    simpa [prefixWord, tailWord_7693628, baseEnd_7693628] using wordTrace_append hprefix tailTrace_7693628
  have hstable : (prefixWord ++ tailWord_7693628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693628).length < 2 ^ (prefixWord ++ tailWord_7693628).sum := by decide
  have hdescent : baseEnd_7693628 < baseStart_7693628 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693645 : List Nat := [1, 6, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7693645 : Nat := 118140960795 + 7693645 * 2 ^ 59
def prefixEnd_7693645 : Nat := 4983230072969 + 3 ^ 40 * 7693645 * 2
def baseEnd_7693645 : Nat := 1316845956686885437418359

theorem tailTrace_7693645 : CollatzResearch.WordTrace tailWord_7693645 prefixEnd_7693645 1316845956686885437418359 := by
  unfold tailWord_7693645
  simp only [CollatzResearch.WordTrace]
  refine ⟨280610286212245609800618389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187073524141497073200412259 280610286212245609800618389)
  ·
    refine ⟨13153607166199012959403987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 280610286212245609800618389 13153607166199012959403987)
    ·
      refine ⟨19730410749298519439105981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13153607166199012959403987 19730410749298519439105981)
      ·
        refine ⟨7398904030986944789664743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19730410749298519439105981 7398904030986944789664743)
        ·
          refine ⟨11098356046480417184497115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7398904030986944789664743 11098356046480417184497115)
          ·
            refine ⟨16647534069720625776745673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098356046480417184497115 16647534069720625776745673)
            ·
              refine ⟨12485650552290469332559255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16647534069720625776745673 12485650552290469332559255)
              ·
                refine ⟨18728475828435703998838883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485650552290469332559255 18728475828435703998838883)
                ·
                  refine ⟨28092713742653555998258325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18728475828435703998838883 28092713742653555998258325)
                  ·
                    refine ⟨1316845956686885437418359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28092713742653555998258325 1316845956686885437418359)
                    ·
                      rfl

theorem cell23_7693645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7693645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693645 prefixEnd_7693645 := by exact prefixLift 7693645
  have htrace : WordTrace (prefixWord ++ tailWord_7693645) baseStart_7693645 baseEnd_7693645 := by
    simpa [prefixWord, tailWord_7693645, baseEnd_7693645] using wordTrace_append hprefix tailTrace_7693645
  have hstable : (prefixWord ++ tailWord_7693645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693645).length < 2 ^ (prefixWord ++ tailWord_7693645).sum := by decide
  have hdescent : baseEnd_7693645 < baseStart_7693645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693651 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 3]
def baseStart_7693651 : Nat := 118140960795 + 7693651 * 2 ^ 59
def prefixEnd_7693651 : Nat := 4983230072969 + 3 ^ 40 * 7693651 * 2
def baseEnd_7693651 : Nat := 3950540950944583288780049

theorem tailTrace_7693651 : CollatzResearch.WordTrace tailWord_7693651 prefixEnd_7693651 3950540950944583288780049 := by
  unfold tailWord_7693651
  simp only [CollatzResearch.WordTrace]
  refine ⟨280610505050223872825336807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187073670033482581883557871 280610505050223872825336807)
  ·
    refine ⟨420915757575335809238005211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280610505050223872825336807 420915757575335809238005211)
    ·
      refine ⟨631373636363003713857007817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420915757575335809238005211 631373636363003713857007817)
      ·
        refine ⟨473530227272252785392755863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631373636363003713857007817 473530227272252785392755863)
        ·
          refine ⟨710295340908379178089133795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473530227272252785392755863 710295340908379178089133795)
          ·
            refine ⟨1065443011362568767133700693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710295340908379178089133795 1065443011362568767133700693)
            ·
              refine ⟨12485660289405102739848055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1065443011362568767133700693 12485660289405102739848055)
              ·
                refine ⟨18728490434107654109772083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12485660289405102739848055 18728490434107654109772083)
                ·
                  refine ⟨28092735651161481164658125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18728490434107654109772083 28092735651161481164658125)
                  ·
                    refine ⟨10534775869185555436746797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28092735651161481164658125 10534775869185555436746797)
                    ·
                      refine ⟨3950540950944583288780049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534775869185555436746797 3950540950944583288780049)
                      ·
                        rfl

theorem cell23_7693651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_7693651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693651 prefixEnd_7693651 := by exact prefixLift 7693651
  have htrace : WordTrace (prefixWord ++ tailWord_7693651) baseStart_7693651 baseEnd_7693651 := by
    simpa [prefixWord, tailWord_7693651, baseEnd_7693651] using wordTrace_append hprefix tailTrace_7693651
  have hstable : (prefixWord ++ tailWord_7693651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693651).length < 2 ^ (prefixWord ++ tailWord_7693651).sum := by decide
  have hdescent : baseEnd_7693651 < baseStart_7693651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693672 : List Nat := [2, 1, 4, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_7693672 : Nat := 118140960795 + 7693672 * 2 ^ 59
def prefixEnd_7693672 : Nat := 4983230072969 + 3 ^ 40 * 7693672 * 2
def baseEnd_7693672 : Nat := 3950551734038327706617453

theorem tailTrace_7693672 : CollatzResearch.WordTrace tailWord_7693672 prefixEnd_7693672 3950551734038327706617453 := by
  unfold tailWord_7693672
  simp only [CollatzResearch.WordTrace]
  refine ⟨140305635491573896705925635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187074180655431862274567513 140305635491573896705925635)
  ·
    refine ⟨210458453237360845058888453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140305635491573896705925635 210458453237360845058888453)
    ·
      refine ⟨39460959982005158448541585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210458453237360845058888453 39460959982005158448541585)
      ·
        refine ⟨29595719986503868836406189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39460959982005158448541585 29595719986503868836406189)
        ·
          refine ⟨11098394994938950813652321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29595719986503868836406189 11098394994938950813652321)
          ·
            refine ⟨8323796246204213110239241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11098394994938950813652321 8323796246204213110239241)
            ·
              refine ⟨6242847184653159832679431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8323796246204213110239241 6242847184653159832679431)
              ·
                refine ⟨9364270776979739749019147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6242847184653159832679431 9364270776979739749019147)
                ·
                  refine ⟨14046406165469609623528721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9364270776979739749019147 14046406165469609623528721)
                  ·
                    refine ⟨10534804624102207217646541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14046406165469609623528721 10534804624102207217646541)
                    ·
                      refine ⟨3950551734038327706617453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534804624102207217646541 3950551734038327706617453)
                      ·
                        rfl

theorem cell23_7693672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_7693672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693672 prefixEnd_7693672 := by exact prefixLift 7693672
  have htrace : WordTrace (prefixWord ++ tailWord_7693672) baseStart_7693672 baseEnd_7693672 := by
    simpa [prefixWord, tailWord_7693672, baseEnd_7693672] using wordTrace_append hprefix tailTrace_7693672
  have hstable : (prefixWord ++ tailWord_7693672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693672).length < 2 ^ (prefixWord ++ tailWord_7693672).sum := by decide
  have hdescent : baseEnd_7693672 < baseStart_7693672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693685 : List Nat := [1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_7693685 : Nat := 118140960795 + 7693685 * 2 ^ 59
def prefixEnd_7693685 : Nat := 4983230072969 + 3 ^ 40 * 7693685 * 2
def baseEnd_7693685 : Nat := 3950558409286836155754893

theorem tailTrace_7693685 : CollatzResearch.WordTrace tailWord_7693685 prefixEnd_7693685 3950558409286836155754893 := by
  unfold tailWord_7693685
  simp only [CollatzResearch.WordTrace]
  refine ⟨280611745132100696632074509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187074496754733797754716339 280611745132100696632074509)
  ·
    refine ⟨105229404424537761237027941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280611745132100696632074509 105229404424537761237027941)
    ·
      refine ⟨19730513329600830231942739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105229404424537761237027941 19730513329600830231942739)
      ·
        refine ⟨29595769994401245347914109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19730513329600830231942739 29595769994401245347914109)
        ·
          refine ⟨11098413747900467005467791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29595769994401245347914109 11098413747900467005467791)
          ·
            refine ⟨16647620621850700508201687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098413747900467005467791 16647620621850700508201687)
            ·
              refine ⟨24971430932776050762302531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16647620621850700508201687 24971430932776050762302531)
              ·
                refine ⟨37457146399164076143453797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24971430932776050762302531 37457146399164076143453797)
                ·
                  refine ⟨7023214949843264276897587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37457146399164076143453797 7023214949843264276897587)
                  ·
                    refine ⟨10534822424764896415346381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023214949843264276897587 10534822424764896415346381)
                    ·
                      refine ⟨3950558409286836155754893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10534822424764896415346381 3950558409286836155754893)
                      ·
                        rfl

theorem cell23_7693685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_7693685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693685 prefixEnd_7693685 := by exact prefixLift 7693685
  have htrace : WordTrace (prefixWord ++ tailWord_7693685) baseStart_7693685 baseEnd_7693685 := by
    simpa [prefixWord, tailWord_7693685, baseEnd_7693685] using wordTrace_append hprefix tailTrace_7693685
  have hstable : (prefixWord ++ tailWord_7693685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693685).length < 2 ^ (prefixWord ++ tailWord_7693685).sum := by decide
  have hdescent : baseEnd_7693685 < baseStart_7693685 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693725 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 4, 2, 2]
def baseStart_7693725 : Nat := 118140960795 + 7693725 * 2 ^ 59
def prefixEnd_7693725 : Nat := 4983230072969 + 3 ^ 40 * 7693725 * 2
def baseEnd_7693725 : Nat := 3950578948513015999254709

theorem tailTrace_7693725 : CollatzResearch.WordTrace tailWord_7693725 prefixEnd_7693725 3950578948513015999254709 := by
  unfold tailWord_7693725
  simp only [CollatzResearch.WordTrace]
  refine ⟨280613204051955783463530629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187075469367970522309020419 280613204051955783463530629)
  ·
    refine ⟨52614975759741709399411993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280613204051955783463530629 52614975759741709399411993)
    ·
      refine ⟨39461231819806282049558995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52614975759741709399411993 39461231819806282049558995)
      ·
        refine ⟨59191847729709423074338493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39461231819806282049558995 59191847729709423074338493)
        ·
          refine ⟨22196942898641033652876935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59191847729709423074338493 22196942898641033652876935)
          ·
            refine ⟨33295414347961550479315403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22196942898641033652876935 33295414347961550479315403)
            ·
              refine ⟨49943121521942325718973105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33295414347961550479315403 49943121521942325718973105)
              ·
                refine ⟨37457341141456744289229829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49943121521942325718973105 37457341141456744289229829)
                ·
                  refine ⟨7023251464023139554230593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37457341141456744289229829 7023251464023139554230593)
                  ·
                    refine ⟨5267438598017354665672945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7023251464023139554230593 5267438598017354665672945)
                    ·
                      refine ⟨3950578948513015999254709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267438598017354665672945 3950578948513015999254709)
                      ·
                        rfl

theorem cell23_7693725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_7693725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693725 prefixEnd_7693725 := by exact prefixLift 7693725
  have htrace : WordTrace (prefixWord ++ tailWord_7693725) baseStart_7693725 baseEnd_7693725 := by
    simpa [prefixWord, tailWord_7693725, baseEnd_7693725] using wordTrace_append hprefix tailTrace_7693725
  have hstable : (prefixWord ++ tailWord_7693725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693725).length < 2 ^ (prefixWord ++ tailWord_7693725).sum := by decide
  have hdescent : baseEnd_7693725 < baseStart_7693725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693744 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 3, 7]
def baseStart_7693744 : Nat := 118140960795 + 7693744 * 2 ^ 59
def prefixEnd_7693744 : Nat := 4983230072969 + 3 ^ 40 * 7693744 * 2
def baseEnd_7693744 : Nat := 1316862901548483808305707

theorem tailTrace_7693744 : CollatzResearch.WordTrace tailWord_7693744 prefixEnd_7693744 1316862901548483808305707 := by
  unfold tailWord_7693744
  simp only [CollatzResearch.WordTrace]
  refine ⟨140306948519443474854236143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187075931359257966472314857 140306948519443474854236143)
  ·
    refine ⟨210460422779165212281354215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140306948519443474854236143 210460422779165212281354215)
    ·
      refine ⟨315690634168747818422031323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210460422779165212281354215 315690634168747818422031323)
      ·
        refine ⟨473535951253121727633046985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315690634168747818422031323 473535951253121727633046985)
        ·
          refine ⟨355151963439841295724785239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473535951253121727633046985 355151963439841295724785239)
          ·
            refine ⟨532727945159761943587177859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355151963439841295724785239 532727945159761943587177859)
            ·
              refine ⟨799091917739642915380766789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532727945159761943587177859 799091917739642915380766789)
              ·
                refine ⟨149829734576183046633893773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799091917739642915380766789 149829734576183046633893773)
                ·
                  refine ⟨56186150466068642487710165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149829734576183046633893773 56186150466068642487710165)
                  ·
                    refine ⟨1316862901548483808305707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56186150466068642487710165 1316862901548483808305707)
                    ·
                      rfl

theorem cell23_7693744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 3, 7].length) (baseStart_7693744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693744 prefixEnd_7693744 := by exact prefixLift 7693744
  have htrace : WordTrace (prefixWord ++ tailWord_7693744) baseStart_7693744 baseEnd_7693744 := by
    simpa [prefixWord, tailWord_7693744, baseEnd_7693744] using wordTrace_append hprefix tailTrace_7693744
  have hstable : (prefixWord ++ tailWord_7693744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693744).length < 2 ^ (prefixWord ++ tailWord_7693744).sum := by decide
  have hdescent : baseEnd_7693744 < baseStart_7693744 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693825 : List Nat := [1, 2, 4, 1, 4, 1, 1, 2, 3, 4]
def baseStart_7693825 : Nat := 118140960795 + 7693825 * 2 ^ 59
def prefixEnd_7693825 : Nat := 4983230072969 + 3 ^ 40 * 7693825 * 2
def baseEnd_7693825 : Nat := 1316876765526155202668083

theorem tailTrace_7693825 : CollatzResearch.WordTrace tailWord_7693825 prefixEnd_7693825 1316876765526155202668083 := by
  unfold tailWord_7693825
  simp only [CollatzResearch.WordTrace]
  refine ⟨280616851351593500542170929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187077900901062333694780619 280616851351593500542170929)
  ·
    refine ⟨210462638513695125406628197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280616851351593500542170929 210462638513695125406628197)
    ·
      refine ⟨39461744721317836013742787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210462638513695125406628197 39461744721317836013742787)
      ·
        refine ⟨59192617081976754020614181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39461744721317836013742787 59192617081976754020614181)
        ·
          refine ⟨11098615702870641378865159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59192617081976754020614181 11098615702870641378865159)
          ·
            refine ⟨16647923554305962068297739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11098615702870641378865159 16647923554305962068297739)
            ·
              refine ⟨24971885331458943102446609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16647923554305962068297739 24971885331458943102446609)
              ·
                refine ⟨18728913998594207326834957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24971885331458943102446609 18728913998594207326834957)
                ·
                  refine ⟨7023342749472827747563109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18728913998594207326834957 7023342749472827747563109)
                  ·
                    refine ⟨1316876765526155202668083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023342749472827747563109 1316876765526155202668083)
                    ·
                      rfl

theorem cell23_7693825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_7693825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693825 prefixEnd_7693825 := by exact prefixLift 7693825
  have htrace : WordTrace (prefixWord ++ tailWord_7693825) baseStart_7693825 baseEnd_7693825 := by
    simpa [prefixWord, tailWord_7693825, baseEnd_7693825] using wordTrace_append hprefix tailTrace_7693825
  have hstable : (prefixWord ++ tailWord_7693825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693825).length < 2 ^ (prefixWord ++ tailWord_7693825).sum := by decide
  have hdescent : baseEnd_7693825 < baseStart_7693825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693888 : List Nat := [2, 1, 1, 2, 2, 2, 1, 1, 1, 8, 2]
def baseStart_7693888 : Nat := 118140960795 + 7693888 * 2 ^ 59
def prefixEnd_7693888 : Nat := 4983230072969 + 3 ^ 40 * 7693888 * 2
def baseEnd_7693888 : Nat := 3950662645859698861516459

theorem tailTrace_7693888 : CollatzResearch.WordTrace tailWord_7693888 prefixEnd_7693888 3950662645859698861516459 := by
  unfold tailWord_7693888
  simp only [CollatzResearch.WordTrace]
  refine ⟨140309574575182631150857159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187079432766910174867809545 140309574575182631150857159)
  ·
    refine ⟨210464361862773946726285739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140309574575182631150857159 210464361862773946726285739)
    ·
      refine ⟨315696542794160920089428609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210464361862773946726285739 315696542794160920089428609)
      ·
        refine ⟨236772407095620690067071457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315696542794160920089428609 236772407095620690067071457)
        ·
          refine ⟨177579305321715517550303593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236772407095620690067071457 177579305321715517550303593)
          ·
            refine ⟨133184478991286638162727695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177579305321715517550303593 133184478991286638162727695)
            ·
              refine ⟨199776718486929957244091543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133184478991286638162727695 199776718486929957244091543)
              ·
                refine ⟨299665077730394935866137315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199776718486929957244091543 299665077730394935866137315)
                ·
                  refine ⟨449497616595592403799205973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299665077730394935866137315 449497616595592403799205973)
                  ·
                    refine ⟨5267550194479598482021945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 449497616595592403799205973 5267550194479598482021945)
                    ·
                      refine ⟨3950662645859698861516459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267550194479598482021945 3950662645859698861516459)
                      ·
                        rfl

theorem cell23_7693888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 1, 1, 8, 2].length) (baseStart_7693888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693888 prefixEnd_7693888 := by exact prefixLift 7693888
  have htrace : WordTrace (prefixWord ++ tailWord_7693888) baseStart_7693888 baseEnd_7693888 := by
    simpa [prefixWord, tailWord_7693888, baseEnd_7693888] using wordTrace_append hprefix tailTrace_7693888
  have hstable : (prefixWord ++ tailWord_7693888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693888).length < 2 ^ (prefixWord ++ tailWord_7693888).sum := by decide
  have hdescent : baseEnd_7693888 < baseStart_7693888 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693898 : List Nat := [3, 1, 2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_7693898 : Nat := 118140960795 + 7693898 * 2 ^ 59
def prefixEnd_7693898 : Nat := 4983230072969 + 3 ^ 40 * 7693898 * 2
def baseEnd_7693898 : Nat := 1316889260222081274130471

theorem tailTrace_7693898 : CollatzResearch.WordTrace tailWord_7693898 prefixEnd_7693898 1316889260222081274130471 := by
  unfold tailWord_7693898
  simp only [CollatzResearch.WordTrace]
  refine ⟨70154878470082258502394587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187079675920219356006385565 70154878470082258502394587)
  ·
    refine ⟨105232317705123387753591881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70154878470082258502394587 105232317705123387753591881)
    ·
      refine ⟨78924238278842540815193911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105232317705123387753591881 78924238278842540815193911)
      ·
        refine ⟨118386357418263811222790867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78924238278842540815193911 118386357418263811222790867)
        ·
          refine ⟨177579536127395716834186301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118386357418263811222790867 177579536127395716834186301)
          ·
            refine ⟨66592326047773393812819863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177579536127395716834186301 66592326047773393812819863)
            ·
              refine ⟨99888489071660090719229795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66592326047773393812819863 99888489071660090719229795)
              ·
                refine ⟨149832733607490136078844693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99888489071660090719229795 149832733607490136078844693)
                ·
                  refine ⟨7023409387851100128695845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149832733607490136078844693 7023409387851100128695845)
                  ·
                    refine ⟨1316889260222081274130471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023409387851100128695845 1316889260222081274130471)
                    ·
                      rfl

theorem cell23_7693898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_7693898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693898 prefixEnd_7693898 := by exact prefixLift 7693898
  have htrace : WordTrace (prefixWord ++ tailWord_7693898) baseStart_7693898 baseEnd_7693898 := by
    simpa [prefixWord, tailWord_7693898, baseEnd_7693898] using wordTrace_append hprefix tailTrace_7693898
  have hstable : (prefixWord ++ tailWord_7693898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693898).length < 2 ^ (prefixWord ++ tailWord_7693898).sum := by decide
  have hdescent : baseEnd_7693898 < baseStart_7693898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693911 : List Nat := [1, 1, 3, 2, 2, 3, 11]
def baseStart_7693911 : Nat := 118140960795 + 7693911 * 2 ^ 59
def prefixEnd_7693911 : Nat := 4983230072969 + 3 ^ 40 * 7693911 * 2
def baseEnd_7693911 : Nat := 48773758714996941623813

theorem tailTrace_7693911 : CollatzResearch.WordTrace tailWord_7693911 prefixEnd_7693911 48773758714996941623813 := by
  unfold tailWord_7693911
  simp only [CollatzResearch.WordTrace]
  refine ⟨280619988029281937229801587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187079992019521291486534391 280619988029281937229801587)
  ·
    refine ⟨420929982043922905844702381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280619988029281937229801587 420929982043922905844702381)
    ·
      refine ⟨157848743266471089691763393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420929982043922905844702381 157848743266471089691763393)
      ·
        refine ⟨118386557449853317268822545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157848743266471089691763393 118386557449853317268822545)
        ·
          refine ⟨88789918087389987951616909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118386557449853317268822545 88789918087389987951616909)
          ·
            refine ⟨33296219282771245481856341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88789918087389987951616909 33296219282771245481856341)
            ·
              refine ⟨48773758714996941623813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 33296219282771245481856341 48773758714996941623813)
              ·
                rfl

theorem cell23_7693911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 11].length) (baseStart_7693911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693911 prefixEnd_7693911 := by exact prefixLift 7693911
  have htrace : WordTrace (prefixWord ++ tailWord_7693911) baseStart_7693911 baseEnd_7693911 := by
    simpa [prefixWord, tailWord_7693911, baseEnd_7693911] using wordTrace_append hprefix tailTrace_7693911
  have hstable : (prefixWord ++ tailWord_7693911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693911).length < 2 ^ (prefixWord ++ tailWord_7693911).sum := by decide
  have hdescent : baseEnd_7693911 < baseStart_7693911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693916 : List Nat := [2, 2, 4, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_7693916 : Nat := 118140960795 + 7693916 * 2 ^ 59
def prefixEnd_7693916 : Nat := 4983230072969 + 3 ^ 40 * 7693916 * 2
def baseEnd_7693916 : Nat := 3950677023318024751966331

theorem tailTrace_7693916 : CollatzResearch.WordTrace tailWord_7693916 prefixEnd_7693916 3950677023318024751966331 := by
  unfold tailWord_7693916
  simp only [CollatzResearch.WordTrace]
  refine ⟨140310085197131911541866801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187080113596175882055822401 140310085197131911541866801)
  ·
    refine ⟨105232563897848933656400101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140310085197131911541866801 105232563897848933656400101)
    ·
      refine ⟨19731105730846675060575019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105232563897848933656400101 19731105730846675060575019)
      ·
        refine ⟨29596658596270012590862529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19731105730846675060575019 29596658596270012590862529)
        ·
          refine ⟨22197493947202509443146897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29596658596270012590862529 22197493947202509443146897)
          ·
            refine ⟨16648120460401882082360173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22197493947202509443146897 16648120460401882082360173)
            ·
              refine ⟨6243045172650705780885065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16648120460401882082360173 6243045172650705780885065)
              ·
                refine ⟨4682283879488029335663799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243045172650705780885065 4682283879488029335663799)
                ·
                  refine ⟨7023425819232044003495699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682283879488029335663799 7023425819232044003495699)
                  ·
                    refine ⟨10535138728848066005243549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023425819232044003495699 10535138728848066005243549)
                    ·
                      refine ⟨3950677023318024751966331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535138728848066005243549 3950677023318024751966331)
                      ·
                        rfl

theorem cell23_7693916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_7693916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693916 prefixEnd_7693916 := by exact prefixLift 7693916
  have htrace : WordTrace (prefixWord ++ tailWord_7693916) baseStart_7693916 baseEnd_7693916 := by
    simpa [prefixWord, tailWord_7693916, baseEnd_7693916] using wordTrace_append hprefix tailTrace_7693916
  have hstable : (prefixWord ++ tailWord_7693916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693916).length < 2 ^ (prefixWord ++ tailWord_7693916).sum := by decide
  have hdescent : baseEnd_7693916 < baseStart_7693916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693928 : List Nat := [2, 1, 4, 3, 1, 1, 1, 10]
def baseStart_7693928 : Nat := 118140960795 + 7693928 * 2 ^ 59
def prefixEnd_7693928 : Nat := 4983230072969 + 3 ^ 40 * 7693928 * 2
def baseEnd_7693928 : Nat := 146321599447625137222825

theorem tailTrace_7693928 : CollatzResearch.WordTrace tailWord_7693928 prefixEnd_7693928 146321599447625137222825 := by
  unfold tailWord_7693928
  simp only [CollatzResearch.WordTrace]
  refine ⟨140310304035110174566585219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187080405380146899422113625 140310304035110174566585219)
  ·
    refine ⟨210465456052665261849877829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140310304035110174566585219 210465456052665261849877829)
    ·
      refine ⟨39462273009874736596852093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210465456052665261849877829 39462273009874736596852093)
      ·
        refine ⟨14798352378703026223819535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39462273009874736596852093 14798352378703026223819535)
        ·
          refine ⟨22197528568054539335729303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798352378703026223819535 22197528568054539335729303)
          ·
            refine ⟨33296292852081809003593955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22197528568054539335729303 33296292852081809003593955)
            ·
              refine ⟨49944439278122713505390933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33296292852081809003593955 49944439278122713505390933)
              ·
                refine ⟨146321599447625137222825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49944439278122713505390933 146321599447625137222825)
                ·
                  rfl

theorem cell23_7693928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 10].length) (baseStart_7693928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693928 prefixEnd_7693928 := by exact prefixLift 7693928
  have htrace : WordTrace (prefixWord ++ tailWord_7693928) baseStart_7693928 baseEnd_7693928 := by
    simpa [prefixWord, tailWord_7693928, baseEnd_7693928] using wordTrace_append hprefix tailTrace_7693928
  have hstable : (prefixWord ++ tailWord_7693928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693928).length < 2 ^ (prefixWord ++ tailWord_7693928).sum := by decide
  have hdescent : baseEnd_7693928 < baseStart_7693928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693942 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_7693942 : Nat := 118140960795 + 7693942 * 2 ^ 59
def prefixEnd_7693942 : Nat := 4983230072969 + 3 ^ 40 * 7693942 * 2
def baseEnd_7693942 : Nat := 3950690373815041650241211

theorem tailTrace_7693942 : CollatzResearch.WordTrace tailWord_7693942 prefixEnd_7693942 3950690373815041650241211 := by
  unfold tailWord_7693942
  simp only [CollatzResearch.WordTrace]
  refine ⟨17538819918260601845261255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187080745794779753016120053 17538819918260601845261255)
  ·
    refine ⟨26308229877390902767891883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17538819918260601845261255 26308229877390902767891883)
    ·
      refine ⟨39462344816086354151837825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26308229877390902767891883 39462344816086354151837825)
      ·
        refine ⟨29596758612064765613878369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39462344816086354151837825 29596758612064765613878369)
        ·
          refine ⟨22197568959048574210408777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29596758612064765613878369 22197568959048574210408777)
          ·
            refine ⟨16648176719286430657806583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22197568959048574210408777 16648176719286430657806583)
            ·
              refine ⟨24972265078929645986709875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16648176719286430657806583 24972265078929645986709875)
              ·
                refine ⟨37458397618394468980064813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24972265078929645986709875 37458397618394468980064813)
                ·
                  refine ⟨14046899106897925867524305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37458397618394468980064813 14046899106897925867524305)
                  ·
                    refine ⟨10535174330173444400643229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14046899106897925867524305 10535174330173444400643229)
                    ·
                      refine ⟨3950690373815041650241211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535174330173444400643229 3950690373815041650241211)
                      ·
                        rfl

theorem cell23_7693942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_7693942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693942 prefixEnd_7693942 := by exact prefixLift 7693942
  have htrace : WordTrace (prefixWord ++ tailWord_7693942) baseStart_7693942 baseEnd_7693942 := by
    simpa [prefixWord, tailWord_7693942, baseEnd_7693942] using wordTrace_append hprefix tailTrace_7693942
  have hstable : (prefixWord ++ tailWord_7693942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693942).length < 2 ^ (prefixWord ++ tailWord_7693942).sum := by decide
  have hdescent : baseEnd_7693942 < baseStart_7693942 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693951 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_7693951 : Nat := 118140960795 + 7693951 * 2 ^ 59
def prefixEnd_7693951 : Nat := 4983230072969 + 3 ^ 40 * 7693951 * 2
def baseEnd_7693951 : Nat := 3950694995140932115028669

theorem tailTrace_7693951 : CollatzResearch.WordTrace tailWord_7693951 prefixEnd_7693951 3950694995140932115028669 := by
  unfold tailWord_7693951
  simp only [CollatzResearch.WordTrace]
  refine ⟨280621446949137024061257707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187080964632758016040838471 280621446949137024061257707)
  ·
    refine ⟨420932170423705536091886561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280621446949137024061257707 420932170423705536091886561)
    ·
      refine ⟨315699127817779152068914921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420932170423705536091886561 315699127817779152068914921)
      ·
        refine ⟨236774345863334364051686191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315699127817779152068914921 236774345863334364051686191)
        ·
          refine ⟨355161518795001546077529287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236774345863334364051686191 355161518795001546077529287)
          ·
            refine ⟨532742278192502319116293931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355161518795001546077529287 532742278192502319116293931)
            ·
              refine ⟨799113417288753478674440897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532742278192502319116293931 799113417288753478674440897)
              ·
                refine ⟨599335062966565109005830673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799113417288753478674440897 599335062966565109005830673)
                ·
                  refine ⟨449501297224923831754373005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599335062966565109005830673 449501297224923831754373005)
                  ·
                    refine ⟨168562986459346436907889877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449501297224923831754373005 168562986459346436907889877)
                    ·
                      refine ⟨3950694995140932115028669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168562986459346436907889877 3950694995140932115028669)
                      ·
                        rfl

theorem cell23_7693951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_7693951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693951 prefixEnd_7693951 := by exact prefixLift 7693951
  have htrace : WordTrace (prefixWord ++ tailWord_7693951) baseStart_7693951 baseEnd_7693951 := by
    simpa [prefixWord, tailWord_7693951, baseEnd_7693951] using wordTrace_append hprefix tailTrace_7693951
  have hstable : (prefixWord ++ tailWord_7693951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693951).length < 2 ^ (prefixWord ++ tailWord_7693951).sum := by decide
  have hdescent : baseEnd_7693951 < baseStart_7693951 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7693988 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 1, 8]
def baseStart_7693988 : Nat := 118140960795 + 7693988 * 2 ^ 59
def prefixEnd_7693988 : Nat := 4983230072969 + 3 ^ 40 * 7693988 * 2
def baseEnd_7693988 : Nat := 1316904664641716156755333

theorem tailTrace_7693988 : CollatzResearch.WordTrace tailWord_7693988 prefixEnd_7693988 1316904664641716156755333 := by
  unfold tailWord_7693988
  simp only [CollatzResearch.WordTrace]
  refine ⟨140311398225001489690177309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187081864300001986253569745 140311398225001489690177309)
  ·
    refine ⟨52616774334375558633816491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140311398225001489690177309 52616774334375558633816491)
    ·
      refine ⟨78925161501563337950724737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52616774334375558633816491 78925161501563337950724737)
      ·
        refine ⟨59193871126172503463043553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78925161501563337950724737 59193871126172503463043553)
        ·
          refine ⟨44395403344629377597282665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59193871126172503463043553 44395403344629377597282665)
          ·
            refine ⟨33296552508472033197961999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44395403344629377597282665 33296552508472033197961999)
            ·
              refine ⟨49944828762708049796942999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33296552508472033197961999 49944828762708049796942999)
              ·
                refine ⟨74917243144062074695414499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49944828762708049796942999 74917243144062074695414499)
                ·
                  refine ⟨112375864716093112043121749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74917243144062074695414499 112375864716093112043121749)
                  ·
                    refine ⟨1316904664641716156755333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112375864716093112043121749 1316904664641716156755333)
                    ·
                      rfl

theorem cell23_7693988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 1, 8].length) (baseStart_7693988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7693988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7693988 prefixEnd_7693988 := by exact prefixLift 7693988
  have htrace : WordTrace (prefixWord ++ tailWord_7693988) baseStart_7693988 baseEnd_7693988 := by
    simpa [prefixWord, tailWord_7693988, baseEnd_7693988] using wordTrace_append hprefix tailTrace_7693988
  have hstable : (prefixWord ++ tailWord_7693988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7693988).length < 2 ^ (prefixWord ++ tailWord_7693988).sum := by decide
  have hdescent : baseEnd_7693988 < baseStart_7693988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7693988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694012 : List Nat := [2, 2, 2, 3, 1, 2, 2, 2, 1, 4, 2]
def baseStart_7694012 : Nat := 118140960795 + 7694012 * 2 ^ 59
def prefixEnd_7694012 : Nat := 4983230072969 + 3 ^ 40 * 7694012 * 2
def baseEnd_7694012 : Nat := 3950726317460856376365889

theorem tailTrace_7694012 : CollatzResearch.WordTrace tailWord_7694012 prefixEnd_7694012 3950726317460856376365889 := by
  unfold tailWord_7694012
  simp only [CollatzResearch.WordTrace]
  refine ⟨140311835900958015739614145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187082447867944020986152193 140311835900958015739614145)
  ·
    refine ⟨105233876925718511804710609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140311835900958015739614145 105233876925718511804710609)
    ·
      refine ⟨78925407694288883853532957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105233876925718511804710609 78925407694288883853532957)
      ·
        refine ⟨29597027885358331445074859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78925407694288883853532957 29597027885358331445074859)
        ·
          refine ⟨44395541828037497167612289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29597027885358331445074859 44395541828037497167612289)
          ·
            refine ⟨33296656371028122875709217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44395541828037497167612289 33296656371028122875709217)
            ·
              refine ⟨24972492278271092156781913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33296656371028122875709217 24972492278271092156781913)
              ·
                refine ⟨18729369208703319117586435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24972492278271092156781913 18729369208703319117586435)
                ·
                  refine ⟨28094053813054978676379653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18729369208703319117586435 28094053813054978676379653)
                  ·
                    refine ⟨5267635089947808501821185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28094053813054978676379653 5267635089947808501821185)
                    ·
                      refine ⟨3950726317460856376365889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267635089947808501821185 3950726317460856376365889)
                      ·
                        rfl

theorem cell23_7694012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_7694012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694012 prefixEnd_7694012 := by exact prefixLift 7694012
  have htrace : WordTrace (prefixWord ++ tailWord_7694012) baseStart_7694012 baseEnd_7694012 := by
    simpa [prefixWord, tailWord_7694012, baseEnd_7694012] using wordTrace_append hprefix tailTrace_7694012
  have hstable : (prefixWord ++ tailWord_7694012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694012).length < 2 ^ (prefixWord ++ tailWord_7694012).sum := by decide
  have hdescent : baseEnd_7694012 < baseStart_7694012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694048 : List Nat := [2, 1, 1, 3, 1, 2, 3, 2, 1, 7]
def baseStart_7694048 : Nat := 118140960795 + 7694048 * 2 ^ 59
def prefixEnd_7694048 : Nat := 4983230072969 + 3 ^ 40 * 7694048 * 2
def baseEnd_7694048 : Nat := 1316914934254806078505241

theorem tailTrace_7694048 : CollatzResearch.WordTrace tailWord_7694048 prefixEnd_7694048 1316914934254806078505241 := by
  unfold tailWord_7694048
  simp only [CollatzResearch.WordTrace]
  refine ⟨140312492414892804813769399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187083323219857073085025865 140312492414892804813769399)
  ·
    refine ⟨210468738622339207220654099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140312492414892804813769399 210468738622339207220654099)
    ·
      refine ⟨315703107933508810830981149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210468738622339207220654099 315703107933508810830981149)
      ·
        refine ⟨118388665475065804061617931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315703107933508810830981149 118388665475065804061617931)
        ·
          refine ⟨177582998212598706092426897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118388665475065804061617931 177582998212598706092426897)
          ·
            refine ⟨133187248659449029569320173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177582998212598706092426897 133187248659449029569320173)
            ·
              refine ⟨49945218247293386088495065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133187248659449029569320173 49945218247293386088495065)
              ·
                refine ⟨37458913685470039566371299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49945218247293386088495065 37458913685470039566371299)
                ·
                  refine ⟨56188370528205059349556949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37458913685470039566371299 56188370528205059349556949)
                  ·
                    refine ⟨1316914934254806078505241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56188370528205059349556949 1316914934254806078505241)
                    ·
                      rfl

theorem cell23_7694048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 2, 1, 7].length) (baseStart_7694048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694048 prefixEnd_7694048 := by exact prefixLift 7694048
  have htrace : WordTrace (prefixWord ++ tailWord_7694048) baseStart_7694048 baseEnd_7694048 := by
    simpa [prefixWord, tailWord_7694048, baseEnd_7694048] using wordTrace_append hprefix tailTrace_7694048
  have hstable : (prefixWord ++ tailWord_7694048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694048).length < 2 ^ (prefixWord ++ tailWord_7694048).sum := by decide
  have hdescent : baseEnd_7694048 < baseStart_7694048 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694082 : List Nat := [3, 4, 1, 1, 1, 1, 3, 2, 2, 5]
def baseStart_7694082 : Nat := 118140960795 + 7694082 * 2 ^ 59
def prefixEnd_7694082 : Nat := 4983230072969 + 3 ^ 40 * 7694082 * 2
def baseEnd_7694082 : Nat := 1316920753702223700830189

theorem tailTrace_7694082 : CollatzResearch.WordTrace tailWord_7694082 prefixEnd_7694082 1316920753702223700830189 := by
  unfold tailWord_7694082
  simp only [CollatzResearch.WordTrace]
  refine ⟨70156556227915608358569125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187084149941108288956184333 70156556227915608358569125)
  ·
    refine ⟨13154354292734176567231711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70156556227915608358569125 13154354292734176567231711)
    ·
      refine ⟨19731531439101264850847567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13154354292734176567231711 19731531439101264850847567)
      ·
        refine ⟨29597297158651897276271351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19731531439101264850847567 29597297158651897276271351)
        ·
          refine ⟨44395945737977845914407027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29597297158651897276271351 44395945737977845914407027)
          ·
            refine ⟨66593918606966768871610541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44395945737977845914407027 66593918606966768871610541)
            ·
              refine ⟨24972719477612538326853953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66593918606966768871610541 24972719477612538326853953)
              ·
                refine ⟨18729539608209403745140465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24972719477612538326853953 18729539608209403745140465)
                ·
                  refine ⟨14047154706157052808855349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18729539608209403745140465 14047154706157052808855349)
                  ·
                    refine ⟨1316920753702223700830189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14047154706157052808855349 1316920753702223700830189)
                    ·
                      rfl

theorem cell23_7694082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_7694082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694082 prefixEnd_7694082 := by exact prefixLift 7694082
  have htrace : WordTrace (prefixWord ++ tailWord_7694082) baseStart_7694082 baseEnd_7694082 := by
    simpa [prefixWord, tailWord_7694082, baseEnd_7694082] using wordTrace_append hprefix tailTrace_7694082
  have hstable : (prefixWord ++ tailWord_7694082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694082).length < 2 ^ (prefixWord ++ tailWord_7694082).sum := by decide
  have hdescent : baseEnd_7694082 < baseStart_7694082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694095 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 3, 4]
def baseStart_7694095 : Nat := 118140960795 + 7694095 * 2 ^ 59
def prefixEnd_7694095 : Nat := 4983230072969 + 3 ^ 40 * 7694095 * 2
def baseEnd_7694095 : Nat := 1316922978785059850542669

theorem tailTrace_7694095 : CollatzResearch.WordTrace tailWord_7694095 prefixEnd_7694095 1316922978785059850542669 := by
  unfold tailWord_7694095
  simp only [CollatzResearch.WordTrace]
  refine ⟨280626699060615336654499739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187084466040410224436333159 280626699060615336654499739)
  ·
    refine ⟨420940048590923004981749609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280626699060615336654499739 420940048590923004981749609)
    ·
      refine ⟨315705036443192253736312207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420940048590923004981749609 315705036443192253736312207)
      ·
        refine ⟨473557554664788380604468311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315705036443192253736312207 473557554664788380604468311)
        ·
          refine ⟨710336331997182570906702467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473557554664788380604468311 710336331997182570906702467)
          ·
            refine ⟨1065504497995773856360053701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710336331997182570906702467 1065504497995773856360053701)
            ·
              refine ⟨199782093374207598067510069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1065504497995773856360053701 199782093374207598067510069)
              ·
                refine ⟨18729571253831962318829069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199782093374207598067510069 18729571253831962318829069)
                ·
                  refine ⟨7023589220186985869560901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18729571253831962318829069 7023589220186985869560901)
                  ·
                    refine ⟨1316922978785059850542669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023589220186985869560901 1316922978785059850542669)
                    ·
                      rfl

theorem cell23_7694095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_7694095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694095 prefixEnd_7694095 := by exact prefixLift 7694095
  have htrace : WordTrace (prefixWord ++ tailWord_7694095) baseStart_7694095 baseEnd_7694095 := by
    simpa [prefixWord, tailWord_7694095, baseEnd_7694095] using wordTrace_append hprefix tailTrace_7694095
  have hstable : (prefixWord ++ tailWord_7694095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694095).length < 2 ^ (prefixWord ++ tailWord_7694095).sum := by decide
  have hdescent : baseEnd_7694095 < baseStart_7694095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694128 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8]
def baseStart_7694128 : Nat := 118140960795 + 7694128 * 2 ^ 59
def prefixEnd_7694128 : Nat := 4983230072969 + 3 ^ 40 * 7694128 * 2
def baseEnd_7694128 : Nat := 3950785881216777922515355

theorem tailTrace_7694128 : CollatzResearch.WordTrace tailWord_7694128 prefixEnd_7694128 3950785881216777922515355 := by
  unfold tailWord_7694128
  simp only [CollatzResearch.WordTrace]
  refine ⟨140313951334747891645225519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187085268446330522193634025 140313951334747891645225519)
  ·
    refine ⟨210470927002121837467838279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140313951334747891645225519 210470927002121837467838279)
    ·
      refine ⟨315706390503182756201757419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210470927002121837467838279 315706390503182756201757419)
      ·
        refine ⟨473559585754774134302636129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315706390503182756201757419 473559585754774134302636129)
        ·
          refine ⟨355169689316080600726977097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473559585754774134302636129 355169689316080600726977097)
          ·
            refine ⟨266377266987060450545232823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355169689316080600726977097 266377266987060450545232823)
            ·
              refine ⟨399565900480590675817849235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266377266987060450545232823 399565900480590675817849235)
              ·
                refine ⟨599348850720886013726773853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399565900480590675817849235 599348850720886013726773853)
                ·
                  refine ⟨224755819020332255147540195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 599348850720886013726773853 224755819020332255147540195)
                  ·
                    refine ⟨337133728530498382721310293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224755819020332255147540195 337133728530498382721310293)
                    ·
                      refine ⟨3950785881216777922515355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 337133728530498382721310293 3950785881216777922515355)
                      ·
                        rfl

theorem cell23_7694128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_7694128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694128 prefixEnd_7694128 := by exact prefixLift 7694128
  have htrace : WordTrace (prefixWord ++ tailWord_7694128) baseStart_7694128 baseEnd_7694128 := by
    simpa [prefixWord, tailWord_7694128, baseEnd_7694128] using wordTrace_append hprefix tailTrace_7694128
  have hstable : (prefixWord ++ tailWord_7694128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694128).length < 2 ^ (prefixWord ++ tailWord_7694128).sum := by decide
  have hdescent : baseEnd_7694128 < baseStart_7694128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694142 : List Nat := [4, 2, 1, 2, 2, 1, 1, 4, 6]
def baseStart_7694142 : Nat := 118140960795 + 7694142 * 2 ^ 59
def prefixEnd_7694142 : Nat := 4983230072969 + 3 ^ 40 * 7694142 * 2
def baseEnd_7694142 : Nat := 438977007771771207526699

theorem tailTrace_7694142 : CollatzResearch.WordTrace tailWord_7694142 prefixEnd_7694142 438977007771771207526699 := by
  unfold tailWord_7694142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35078551661430632960182585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187085608860963375787640453 35078551661430632960182585)
  ·
    refine ⟨26308913746072974720136939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35078551661430632960182585 26308913746072974720136939)
    ·
      refine ⟨39463370619109462080205409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26308913746072974720136939 39463370619109462080205409)
      ·
        refine ⟨29597527964332096560154057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39463370619109462080205409 29597527964332096560154057)
        ·
          refine ⟨22198145973249072420115543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29597527964332096560154057 22198145973249072420115543)
          ·
            refine ⟨33297218959873608630173315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22198145973249072420115543 33297218959873608630173315)
            ·
              refine ⟨49945828439810412945259973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33297218959873608630173315 49945828439810412945259973)
              ·
                refine ⟨9364842832464452427236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49945828439810412945259973 9364842832464452427236245)
                ·
                  refine ⟨438977007771771207526699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9364842832464452427236245 438977007771771207526699)
                  ·
                    rfl

theorem cell23_7694142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 6].length) (baseStart_7694142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694142 prefixEnd_7694142 := by exact prefixLift 7694142
  have htrace : WordTrace (prefixWord ++ tailWord_7694142) baseStart_7694142 baseEnd_7694142 := by
    simpa [prefixWord, tailWord_7694142, baseEnd_7694142] using wordTrace_append hprefix tailTrace_7694142
  have hstable : (prefixWord ++ tailWord_7694142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694142).length < 2 ^ (prefixWord ++ tailWord_7694142).sum := by decide
  have hdescent : baseEnd_7694142 < baseStart_7694142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694179 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 1, 5, 2]
def baseStart_7694179 : Nat := 118140960795 + 7694179 * 2 ^ 59
def prefixEnd_7694179 : Nat := 4983230072969 + 3 ^ 40 * 7694179 * 2
def baseEnd_7694179 : Nat := 3950812068730157222977621

theorem tailTrace_7694179 : CollatzResearch.WordTrace tailWord_7694179 prefixEnd_7694179 3950812068730157222977621 := by
  unfold tailWord_7694179
  simp only [CollatzResearch.WordTrace]
  refine ⟨280629762792311019000557591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187086508528207346000371727 280629762792311019000557591)
  ·
    refine ⟨420944644188466528500836387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280629762792311019000557591 420944644188466528500836387)
    ·
      refine ⟨631416966282699792751254581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420944644188466528500836387 631416966282699792751254581)
      ·
        refine ⟨59195340589003105570430117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 631416966282699792751254581 59195340589003105570430117)
        ·
          refine ⟨11099126360438082294455647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59195340589003105570430117 11099126360438082294455647)
          ·
            refine ⟨16648689540657123441683471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099126360438082294455647 16648689540657123441683471)
            ·
              refine ⟨24973034310985685162525207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16648689540657123441683471 24973034310985685162525207)
              ·
                refine ⟨37459551466478527743787811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24973034310985685162525207 37459551466478527743787811)
                ·
                  refine ⟨56189327199717791615681717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37459551466478527743787811 56189327199717791615681717)
                  ·
                    refine ⟨5267749424973542963970161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56189327199717791615681717 5267749424973542963970161)
                    ·
                      refine ⟨3950812068730157222977621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267749424973542963970161 3950812068730157222977621)
                      ·
                        rfl

theorem cell23_7694179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_7694179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694179 prefixEnd_7694179 := by exact prefixLift 7694179
  have htrace : WordTrace (prefixWord ++ tailWord_7694179) baseStart_7694179 baseEnd_7694179 := by
    simpa [prefixWord, tailWord_7694179, baseEnd_7694179] using wordTrace_append hprefix tailTrace_7694179
  have hstable : (prefixWord ++ tailWord_7694179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694179).length < 2 ^ (prefixWord ++ tailWord_7694179).sum := by decide
  have hdescent : baseEnd_7694179 < baseStart_7694179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694189 : List Nat := [1, 5, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_7694189 : Nat := 118140960795 + 7694189 * 2 ^ 59
def prefixEnd_7694189 : Nat := 4983230072969 + 3 ^ 40 * 7694189 * 2
def baseEnd_7694189 : Nat := 1316939067845567394617525

theorem tailTrace_7694189 : CollatzResearch.WordTrace tailWord_7694189 prefixEnd_7694189 1316939067845567394617525 := by
  unfold tailWord_7694189
  simp only [CollatzResearch.WordTrace]
  refine ⟨280630127522274790708421621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187086751681516527138947747 280630127522274790708421621)
  ·
    refine ⟨26309074455213261628914527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280630127522274790708421621 26309074455213261628914527)
    ·
      refine ⟨39463611682819892443371791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26309074455213261628914527 39463611682819892443371791)
      ·
        refine ⟨59195417524229838665057687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39463611682819892443371791 59195417524229838665057687)
        ·
          refine ⟨88793126286344757997586531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59195417524229838665057687 88793126286344757997586531)
          ·
            refine ⟨133189689429517136996379797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88793126286344757997586531 133189689429517136996379797)
            ·
              refine ⟨6243266692008615796705303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133189689429517136996379797 6243266692008615796705303)
              ·
                refine ⟨9364900038012923695057955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243266692008615796705303 9364900038012923695057955)
                ·
                  refine ⟨14047350057019385542586933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9364900038012923695057955 14047350057019385542586933)
                  ·
                    refine ⟨1316939067845567394617525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14047350057019385542586933 1316939067845567394617525)
                    ·
                      rfl

theorem cell23_7694189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_7694189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694189 prefixEnd_7694189 := by exact prefixLift 7694189
  have htrace : WordTrace (prefixWord ++ tailWord_7694189) baseStart_7694189 baseEnd_7694189 := by
    simpa [prefixWord, tailWord_7694189, baseEnd_7694189] using wordTrace_append hprefix tailTrace_7694189
  have hstable : (prefixWord ++ tailWord_7694189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694189).length < 2 ^ (prefixWord ++ tailWord_7694189).sum := by decide
  have hdescent : baseEnd_7694189 < baseStart_7694189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694195 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5]
def baseStart_7694195 : Nat := 118140960795 + 7694195 * 2 ^ 59
def prefixEnd_7694195 : Nat := 4983230072969 + 3 ^ 40 * 7694195 * 2
def baseEnd_7694195 : Nat := 3950820284420629160377547

theorem tailTrace_7694195 : CollatzResearch.WordTrace tailWord_7694195 prefixEnd_7694195 3950820284420629160377547 := by
  unfold tailWord_7694195
  simp only [CollatzResearch.WordTrace]
  refine ⟨280630346360253053733140039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187086897573502035822093359 280630346360253053733140039)
  ·
    refine ⟨420945519540379580599710059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280630346360253053733140039 420945519540379580599710059)
    ·
      refine ⟨631418279310569370899565089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420945519540379580599710059 631418279310569370899565089)
      ·
        refine ⟨473563709482927028174673817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631418279310569370899565089 473563709482927028174673817)
        ·
          refine ⟨355172782112195271131005363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473563709482927028174673817 355172782112195271131005363)
          ·
            refine ⟨532759173168292906696508045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355172782112195271131005363 532759173168292906696508045)
            ·
              refine ⟨199784689938109840011190517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532759173168292906696508045 199784689938109840011190517)
              ·
                refine ⟨18729814681697797501049111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199784689938109840011190517 18729814681697797501049111)
                ·
                  refine ⟨28094722022546696251573667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18729814681697797501049111 28094722022546696251573667)
                  ·
                    refine ⟨42142083033820044377360501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28094722022546696251573667 42142083033820044377360501)
                    ·
                      refine ⟨3950820284420629160377547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42142083033820044377360501 3950820284420629160377547)
                      ·
                        rfl

theorem cell23_7694195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_7694195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694195 prefixEnd_7694195 := by exact prefixLift 7694195
  have htrace : WordTrace (prefixWord ++ tailWord_7694195) baseStart_7694195 baseEnd_7694195 := by
    simpa [prefixWord, tailWord_7694195, baseEnd_7694195] using wordTrace_append hprefix tailTrace_7694195
  have hstable : (prefixWord ++ tailWord_7694195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694195).length < 2 ^ (prefixWord ++ tailWord_7694195).sum := by decide
  have hdescent : baseEnd_7694195 < baseStart_7694195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694205 : List Nat := [1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_7694205 : Nat := 118140960795 + 7694205 * 2 ^ 59
def prefixEnd_7694205 : Nat := 4983230072969 + 3 ^ 40 * 7694205 * 2
def baseEnd_7694205 : Nat := 3950825419227174121252501

theorem tailTrace_7694205 : CollatzResearch.WordTrace tailWord_7694205 prefixEnd_7694205 3950825419227174121252501 := by
  unfold tailWord_7694205
  simp only [CollatzResearch.WordTrace]
  refine ⟨280630711090216825441004069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187087140726811216960669379 280630711090216825441004069)
  ·
    refine ⟨52618258329415654770188263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280630711090216825441004069 52618258329415654770188263)
    ·
      refine ⟨78927387494123482155282395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52618258329415654770188263 78927387494123482155282395)
      ·
        refine ⟨118391081241185223232923593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78927387494123482155282395 118391081241185223232923593)
        ·
          refine ⟨88793310930888917424692695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118391081241185223232923593 88793310930888917424692695)
          ·
            refine ⟨133189966396333376137039043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88793310930888917424692695 133189966396333376137039043)
            ·
              refine ⟨199784949594500064205558565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133189966396333376137039043 199784949594500064205558565)
              ·
                refine ⟨37459678048968762038542231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199784949594500064205558565 37459678048968762038542231)
                ·
                  refine ⟨56189517073453143057813347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37459678048968762038542231 56189517073453143057813347)
                  ·
                    refine ⟨84284275610179714586720021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56189517073453143057813347 84284275610179714586720021)
                    ·
                      refine ⟨3950825419227174121252501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84284275610179714586720021 3950825419227174121252501)
                      ·
                        rfl

theorem cell23_7694205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_7694205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694205 prefixEnd_7694205 := by exact prefixLift 7694205
  have htrace : WordTrace (prefixWord ++ tailWord_7694205) baseStart_7694205 baseEnd_7694205 := by
    simpa [prefixWord, tailWord_7694205, baseEnd_7694205] using wordTrace_append hprefix tailTrace_7694205
  have hstable : (prefixWord ++ tailWord_7694205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694205).length < 2 ^ (prefixWord ++ tailWord_7694205).sum := by decide
  have hdescent : baseEnd_7694205 < baseStart_7694205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694212 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_7694212 : Nat := 118140960795 + 7694212 * 2 ^ 59
def prefixEnd_7694212 : Nat := 4983230072969 + 3 ^ 40 * 7694212 * 2
def baseEnd_7694212 : Nat := 3950829013591755593864969

theorem tailTrace_7694212 : CollatzResearch.WordTrace tailWord_7694212 prefixEnd_7694212 3950829013591755593864969 := by
  unfold tailWord_7694212
  simp only [CollatzResearch.WordTrace]
  refine ⟨140315483200595732818254445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187087310934127643757672593 140315483200595732818254445)
  ·
    refine ⟨52618306200223399806845417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140315483200595732818254445 52618306200223399806845417)
    ·
      refine ⟨39463729650167549855134063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52618306200223399806845417 39463729650167549855134063)
      ·
        refine ⟨59195594475251324782701095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39463729650167549855134063 59195594475251324782701095)
        ·
          refine ⟨88793391712876987174051643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59195594475251324782701095 88793391712876987174051643)
          ·
            refine ⟨133190087569315480761077465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88793391712876987174051643 133190087569315480761077465)
            ·
              refine ⟨99892565676986610570808099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133190087569315480761077465 99892565676986610570808099)
              ·
                refine ⟨149838848515479915856212149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99892565676986610570808099 149838848515479915856212149)
                ·
                  refine ⟨14047392048326242111519889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149838848515479915856212149 14047392048326242111519889)
                  ·
                    refine ⟨10535544036244681583639917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14047392048326242111519889 10535544036244681583639917)
                    ·
                      refine ⟨3950829013591755593864969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535544036244681583639917 3950829013591755593864969)
                      ·
                        rfl

theorem cell23_7694212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_7694212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694212 prefixEnd_7694212 := by exact prefixLift 7694212
  have htrace : WordTrace (prefixWord ++ tailWord_7694212) baseStart_7694212 baseEnd_7694212 := by
    simpa [prefixWord, tailWord_7694212, baseEnd_7694212] using wordTrace_append hprefix tailTrace_7694212
  have hstable : (prefixWord ++ tailWord_7694212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694212).length < 2 ^ (prefixWord ++ tailWord_7694212).sum := by decide
  have hdescent : baseEnd_7694212 < baseStart_7694212 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694226 : List Nat := [3, 2, 3, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_7694226 : Nat := 118140960795 + 7694226 * 2 ^ 59
def prefixEnd_7694226 : Nat := 4983230072969 + 3 ^ 40 * 7694226 * 2
def baseEnd_7694226 : Nat := 3950836202320918539089905

theorem tailTrace_7694226 : CollatzResearch.WordTrace tailWord_7694226 prefixEnd_7694226 3950836202320918539089905 := by
  unfold tailWord_7694226
  simp only [CollatzResearch.WordTrace]
  refine ⟨70157869255785186506879633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187087651348760497351679021 70157869255785186506879633)
  ·
    refine ⟨52618401941838889880159725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70157869255785186506879633 52618401941838889880159725)
    ·
      refine ⟨19731900728189583705059897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52618401941838889880159725 19731900728189583705059897)
      ·
        refine ⟨14798925546142187778794923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19731900728189583705059897 14798925546142187778794923)
        ·
          refine ⟨22198388319213281668192385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14798925546142187778794923 22198388319213281668192385)
          ·
            refine ⟨16648791239409961251144289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22198388319213281668192385 16648791239409961251144289)
            ·
              refine ⟨12486593429557470938358217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16648791239409961251144289 12486593429557470938358217)
              ·
                refine ⟨9364945072168103203768663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12486593429557470938358217 9364945072168103203768663)
                ·
                  refine ⟨14047417608252154805652995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9364945072168103203768663 14047417608252154805652995)
                  ·
                    refine ⟨21071126412378232208479493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14047417608252154805652995 21071126412378232208479493)
                    ·
                      refine ⟨3950836202320918539089905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21071126412378232208479493 3950836202320918539089905)
                      ·
                        rfl

theorem cell23_7694226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_7694226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694226 prefixEnd_7694226 := by exact prefixLift 7694226
  have htrace : WordTrace (prefixWord ++ tailWord_7694226) baseStart_7694226 baseEnd_7694226 := by
    simpa [prefixWord, tailWord_7694226, baseEnd_7694226] using wordTrace_append hprefix tailTrace_7694226
  have hstable : (prefixWord ++ tailWord_7694226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694226).length < 2 ^ (prefixWord ++ tailWord_7694226).sum := by decide
  have hdescent : baseEnd_7694226 < baseStart_7694226 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694229 : List Nat := [1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_7694229 : Nat := 118140960795 + 7694229 * 2 ^ 59
def prefixEnd_7694229 : Nat := 4983230072969 + 3 ^ 40 * 7694229 * 2
def baseEnd_7694229 : Nat := 3950837742762882027352391

theorem tailTrace_7694229 : CollatzResearch.WordTrace tailWord_7694229 prefixEnd_7694229 3950837742762882027352391 := by
  unfold tailWord_7694229
  simp only [CollatzResearch.WordTrace]
  refine ⟨280631586442129877539877741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187087724294753251693251827 280631586442129877539877741)
  ·
    refine ⟨105236844915798704077454153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280631586442129877539877741 105236844915798704077454153)
    ·
      refine ⟨78927633686849028058090615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105236844915798704077454153 78927633686849028058090615)
      ·
        refine ⟨118391450530273542087135923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78927633686849028058090615 118391450530273542087135923)
        ·
          refine ⟨177587175795410313130703885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118391450530273542087135923 177587175795410313130703885)
          ·
            refine ⟨66595190923278867424013957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177587175795410313130703885 66595190923278867424013957)
            ·
              refine ⟨12486598298114787642002617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66595190923278867424013957 12486598298114787642002617)
              ·
                refine ⟨9364948723586090731501963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12486598298114787642002617 9364948723586090731501963)
                ·
                  refine ⟨14047423085379136097252945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9364948723586090731501963 14047423085379136097252945)
                  ·
                    refine ⟨10535567314034352072939709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14047423085379136097252945 10535567314034352072939709)
                    ·
                      refine ⟨3950837742762882027352391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535567314034352072939709 3950837742762882027352391)
                      ·
                        rfl

theorem cell23_7694229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_7694229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694229 prefixEnd_7694229 := by exact prefixLift 7694229
  have htrace : WordTrace (prefixWord ++ tailWord_7694229) baseStart_7694229 baseEnd_7694229 := by
    simpa [prefixWord, tailWord_7694229, baseEnd_7694229] using wordTrace_append hprefix tailTrace_7694229
  have hstable : (prefixWord ++ tailWord_7694229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694229).length < 2 ^ (prefixWord ++ tailWord_7694229).sum := by decide
  have hdescent : baseEnd_7694229 < baseStart_7694229 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694254 : List Nat := [4, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_7694254 : Nat := 118140960795 + 7694254 * 2 ^ 59
def prefixEnd_7694254 : Nat := 4983230072969 + 3 ^ 40 * 7694254 * 2
def baseEnd_7694254 : Nat := 3950850579779244429539777

theorem tailTrace_7694254 : CollatzResearch.WordTrace tailWord_7694254 prefixEnd_7694254 3950850579779244429539777 := by
  unfold tailWord_7694254
  simp only [CollatzResearch.WordTrace]
  refine ⟨35079062283379913351192227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187088332178026204539691877 35079062283379913351192227)
  ·
    refine ⟨52618593425069870026788341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35079062283379913351192227 52618593425069870026788341)
    ·
      refine ⟨4932993133600300315011407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 52618593425069870026788341 4932993133600300315011407)
      ·
        refine ⟨7399489700400450472517111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4932993133600300315011407 7399489700400450472517111)
        ·
          refine ⟨11099234550600675708775667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399489700400450472517111 11099234550600675708775667)
          ·
            refine ⟨16648851825901013563163501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099234550600675708775667 16648851825901013563163501)
            ·
              refine ⟨6243319434712880086186313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16648851825901013563163501 6243319434712880086186313)
              ·
                refine ⟨4682489576034660064639735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243319434712880086186313 4682489576034660064639735)
                ·
                  refine ⟨7023734364051990096959603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682489576034660064639735 7023734364051990096959603)
                  ·
                    refine ⟨10535601546077985145439405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023734364051990096959603 10535601546077985145439405)
                    ·
                      refine ⟨3950850579779244429539777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535601546077985145439405 3950850579779244429539777)
                      ·
                        rfl

theorem cell23_7694254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_7694254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694254 prefixEnd_7694254 := by exact prefixLift 7694254
  have htrace : WordTrace (prefixWord ++ tailWord_7694254) baseStart_7694254 baseEnd_7694254 := by
    simpa [prefixWord, tailWord_7694254, baseEnd_7694254] using wordTrace_append hprefix tailTrace_7694254
  have hstable : (prefixWord ++ tailWord_7694254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694254).length < 2 ^ (prefixWord ++ tailWord_7694254).sum := by decide
  have hdescent : baseEnd_7694254 < baseStart_7694254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694255 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_7694255 : Nat := 118140960795 + 7694255 * 2 ^ 59
def prefixEnd_7694255 : Nat := 4983230072969 + 3 ^ 40 * 7694255 * 2
def baseEnd_7694255 : Nat := 3950851093259898925627271

theorem tailTrace_7694255 : CollatzResearch.WordTrace tailWord_7694255 prefixEnd_7694255 3950851093259898925627271 := by
  unfold tailWord_7694255
  simp only [CollatzResearch.WordTrace]
  refine ⟨280632534740035683980324219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187088356493357122653549479 280632534740035683980324219)
  ·
    refine ⟨420948802110053525970486329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280632534740035683980324219 420948802110053525970486329)
    ·
      refine ⟨315711601582540144477864747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420948802110053525970486329 315711601582540144477864747)
      ·
        refine ⟨473567402373810216716797121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315711601582540144477864747 473567402373810216716797121)
        ·
          refine ⟨355175551780357662537597841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473567402373810216716797121 355175551780357662537597841)
          ·
            refine ⟨266381663835268246903198381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355175551780357662537597841 266381663835268246903198381)
            ·
              refine ⟨99893123938225592588699393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266381663835268246903198381 99893123938225592588699393)
              ·
                refine ⟨74919842953669194441524545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99893123938225592588699393 74919842953669194441524545)
                ·
                  refine ⟨56189882215251895831143409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74919842953669194441524545 56189882215251895831143409)
                  ·
                    refine ⟨42142411661438921873357557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56189882215251895831143409 42142411661438921873357557)
                    ·
                      refine ⟨3950851093259898925627271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42142411661438921873357557 3950851093259898925627271)
                      ·
                        rfl

theorem cell23_7694255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_7694255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694255 prefixEnd_7694255 := by exact prefixLift 7694255
  have htrace : WordTrace (prefixWord ++ tailWord_7694255) baseStart_7694255 baseEnd_7694255 := by
    simpa [prefixWord, tailWord_7694255, baseEnd_7694255] using wordTrace_append hprefix tailTrace_7694255
  have hstable : (prefixWord ++ tailWord_7694255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694255).length < 2 ^ (prefixWord ++ tailWord_7694255).sum := by decide
  have hdescent : baseEnd_7694255 < baseStart_7694255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694259 : List Nat := [1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 3]
def baseStart_7694259 : Nat := 118140960795 + 7694259 * 2 ^ 59
def prefixEnd_7694259 : Nat := 4983230072969 + 3 ^ 40 * 7694259 * 2
def baseEnd_7694259 : Nat := 3950853147182516909977253

theorem tailTrace_7694259 : CollatzResearch.WordTrace tailWord_7694259 prefixEnd_7694259 3950853147182516909977253 := by
  unfold tailWord_7694259
  simp only [CollatzResearch.WordTrace]
  refine ⟨280632680632021192663469831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187088453754680795108979887 280632680632021192663469831)
  ·
    refine ⟨420949020948031788995204747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280632680632021192663469831 420949020948031788995204747)
    ·
      refine ⟨631423531422047683492807121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420949020948031788995204747 631423531422047683492807121)
      ·
        refine ⟨473567648566535762619605341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631423531422047683492807121 473567648566535762619605341)
        ·
          refine ⟨177587868212450910982352003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473567648566535762619605341 177587868212450910982352003)
          ·
            refine ⟨266381802318676366473528005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177587868212450910982352003 266381802318676366473528005)
            ·
              refine ⟨49946587934751818713786501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266381802318676366473528005 49946587934751818713786501)
              ·
                refine ⟨9364985237765966008834969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49946587934751818713786501 9364985237765966008834969)
                ·
                  refine ⟨7023738928324474506626227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9364985237765966008834969 7023738928324474506626227)
                  ·
                    refine ⟨10535608392486711759939341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023738928324474506626227 10535608392486711759939341)
                    ·
                      refine ⟨3950853147182516909977253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535608392486711759939341 3950853147182516909977253)
                      ·
                        rfl

theorem cell23_7694259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_7694259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694259 prefixEnd_7694259 := by exact prefixLift 7694259
  have htrace : WordTrace (prefixWord ++ tailWord_7694259) baseStart_7694259 baseEnd_7694259 := by
    simpa [prefixWord, tailWord_7694259, baseEnd_7694259] using wordTrace_append hprefix tailTrace_7694259
  have hstable : (prefixWord ++ tailWord_7694259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694259).length < 2 ^ (prefixWord ++ tailWord_7694259).sum := by decide
  have hdescent : baseEnd_7694259 < baseStart_7694259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694303 : List Nat := [1, 1, 2, 3, 4, 2, 3, 1, 1, 3, 2]
def baseStart_7694303 : Nat := 118140960795 + 7694303 * 2 ^ 59
def prefixEnd_7694303 : Nat := 4983230072969 + 3 ^ 40 * 7694303 * 2
def baseEnd_7694303 : Nat := 3950875740331314737827051

theorem tailTrace_7694303 : CollatzResearch.WordTrace tailWord_7694303 prefixEnd_7694303 3950875740331314737827051 := by
  unfold tailWord_7694303
  simp only [CollatzResearch.WordTrace]
  refine ⟨280634285443861788178071563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187089523629241192118714375 280634285443861788178071563)
  ·
    refine ⟨420951428165792682267107345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280634285443861788178071563 420951428165792682267107345)
    ·
      refine ⟨315713571124344511700330509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420951428165792682267107345 315713571124344511700330509)
      ·
        refine ⟨118392589171629191887623941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315713571124344511700330509 118392589171629191887623941)
        ·
          refine ⟨22198610469680473478929489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118392589171629191887623941 22198610469680473478929489)
          ·
            refine ⟨16648957852260355109197117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22198610469680473478929489 16648957852260355109197117)
            ·
              refine ⟨6243359194597633165948919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16648957852260355109197117 6243359194597633165948919)
              ·
                refine ⟨9365038791896449748923379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243359194597633165948919 9365038791896449748923379)
                ·
                  refine ⟨14047558187844674623385069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365038791896449748923379 14047558187844674623385069)
                  ·
                    refine ⟨5267834320441752983769401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14047558187844674623385069 5267834320441752983769401)
                    ·
                      refine ⟨3950875740331314737827051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267834320441752983769401 3950875740331314737827051)
                      ·
                        rfl

theorem cell23_7694303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_7694303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694303 prefixEnd_7694303 := by exact prefixLift 7694303
  have htrace : WordTrace (prefixWord ++ tailWord_7694303) baseStart_7694303 baseEnd_7694303 := by
    simpa [prefixWord, tailWord_7694303, baseEnd_7694303] using wordTrace_append hprefix tailTrace_7694303
  have hstable : (prefixWord ++ tailWord_7694303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694303).length < 2 ^ (prefixWord ++ tailWord_7694303).sum := by decide
  have hdescent : baseEnd_7694303 < baseStart_7694303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694312 : List Nat := [2, 1, 4, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7694312 : Nat := 118140960795 + 7694312 * 2 ^ 59
def prefixEnd_7694312 : Nat := 4983230072969 + 3 ^ 40 * 7694312 * 2
def baseEnd_7694312 : Nat := 3950880361657205202614509

theorem tailTrace_7694312 : CollatzResearch.WordTrace tailWord_7694312 prefixEnd_7694312 3950880361657205202614509 := by
  unfold tailWord_7694312
  simp only [CollatzResearch.WordTrace]
  refine ⟨140317306850414591357574595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187089742467219455143432793 140317306850414591357574595)
  ·
    refine ⟨210475960275621887036361893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140317306850414591357574595 210475960275621887036361893)
    ·
      refine ⟨39464242551679103819317855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210475960275621887036361893 39464242551679103819317855)
      ·
        refine ⟨59196363827518655728976783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39464242551679103819317855 59196363827518655728976783)
        ·
          refine ⟨88794545741277983593465175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59196363827518655728976783 88794545741277983593465175)
          ·
            refine ⟨133191818611916975390197763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88794545741277983593465175 133191818611916975390197763)
            ·
              refine ⟨199787727917875463085296645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133191818611916975390197763 199787727917875463085296645)
              ·
                refine ⟨37460198984601649328493121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199787727917875463085296645 37460198984601649328493121)
                ·
                  refine ⟨28095149238451236996369841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37460198984601649328493121 28095149238451236996369841)
                  ·
                    refine ⟨21071361928838427747277381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28095149238451236996369841 21071361928838427747277381)
                    ·
                      refine ⟨3950880361657205202614509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21071361928838427747277381 3950880361657205202614509)
                      ·
                        rfl

theorem cell23_7694312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7694312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694312 prefixEnd_7694312 := by exact prefixLift 7694312
  have htrace : WordTrace (prefixWord ++ tailWord_7694312) baseStart_7694312 baseEnd_7694312 := by
    simpa [prefixWord, tailWord_7694312, baseEnd_7694312] using wordTrace_append hprefix tailTrace_7694312
  have hstable : (prefixWord ++ tailWord_7694312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694312).length < 2 ^ (prefixWord ++ tailWord_7694312).sum := by decide
  have hdescent : baseEnd_7694312 < baseStart_7694312 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694315 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_7694315 : Nat := 118140960795 + 7694315 * 2 ^ 59
def prefixEnd_7694315 : Nat := 4983230072969 + 3 ^ 40 * 7694315 * 2
def baseEnd_7694315 : Nat := 3950881902099168690876995

theorem tailTrace_7694315 : CollatzResearch.WordTrace tailWord_7694315 prefixEnd_7694315 3950881902099168690876995 := by
  unfold tailWord_7694315
  simp only [CollatzResearch.WordTrace]
  refine ⟨280634723119818314227508399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187089815413212209485005599 280634723119818314227508399)
  ·
    refine ⟨420952084679727471341262599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280634723119818314227508399 420952084679727471341262599)
    ·
      refine ⟨631428127019591207011893899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420952084679727471341262599 631428127019591207011893899)
      ·
        refine ⟨947142190529386810517840849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631428127019591207011893899 947142190529386810517840849)
        ·
          refine ⟨710356642897040107888380637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947142190529386810517840849 710356642897040107888380637)
          ·
            refine ⟨266383741086390040458142739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710356642897040107888380637 266383741086390040458142739)
            ·
              refine ⟨399575611629585060687214109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266383741086390040458142739 399575611629585060687214109)
              ·
                refine ⟨149840854361094397757705291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399575611629585060687214109 149840854361094397757705291)
                ·
                  refine ⟨224761281541641596636557937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149840854361094397757705291 224761281541641596636557937)
                  ·
                    refine ⟨168570961156231197477418453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224761281541641596636557937 168570961156231197477418453)
                    ·
                      refine ⟨3950881902099168690876995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168570961156231197477418453 3950881902099168690876995)
                      ·
                        rfl

theorem cell23_7694315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_7694315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694315 prefixEnd_7694315 := by exact prefixLift 7694315
  have htrace : WordTrace (prefixWord ++ tailWord_7694315) baseStart_7694315 baseEnd_7694315 := by
    simpa [prefixWord, tailWord_7694315, baseEnd_7694315] using wordTrace_append hprefix tailTrace_7694315
  have hstable : (prefixWord ++ tailWord_7694315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694315).length < 2 ^ (prefixWord ++ tailWord_7694315).sum := by decide
  have hdescent : baseEnd_7694315 < baseStart_7694315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694399 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 3, 4]
def baseStart_7694399 : Nat := 118140960795 + 7694399 * 2 ^ 59
def prefixEnd_7694399 : Nat := 4983230072969 + 3 ^ 40 * 7694399 * 2
def baseEnd_7694399 : Nat := 1316975011491382120742203

theorem tailTrace_7694399 : CollatzResearch.WordTrace tailWord_7694399 prefixEnd_7694399 1316975011491382120742203 := by
  unfold tailWord_7694399
  simp only [CollatzResearch.WordTrace]
  refine ⟨280637786851513996573566251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187091857901009331049044167 280637786851513996573566251)
  ·
    refine ⟨420956680277270994860349377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280637786851513996573566251 420956680277270994860349377)
    ·
      refine ⟨315717510207953246145262033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420956680277270994860349377 315717510207953246145262033)
      ·
        refine ⟨236788132655964934608946525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315717510207953246145262033 236788132655964934608946525)
        ·
          refine ⟨88795549745986850478354947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236788132655964934608946525 88795549745986850478354947)
          ·
            refine ⟨133193324618980275717532421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88795549745986850478354947 133193324618980275717532421)
            ·
              refine ⟨24973748366058801697037329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133193324618980275717532421 24973748366058801697037329)
              ·
                refine ⟨18730311274544101272777997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24973748366058801697037329 18730311274544101272777997)
                ·
                  refine ⟨7023866727954037977291749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18730311274544101272777997 7023866727954037977291749)
                  ·
                    refine ⟨1316975011491382120742203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023866727954037977291749 1316975011491382120742203)
                    ·
                      rfl

theorem cell23_7694399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_7694399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694399 prefixEnd_7694399 := by exact prefixLift 7694399
  have htrace : WordTrace (prefixWord ++ tailWord_7694399) baseStart_7694399 baseEnd_7694399 := by
    simpa [prefixWord, tailWord_7694399, baseEnd_7694399] using wordTrace_append hprefix tailTrace_7694399
  have hstable : (prefixWord ++ tailWord_7694399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694399).length < 2 ^ (prefixWord ++ tailWord_7694399).sum := by decide
  have hdescent : baseEnd_7694399 < baseStart_7694399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694406 : List Nat := [6, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_7694406 : Nat := 118140960795 + 7694406 * 2 ^ 59
def prefixEnd_7694406 : Nat := 4983230072969 + 3 ^ 40 * 7694406 * 2
def baseEnd_7694406 : Nat := 3950928628838727834839077

theorem tailTrace_7694406 : CollatzResearch.WordTrace tailWord_7694406 prefixEnd_7694406 3950928628838727834839077 := by
  unfold tailWord_7694406
  simp only [CollatzResearch.WordTrace]
  refine ⟨8769938817577769899033471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187092028108325757846047381 8769938817577769899033471)
  ·
    refine ⟨13154908226366654848550207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8769938817577769899033471 13154908226366654848550207)
    ·
      refine ⟨19732362339549982272825311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13154908226366654848550207 19732362339549982272825311)
      ·
        refine ⟨29598543509324973409237967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19732362339549982272825311 29598543509324973409237967)
        ·
          refine ⟨44397815263987460113856951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29598543509324973409237967 44397815263987460113856951)
          ·
            refine ⟨66596722895981190170785427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44397815263987460113856951 66596722895981190170785427)
            ·
              refine ⟨99895084343971785256178141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66596722895981190170785427 99895084343971785256178141)
              ·
                refine ⟨37460656628989419471066803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99895084343971785256178141 37460656628989419471066803)
                ·
                  refine ⟨56190984943484129206600205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37460656628989419471066803 56190984943484129206600205)
                  ·
                    refine ⟨21071619353806548452475077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56190984943484129206600205 21071619353806548452475077)
                    ·
                      refine ⟨3950928628838727834839077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21071619353806548452475077 3950928628838727834839077)
                      ·
                        rfl

theorem cell23_7694406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_7694406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694406 prefixEnd_7694406 := by exact prefixLift 7694406
  have htrace : WordTrace (prefixWord ++ tailWord_7694406) baseStart_7694406 baseEnd_7694406 := by
    simpa [prefixWord, tailWord_7694406, baseEnd_7694406] using wordTrace_append hprefix tailTrace_7694406
  have hstable : (prefixWord ++ tailWord_7694406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694406).length < 2 ^ (prefixWord ++ tailWord_7694406).sum := by decide
  have hdescent : baseEnd_7694406 < baseStart_7694406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694409 : List Nat := [1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_7694409 : Nat := 118140960795 + 7694409 * 2 ^ 59
def prefixEnd_7694409 : Nat := 4983230072969 + 3 ^ 40 * 7694409 * 2
def baseEnd_7694409 : Nat := 3950930169280691323101563

theorem tailTrace_7694409 : CollatzResearch.WordTrace tailWord_7694409 prefixEnd_7694409 3950930169280691323101563 := by
  unfold tailWord_7694409
  simp only [CollatzResearch.WordTrace]
  refine ⟨280638151581477768281430281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187092101054318512187620187 280638151581477768281430281)
  ·
    refine ⟨210478613686108326211072711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280638151581477768281430281 210478613686108326211072711)
    ·
      refine ⟨315717920529162489316609067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210478613686108326211072711 315717920529162489316609067)
      ·
        refine ⟨473576880793743733974913601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315717920529162489316609067 473576880793743733974913601)
        ·
          refine ⟨355182660595307800481185201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473576880793743733974913601 355182660595307800481185201)
          ·
            refine ⟨266386995446480850360888901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355182660595307800481185201 266386995446480850360888901)
            ·
              refine ⟨49947561646215159442666669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266386995446480850360888901 49947561646215159442666669)
              ·
                refine ⟨18730335617330684791000001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49947561646215159442666669 18730335617330684791000001)
                ·
                  refine ⟨14047751712998013593250001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18730335617330684791000001 14047751712998013593250001)
                  ·
                    refine ⟨10535813784748510194937501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14047751712998013593250001 10535813784748510194937501)
                    ·
                      refine ⟨3950930169280691323101563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535813784748510194937501 3950930169280691323101563)
                      ·
                        rfl

theorem cell23_7694409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_7694409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694409 prefixEnd_7694409 := by exact prefixLift 7694409
  have htrace : WordTrace (prefixWord ++ tailWord_7694409) baseStart_7694409 baseEnd_7694409 := by
    simpa [prefixWord, tailWord_7694409, baseEnd_7694409] using wordTrace_append hprefix tailTrace_7694409
  have hstable : (prefixWord ++ tailWord_7694409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694409).length < 2 ^ (prefixWord ++ tailWord_7694409).sum := by decide
  have hdescent : baseEnd_7694409 < baseStart_7694409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694412 : List Nat := [2, 2, 1, 3, 1, 1, 3, 2, 8]
def baseStart_7694412 : Nat := 118140960795 + 7694412 * 2 ^ 59
def prefixEnd_7694412 : Nat := 4983230072969 + 3 ^ 40 * 7694412 * 2
def baseEnd_7694412 : Nat := 438992412191406090151561

theorem tailTrace_7694412 : CollatzResearch.WordTrace tailWord_7694412 prefixEnd_7694412 438992412191406090151561 := by
  unfold tailWord_7694412
  simp only [CollatzResearch.WordTrace]
  refine ⟨140319130500233449896894745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187092174000311266529192993 140319130500233449896894745)
  ·
    refine ⟨105239347875175087422671059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140319130500233449896894745 105239347875175087422671059)
    ·
      refine ⟨157859021812762631134006589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105239347875175087422671059 157859021812762631134006589)
      ·
        refine ⟨59197133179785986675252471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157859021812762631134006589 59197133179785986675252471)
        ·
          refine ⟨88795699769678980012878707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59197133179785986675252471 88795699769678980012878707)
          ·
            refine ⟨133193549654518470019318061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88795699769678980012878707 133193549654518470019318061)
            ·
              refine ⟨49947581120444426257244273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133193549654518470019318061 49947581120444426257244273)
              ·
                refine ⟨37460685840333319692933205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49947581120444426257244273 37460685840333319692933205)
                ·
                  refine ⟨438992412191406090151561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37460685840333319692933205 438992412191406090151561)
                  ·
                    rfl

theorem cell23_7694412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_7694412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694412 prefixEnd_7694412 := by exact prefixLift 7694412
  have htrace : WordTrace (prefixWord ++ tailWord_7694412) baseStart_7694412 baseEnd_7694412 := by
    simpa [prefixWord, tailWord_7694412, baseEnd_7694412] using wordTrace_append hprefix tailTrace_7694412
  have hstable : (prefixWord ++ tailWord_7694412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694412).length < 2 ^ (prefixWord ++ tailWord_7694412).sum := by decide
  have hdescent : baseEnd_7694412 < baseStart_7694412 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694473 : List Nat := [1, 2, 1, 1, 4, 2, 2, 5, 1, 1, 3]
def baseStart_7694473 : Nat := 118140960795 + 7694473 * 2 ^ 59
def prefixEnd_7694473 : Nat := 4983230072969 + 3 ^ 40 * 7694473 * 2
def baseEnd_7694473 : Nat := 3950963032042579072701269

theorem tailTrace_7694473 : CollatzResearch.WordTrace tailWord_7694473 prefixEnd_7694473 3950963032042579072701269 := by
  unfold tailWord_7694473
  simp only [CollatzResearch.WordTrace]
  refine ⟨280640485853245907211760073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187093657235497271474506715 280640485853245907211760073)
  ·
    refine ⟨210480364389934430408820055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280640485853245907211760073 210480364389934430408820055)
    ·
      refine ⟨315720546584901645613230083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210480364389934430408820055 315720546584901645613230083)
      ·
        refine ⟨473580819877352468419845125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315720546584901645613230083 473580819877352468419845125)
        ·
          refine ⟨88796403727003587828720961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473580819877352468419845125 88796403727003587828720961)
          ·
            refine ⟨66597302795252690871540721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88796403727003587828720961 66597302795252690871540721)
            ·
              refine ⟨49947977096439518153655541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66597302795252690871540721 49947977096439518153655541)
              ·
                refine ⟨4682622852791204826905207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49947977096439518153655541 4682622852791204826905207)
                ·
                  refine ⟨7023934279186807240357811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682622852791204826905207 7023934279186807240357811)
                  ·
                    refine ⟨10535901418780210860536717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7023934279186807240357811 10535901418780210860536717)
                    ·
                      refine ⟨3950963032042579072701269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535901418780210860536717 3950963032042579072701269)
                      ·
                        rfl

theorem cell23_7694473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 5, 1, 1, 3].length) (baseStart_7694473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694473 prefixEnd_7694473 := by exact prefixLift 7694473
  have htrace : WordTrace (prefixWord ++ tailWord_7694473) baseStart_7694473 baseEnd_7694473 := by
    simpa [prefixWord, tailWord_7694473, baseEnd_7694473] using wordTrace_append hprefix tailTrace_7694473
  have hstable : (prefixWord ++ tailWord_7694473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694473).length < 2 ^ (prefixWord ++ tailWord_7694473).sum := by decide
  have hdescent : baseEnd_7694473 < baseStart_7694473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694484 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_7694484 : Nat := 118140960795 + 7694484 * 2 ^ 59
def prefixEnd_7694484 : Nat := 4983230072969 + 3 ^ 40 * 7694484 * 2
def baseEnd_7694484 : Nat := 1316989560109926176554573

theorem tailTrace_7694484 : CollatzResearch.WordTrace tailWord_7694484 prefixEnd_7694484 1316989560109926176554573 := by
  unfold tailWord_7694484
  simp only [CollatzResearch.WordTrace]
  refine ⟨140320443528103028045205253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187093924704137370726940337 140320443528103028045205253)
  ·
    refine ⟨26310083161519317758475985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140320443528103028045205253 26310083161519317758475985)
    ·
      refine ⟨19732562371139488318856989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26310083161519317758475985 19732562371139488318856989)
      ·
        refine ⟨7399710889177308119571371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19732562371139488318856989 7399710889177308119571371)
        ·
          refine ⟨11099566333765962179357057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399710889177308119571371 11099566333765962179357057)
          ·
            refine ⟨8324674750324471634517793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11099566333765962179357057 8324674750324471634517793)
            ·
              refine ⟨6243506062743353725888345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8324674750324471634517793 6243506062743353725888345)
              ·
                refine ⟨4682629547057515294416259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243506062743353725888345 4682629547057515294416259)
                ·
                  refine ⟨7023944320586272941624389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682629547057515294416259 7023944320586272941624389)
                  ·
                    refine ⟨1316989560109926176554573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023944320586272941624389 1316989560109926176554573)
                    ·
                      rfl

theorem cell23_7694484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_7694484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694484 prefixEnd_7694484 := by exact prefixLift 7694484
  have htrace : WordTrace (prefixWord ++ tailWord_7694484) baseStart_7694484 baseEnd_7694484 := by
    simpa [prefixWord, tailWord_7694484, baseEnd_7694484] using wordTrace_append hprefix tailTrace_7694484
  have hstable : (prefixWord ++ tailWord_7694484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694484).length < 2 ^ (prefixWord ++ tailWord_7694484).sum := by decide
  have hdescent : baseEnd_7694484 < baseStart_7694484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694489 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 4, 4]
def baseStart_7694489 : Nat := 118140960795 + 7694489 * 2 ^ 59
def prefixEnd_7694489 : Nat := 4983230072969 + 3 ^ 40 * 7694489 * 2
def baseEnd_7694489 : Nat := 1316990415911017003367065

theorem tailTrace_7694489 : CollatzResearch.WordTrace tailWord_7694489 prefixEnd_7694489 1316990415911017003367065 := by
  unfold tailWord_7694489
  simp only [CollatzResearch.WordTrace]
  refine ⟨280641069421187941944342521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187094046280791961296228347 280641069421187941944342521)
  ·
    refine ⟨210480802065890956458256891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280641069421187941944342521 210480802065890956458256891)
    ·
      refine ⟨315721203098836434687385337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210480802065890956458256891 315721203098836434687385337)
      ·
        refine ⟨236790902324127326015539003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315721203098836434687385337 236790902324127326015539003)
        ·
          refine ⟨355186353486190989023308505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236790902324127326015539003 355186353486190989023308505)
          ·
            refine ⟨266389765114643241767481379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355186353486190989023308505 266389765114643241767481379)
            ·
              refine ⟨399584647671964862651222069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266389765114643241767481379 399584647671964862651222069)
              ·
                refine ⟨37461060719246705873552069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399584647671964862651222069 37461060719246705873552069)
                ·
                  refine ⟨7023948884858757351291013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37461060719246705873552069 7023948884858757351291013)
                  ·
                    refine ⟨1316990415911017003367065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7023948884858757351291013 1316990415911017003367065)
                    ·
                      rfl

theorem cell23_7694489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_7694489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694489 prefixEnd_7694489 := by exact prefixLift 7694489
  have htrace : WordTrace (prefixWord ++ tailWord_7694489) baseStart_7694489 baseEnd_7694489 := by
    simpa [prefixWord, tailWord_7694489, baseEnd_7694489] using wordTrace_append hprefix tailTrace_7694489
  have hstable : (prefixWord ++ tailWord_7694489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694489).length < 2 ^ (prefixWord ++ tailWord_7694489).sum := by decide
  have hdescent : baseEnd_7694489 < baseStart_7694489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694517 : List Nat := [1, 3, 3, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7694517 : Nat := 118140960795 + 7694517 * 2 ^ 59
def prefixEnd_7694517 : Nat := 4983230072969 + 3 ^ 40 * 7694517 * 2
def baseEnd_7694517 : Nat := 3950985625191376900551067

theorem tailTrace_7694517 : CollatzResearch.WordTrace tailWord_7694517 prefixEnd_7694517 3950985625191376900551067 := by
  unfold tailWord_7694517
  simp only [CollatzResearch.WordTrace]
  refine ⟨280642090665086502726361805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187094727110057668484241203 280642090665086502726361805)
  ·
    refine ⟨105240783999407438522385677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280642090665086502726361805 105240783999407438522385677)
    ·
      refine ⟨39465293999777789445894629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105240783999407438522385677 39465293999777789445894629)
      ·
        refine ⟨7399742624958335521105243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39465293999777789445894629 7399742624958335521105243)
        ·
          refine ⟨11099613937437503281657865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7399742624958335521105243 11099613937437503281657865)
          ·
            refine ⟨8324710453078127461243399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11099613937437503281657865 8324710453078127461243399)
            ·
              refine ⟨12487065679617191191865099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8324710453078127461243399 12487065679617191191865099)
              ·
                refine ⟨18730598519425786787797649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12487065679617191191865099 18730598519425786787797649)
                ·
                  refine ⟨14047948889569340090848237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18730598519425786787797649 14047948889569340090848237)
                  ·
                    refine ⟨5267980833588502534068089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14047948889569340090848237 5267980833588502534068089)
                    ·
                      refine ⟨3950985625191376900551067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5267980833588502534068089 3950985625191376900551067)
                      ·
                        rfl

theorem cell23_7694517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7694517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694517 prefixEnd_7694517 := by exact prefixLift 7694517
  have htrace : WordTrace (prefixWord ++ tailWord_7694517) baseStart_7694517 baseEnd_7694517 := by
    simpa [prefixWord, tailWord_7694517, baseEnd_7694517] using wordTrace_append hprefix tailTrace_7694517
  have hstable : (prefixWord ++ tailWord_7694517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694517).length < 2 ^ (prefixWord ++ tailWord_7694517).sum := by decide
  have hdescent : baseEnd_7694517 < baseStart_7694517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694533 : List Nat := [1, 3, 1, 1, 1, 1, 8, 1, 1, 2, 3]
def baseStart_7694533 : Nat := 118140960795 + 7694533 * 2 ^ 59
def prefixEnd_7694533 : Nat := 4983230072969 + 3 ^ 40 * 7694533 * 2
def baseEnd_7694533 : Nat := 3950993840881848837950993

theorem tailTrace_7694533 : CollatzResearch.WordTrace tailWord_7694533 prefixEnd_7694533 3950993840881848837950993 := by
  unfold tailWord_7694533
  simp only [CollatzResearch.WordTrace]
  refine ⟨280642674233028537458944253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187095116155352358305962835 280642674233028537458944253)
  ·
    refine ⟨105241002837385701547104095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280642674233028537458944253 105241002837385701547104095)
    ·
      refine ⟨157861504256078552320656143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105241002837385701547104095 157861504256078552320656143)
      ·
        refine ⟨236792256384117828480984215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157861504256078552320656143 236792256384117828480984215)
        ·
          refine ⟨355188384576176742721476323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236792256384117828480984215 355188384576176742721476323)
          ·
            refine ⟨532782576864265114082214485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355188384576176742721476323 532782576864265114082214485)
            ·
              refine ⟨6243545822628106805650951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 532782576864265114082214485 6243545822628106805650951)
              ·
                refine ⟨9365318733942160208476427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243545822628106805650951 9365318733942160208476427)
                ·
                  refine ⟨14047978100913240312714641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365318733942160208476427 14047978100913240312714641)
                  ·
                    refine ⟨10535983575684930234535981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14047978100913240312714641 10535983575684930234535981)
                    ·
                      refine ⟨3950993840881848837950993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10535983575684930234535981 3950993840881848837950993)
                      ·
                        rfl

theorem cell23_7694533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8, 1, 1, 2, 3].length) (baseStart_7694533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694533 prefixEnd_7694533 := by exact prefixLift 7694533
  have htrace : WordTrace (prefixWord ++ tailWord_7694533) baseStart_7694533 baseEnd_7694533 := by
    simpa [prefixWord, tailWord_7694533, baseEnd_7694533] using wordTrace_append hprefix tailTrace_7694533
  have hstable : (prefixWord ++ tailWord_7694533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694533).length < 2 ^ (prefixWord ++ tailWord_7694533).sum := by decide
  have hdescent : baseEnd_7694533 < baseStart_7694533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694590 : List Nat := [4, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_7694590 : Nat := 118140960795 + 7694590 * 2 ^ 59
def prefixEnd_7694590 : Nat := 4983230072969 + 3 ^ 40 * 7694590 * 2
def baseEnd_7694590 : Nat := 3951023109279155114938231

theorem tailTrace_7694590 : CollatzResearch.WordTrace tailWord_7694590 prefixEnd_7694590 3951023109279155114938231 := by
  unfold tailWord_7694590
  simp only [CollatzResearch.WordTrace]
  refine ⟨35080594149227754524221153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187096502129214690795846149 35080594149227754524221153)
  ·
    refine ⟨26310445611920815893165865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35080594149227754524221153 26310445611920815893165865)
    ·
      refine ⟨19732834208940611919874399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26310445611920815893165865 19732834208940611919874399)
      ·
        refine ⟨29599251313410917879811599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19732834208940611919874399 29599251313410917879811599)
        ·
          refine ⟨44398876970116376819717399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29599251313410917879811599 44398876970116376819717399)
          ·
            refine ⟨66598315455174565229576099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44398876970116376819717399 66598315455174565229576099)
            ·
              refine ⟨99897473182761847844364149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66598315455174565229576099 99897473182761847844364149)
              ·
                refine ⟨9365388110883923235409139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99897473182761847844364149 9365388110883923235409139)
                ·
                  refine ⟨14048082166325884853113709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365388110883923235409139 14048082166325884853113709)
                  ·
                    refine ⟨5268030812372206819917641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14048082166325884853113709 5268030812372206819917641)
                    ·
                      refine ⟨3951023109279155114938231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268030812372206819917641 3951023109279155114938231)
                      ·
                        rfl

theorem cell23_7694590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_7694590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694590 prefixEnd_7694590 := by exact prefixLift 7694590
  have htrace : WordTrace (prefixWord ++ tailWord_7694590) baseStart_7694590 baseEnd_7694590 := by
    simpa [prefixWord, tailWord_7694590, baseEnd_7694590] using wordTrace_append hprefix tailTrace_7694590
  have hstable : (prefixWord ++ tailWord_7694590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694590).length < 2 ^ (prefixWord ++ tailWord_7694590).sum := by decide
  have hdescent : baseEnd_7694590 < baseStart_7694590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694603 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 4, 2, 2]
def baseStart_7694603 : Nat := 118140960795 + 7694603 * 2 ^ 59
def prefixEnd_7694603 : Nat := 4983230072969 + 3 ^ 40 * 7694603 * 2
def baseEnd_7694603 : Nat := 3951029784527663564075671

theorem tailTrace_7694603 : CollatzResearch.WordTrace tailWord_7694603 prefixEnd_7694603 3951029784527663564075671 := by
  unfold tailWord_7694603
  simp only [CollatzResearch.WordTrace]
  refine ⟨280645227342774939413992463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187096818228516626275994975 280645227342774939413992463)
  ·
    refine ⟨420967841014162409120988695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280645227342774939413992463 420967841014162409120988695)
    ·
      refine ⟨631451761521243613681483043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420967841014162409120988695 631451761521243613681483043)
      ·
        refine ⟨947177642281865420522224565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631451761521243613681483043 947177642281865420522224565)
        ·
          refine ⟨88797903963924883173958553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 947177642281865420522224565 88797903963924883173958553)
          ·
            refine ⟨66598427972943662380468915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88797903963924883173958553 66598427972943662380468915)
            ·
              refine ⟨99897641959415493570703373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66598427972943662380468915 99897641959415493570703373)
              ·
                refine ⟨37461615734780810089013765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99897641959415493570703373 37461615734780810089013765)
                ·
                  refine ⟨7024052950271401891690081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37461615734780810089013765 7024052950271401891690081)
                  ·
                    refine ⟨5268039712703551418767561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024052950271401891690081 5268039712703551418767561)
                    ·
                      refine ⟨3951029784527663564075671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268039712703551418767561 3951029784527663564075671)
                      ·
                        rfl

theorem cell23_7694603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 4, 2, 2].length) (baseStart_7694603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694603 prefixEnd_7694603 := by exact prefixLift 7694603
  have htrace : WordTrace (prefixWord ++ tailWord_7694603) baseStart_7694603 baseEnd_7694603 := by
    simpa [prefixWord, tailWord_7694603, baseEnd_7694603] using wordTrace_append hprefix tailTrace_7694603
  have hstable : (prefixWord ++ tailWord_7694603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694603).length < 2 ^ (prefixWord ++ tailWord_7694603).sum := by decide
  have hdescent : baseEnd_7694603 < baseStart_7694603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694606 : List Nat := [4, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_7694606 : Nat := 118140960795 + 7694606 * 2 ^ 59
def prefixEnd_7694606 : Nat := 4983230072969 + 3 ^ 40 * 7694606 * 2
def baseEnd_7694606 : Nat := 3951031324969627052338157

theorem tailTrace_7694606 : CollatzResearch.WordTrace tailWord_7694606 prefixEnd_7694606 3951031324969627052338157 := by
  unfold tailWord_7694606
  simp only [CollatzResearch.WordTrace]
  refine ⟨35080667095220508865793959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187096891174509380617567781 35080667095220508865793959)
  ·
    refine ⟨52621000642830763298690939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35080667095220508865793959 52621000642830763298690939)
    ·
      refine ⟨78931500964246144948036409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52621000642830763298690939 78931500964246144948036409)
      ·
        refine ⟨59198625723184608711027307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78931500964246144948036409 59198625723184608711027307)
        ·
          refine ⟨88797938584776913066540961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59198625723184608711027307 88797938584776913066540961)
          ·
            refine ⟨66598453938582684799905721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88797938584776913066540961 66598453938582684799905721)
            ·
              refine ⟨49948840453937013599929291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66598453938582684799905721 49948840453937013599929291)
              ·
                refine ⟨74923260680905520399893937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49948840453937013599929291 74923260680905520399893937)
                ·
                  refine ⟨56192445510679140299920453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74923260680905520399893937 56192445510679140299920453)
                  ·
                    refine ⟨10536083533252338806235085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56192445510679140299920453 10536083533252338806235085)
                    ·
                      refine ⟨3951031324969627052338157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536083533252338806235085 3951031324969627052338157)
                      ·
                        rfl

theorem cell23_7694606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_7694606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694606 prefixEnd_7694606 := by exact prefixLift 7694606
  have htrace : WordTrace (prefixWord ++ tailWord_7694606) baseStart_7694606 baseEnd_7694606 := by
    simpa [prefixWord, tailWord_7694606, baseEnd_7694606] using wordTrace_append hprefix tailTrace_7694606
  have hstable : (prefixWord ++ tailWord_7694606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694606).length < 2 ^ (prefixWord ++ tailWord_7694606).sum := by decide
  have hdescent : baseEnd_7694606 < baseStart_7694606 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694637 : List Nat := [1, 5, 3, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_7694637 : Nat := 118140960795 + 7694637 * 2 ^ 59
def prefixEnd_7694637 : Nat := 4983230072969 + 3 ^ 40 * 7694637 * 2
def baseEnd_7694637 : Nat := 3951047242869916431050515

theorem tailTrace_7694637 : CollatzResearch.WordTrace tailWord_7694637 prefixEnd_7694637 3951047242869916431050515 := by
  unfold tailWord_7694637
  simp only [CollatzResearch.WordTrace]
  refine ⟨280646467424651763220730165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187097644949767842147153443 280646467424651763220730165)
  ·
    refine ⟨26310606321061102801943453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280646467424651763220730165 26310606321061102801943453)
    ·
      refine ⟨9866477370397913550728795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26310606321061102801943453 9866477370397913550728795)
      ·
        refine ⟨14799716055596870326093193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9866477370397913550728795 14799716055596870326093193)
        ·
          refine ⟨11099787041697652744569895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14799716055596870326093193 11099787041697652744569895)
          ·
            refine ⟨16649680562546479116854843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11099787041697652744569895 16649680562546479116854843)
            ·
              refine ⟨24974520843819718675282265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16649680562546479116854843 24974520843819718675282265)
              ·
                refine ⟨18730890632864789006461699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24974520843819718675282265 18730890632864789006461699)
                ·
                  refine ⟨28096335949297183509692549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18730890632864789006461699 28096335949297183509692549)
                  ·
                    refine ⟨5268062990493221908067353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28096335949297183509692549 5268062990493221908067353)
                    ·
                      refine ⟨3951047242869916431050515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268062990493221908067353 3951047242869916431050515)
                      ·
                        rfl

theorem cell23_7694637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_7694637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694637 prefixEnd_7694637 := by exact prefixLift 7694637
  have htrace : WordTrace (prefixWord ++ tailWord_7694637) baseStart_7694637 baseEnd_7694637 := by
    simpa [prefixWord, tailWord_7694637, baseEnd_7694637] using wordTrace_append hprefix tailTrace_7694637
  have hstable : (prefixWord ++ tailWord_7694637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694637).length < 2 ^ (prefixWord ++ tailWord_7694637).sum := by decide
  have hdescent : baseEnd_7694637 < baseStart_7694637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694639 : List Nat := [1, 1, 2, 1, 2, 1, 4, 3, 1, 7]
def baseStart_7694639 : Nat := 118140960795 + 7694639 * 2 ^ 59
def prefixEnd_7694639 : Nat := 4983230072969 + 3 ^ 40 * 7694639 * 2
def baseEnd_7694639 : Nat := 1317016089943741807741835

theorem tailTrace_7694639 : CollatzResearch.WordTrace tailWord_7694639 prefixEnd_7694639 1317016089943741807741835 := by
  unfold tailWord_7694639
  simp only [CollatzResearch.WordTrace]
  refine ⟨280646540370644517562302971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187097693580429678374868647 280646540370644517562302971)
  ·
    refine ⟨420969810555966776343454457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280646540370644517562302971 420969810555966776343454457)
    ·
      refine ⟨315727357916975082257590843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420969810555966776343454457 315727357916975082257590843)
      ·
        refine ⟨473591036875462623386386265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315727357916975082257590843 473591036875462623386386265)
        ·
          refine ⟨355193277656596967539789699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473591036875462623386386265 355193277656596967539789699)
          ·
            refine ⟨532789916484895451309684549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355193277656596967539789699 532789916484895451309684549)
            ·
              refine ⟨99898109340917897120565853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 532789916484895451309684549 99898109340917897120565853)
              ·
                refine ⟨37461791002844211420212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99898109340917897120565853 37461791002844211420212195)
                ·
                  refine ⟨56192686504266317130318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37461791002844211420212195 56192686504266317130318293)
                  ·
                    refine ⟨1317016089943741807741835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56192686504266317130318293 1317016089943741807741835)
                    ·
                      rfl

theorem cell23_7694639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_7694639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694639 prefixEnd_7694639 := by exact prefixLift 7694639
  have htrace : WordTrace (prefixWord ++ tailWord_7694639) baseStart_7694639 baseEnd_7694639 := by
    simpa [prefixWord, tailWord_7694639, baseEnd_7694639] using wordTrace_append hprefix tailTrace_7694639
  have hstable : (prefixWord ++ tailWord_7694639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694639).length < 2 ^ (prefixWord ++ tailWord_7694639).sum := by decide
  have hdescent : baseEnd_7694639 < baseStart_7694639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694690 : List Nat := [3, 3, 2, 1, 1, 4, 1, 1, 2, 5]
def baseStart_7694690 : Nat := 118140960795 + 7694690 * 2 ^ 59
def prefixEnd_7694690 : Nat := 4983230072969 + 3 ^ 40 * 7694690 * 2
def baseEnd_7694690 : Nat := 1317024819114868241229257

theorem tailTrace_7694690 : CollatzResearch.WordTrace tailWord_7694690 prefixEnd_7694690 1317024819114868241229257 := by
  unfold tailWord_7694690
  simp only [CollatzResearch.WordTrace]
  refine ⟨70162100123364938318102381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187098933662306502181606349 70162100123364938318102381)
  ·
    refine ⟨26310787546261851869288393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70162100123364938318102381 26310787546261851869288393)
    ·
      refine ⟨19733090659696388901966295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26310787546261851869288393 19733090659696388901966295)
      ·
        refine ⟨29599635989544583352949443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19733090659696388901966295 29599635989544583352949443)
        ·
          refine ⟨44399453984316875029424165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29599635989544583352949443 44399453984316875029424165)
          ·
            refine ⟨8324897622059414068017031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44399453984316875029424165 8324897622059414068017031)
            ·
              refine ⟨12487346433089121102025547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8324897622059414068017031 12487346433089121102025547)
              ·
                refine ⟨18731019649633681653038321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12487346433089121102025547 18731019649633681653038321)
                ·
                  refine ⟨14048264737225261239778741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18731019649633681653038321 14048264737225261239778741)
                  ·
                    refine ⟨1317024819114868241229257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14048264737225261239778741 1317024819114868241229257)
                    ·
                      rfl

theorem cell23_7694690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_7694690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694690 prefixEnd_7694690 := by exact prefixLift 7694690
  have htrace : WordTrace (prefixWord ++ tailWord_7694690) baseStart_7694690 baseEnd_7694690 := by
    simpa [prefixWord, tailWord_7694690, baseEnd_7694690] using wordTrace_append hprefix tailTrace_7694690
  have hstable : (prefixWord ++ tailWord_7694690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694690).length < 2 ^ (prefixWord ++ tailWord_7694690).sum := by decide
  have hdescent : baseEnd_7694690 < baseStart_7694690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694693 : List Nat := [1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_7694693 : Nat := 118140960795 + 7694693 * 2 ^ 59
def prefixEnd_7694693 : Nat := 4983230072969 + 3 ^ 40 * 7694693 * 2
def baseEnd_7694693 : Nat := 3951075997786568211950257

theorem tailTrace_7694693 : CollatzResearch.WordTrace tailWord_7694693 prefixEnd_7694693 3951075997786568211950257 := by
  unfold tailWord_7694693
  simp only [CollatzResearch.WordTrace]
  refine ⟨280648509912448884784768733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187099006608299256523179155 280648509912448884784768733)
  ·
    refine ⟨105243191217168331794288275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280648509912448884784768733 105243191217168331794288275)
    ·
      refine ⟨157864786825752497691432413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105243191217168331794288275 157864786825752497691432413)
      ·
        refine ⟨59199295059657186634287155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157864786825752497691432413 59199295059657186634287155)
        ·
          refine ⟨88798942589485779951430733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59199295059657186634287155 88798942589485779951430733)
          ·
            refine ⟨33299603471057167481786525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88798942589485779951430733 33299603471057167481786525)
            ·
              refine ⟨12487351301646437805669947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33299603471057167481786525 12487351301646437805669947)
              ·
                refine ⟨18731026952469656708504921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12487351301646437805669947 18731026952469656708504921)
                ·
                  refine ⟨14048270214352242531378691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18731026952469656708504921 14048270214352242531378691)
                  ·
                    refine ⟨21072405321528363797068037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14048270214352242531378691 21072405321528363797068037)
                    ·
                      refine ⟨3951075997786568211950257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21072405321528363797068037 3951075997786568211950257)
                      ·
                        rfl

theorem cell23_7694693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_7694693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694693 prefixEnd_7694693 := by exact prefixLift 7694693
  have htrace : WordTrace (prefixWord ++ tailWord_7694693) baseStart_7694693 baseEnd_7694693 := by
    simpa [prefixWord, tailWord_7694693, baseEnd_7694693] using wordTrace_append hprefix tailTrace_7694693
  have hstable : (prefixWord ++ tailWord_7694693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694693).length < 2 ^ (prefixWord ++ tailWord_7694693).sum := by decide
  have hdescent : baseEnd_7694693 < baseStart_7694693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694699 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 10]
def baseStart_7694699 : Nat := 118140960795 + 7694699 * 2 ^ 59
def prefixEnd_7694699 : Nat := 4983230072969 + 3 ^ 40 * 7694699 * 2
def baseEnd_7694699 : Nat := 439008786518943909830581

theorem tailTrace_7694699 : CollatzResearch.WordTrace tailWord_7694699 prefixEnd_7694699 439008786518943909830581 := by
  unfold tailWord_7694699
  simp only [CollatzResearch.WordTrace]
  refine ⟨280648728750427147809487151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187099152500284765206324767 280648728750427147809487151)
  ·
    refine ⟨420973093125640721714230727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280648728750427147809487151 420973093125640721714230727)
    ·
      refine ⟨631459639688461082571346091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420973093125640721714230727 631459639688461082571346091)
      ·
        refine ⟨947189459532691623857019137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631459639688461082571346091 947189459532691623857019137)
        ·
          refine ⟨710392094649518717892764353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 947189459532691623857019137 710392094649518717892764353)
          ·
            refine ⟨532794070987139038419573265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710392094649518717892764353 532794070987139038419573265)
            ·
              refine ⟨399595553240354278814679949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532794070987139038419573265 399595553240354278814679949)
              ·
                refine ⟨149848332465132854555504981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 399595553240354278814679949 149848332465132854555504981)
                ·
                  refine ⟨439008786518943909830581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149848332465132854555504981 439008786518943909830581)
                  ·
                    rfl

theorem cell23_7694699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 10].length) (baseStart_7694699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694699 prefixEnd_7694699 := by exact prefixLift 7694699
  have htrace : WordTrace (prefixWord ++ tailWord_7694699) baseStart_7694699 baseEnd_7694699 := by
    simpa [prefixWord, tailWord_7694699, baseEnd_7694699] using wordTrace_append hprefix tailTrace_7694699
  have hstable : (prefixWord ++ tailWord_7694699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694699).length < 2 ^ (prefixWord ++ tailWord_7694699).sum := by decide
  have hdescent : baseEnd_7694699 < baseStart_7694699 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694706 : List Nat := [3, 2, 1, 2, 1, 3, 1, 1, 2, 1, 6]
def baseStart_7694706 : Nat := 118140960795 + 7694706 * 2 ^ 59
def prefixEnd_7694706 : Nat := 4983230072969 + 3 ^ 40 * 7694706 * 2
def baseEnd_7694706 : Nat := 3951082673035076661087697

theorem tailTrace_7694706 : CollatzResearch.WordTrace tailWord_7694706 prefixEnd_7694706 3951082673035076661087697 := by
  unfold tailWord_7694706
  simp only [CollatzResearch.WordTrace]
  refine ⟨70162246015350447001247993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187099322707601192003327981 70162246015350447001247993)
  ·
    refine ⟨52621684511512835250935995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70162246015350447001247993 52621684511512835250935995)
    ·
      refine ⟨78932526767269252876403993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52621684511512835250935995 78932526767269252876403993)
      ·
        refine ⟨59199395075451939657302995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78932526767269252876403993 59199395075451939657302995)
        ·
          refine ⟨88799092613177909485954493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59199395075451939657302995 88799092613177909485954493)
          ·
            refine ⟨33299659729941716057232935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88799092613177909485954493 33299659729941716057232935)
            ·
              refine ⟨49949489594912574085849403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33299659729941716057232935 49949489594912574085849403)
              ·
                refine ⟨74924234392368861128774105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49949489594912574085849403 74924234392368861128774105)
                ·
                  refine ⟨56193175794276645846580579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74924234392368861128774105 56193175794276645846580579)
                  ·
                    refine ⟨84289763691414968769870869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56193175794276645846580579 84289763691414968769870869)
                    ·
                      refine ⟨3951082673035076661087697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84289763691414968769870869 3951082673035076661087697)
                      ·
                        rfl

theorem cell23_7694706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_7694706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694706 prefixEnd_7694706 := by exact prefixLift 7694706
  have htrace : WordTrace (prefixWord ++ tailWord_7694706) baseStart_7694706 baseEnd_7694706 := by
    simpa [prefixWord, tailWord_7694706, baseEnd_7694706] using wordTrace_append hprefix tailTrace_7694706
  have hstable : (prefixWord ++ tailWord_7694706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694706).length < 2 ^ (prefixWord ++ tailWord_7694706).sum := by decide
  have hdescent : baseEnd_7694706 < baseStart_7694706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694716 : List Nat := [2, 2, 2, 1, 1, 1, 2, 6, 6]
def baseStart_7694716 : Nat := 118140960795 + 7694716 * 2 ^ 59
def prefixEnd_7694716 : Nat := 4983230072969 + 3 ^ 40 * 7694716 * 2
def baseEnd_7694716 : Nat := 439009756426846846884739

theorem tailTrace_7694716 : CollatzResearch.WordTrace tailWord_7694716 prefixEnd_7694716 439009756426846846884739 := by
  unfold tailWord_7694716
  simp only [CollatzResearch.WordTrace]
  refine ⟨140324674395682779856428001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187099565860910373141904001 140324674395682779856428001)
  ·
    refine ⟨105243505796762084892321001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140324674395682779856428001 105243505796762084892321001)
    ·
      refine ⟨78932629347571563669240751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105243505796762084892321001 78932629347571563669240751)
      ·
        refine ⟨118398944021357345503861127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78932629347571563669240751 118398944021357345503861127)
        ·
          refine ⟨177598416032036018255791691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118398944021357345503861127 177598416032036018255791691)
          ·
            refine ⟨266397624048054027383687537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177598416032036018255791691 266397624048054027383687537)
            ·
              refine ⟨199798218036040520537765653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266397624048054027383687537 199798218036040520537765653)
              ·
                refine ⟨9365541470439399400207765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199798218036040520537765653 9365541470439399400207765)
                ·
                  refine ⟨439009756426846846884739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9365541470439399400207765 439009756426846846884739)
                  ·
                    rfl

theorem cell23_7694716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 6, 6].length) (baseStart_7694716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694716 prefixEnd_7694716 := by exact prefixLift 7694716
  have htrace : WordTrace (prefixWord ++ tailWord_7694716) baseStart_7694716 baseEnd_7694716 := by
    simpa [prefixWord, tailWord_7694716, baseEnd_7694716] using wordTrace_append hprefix tailTrace_7694716
  have hstable : (prefixWord ++ tailWord_7694716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694716).length < 2 ^ (prefixWord ++ tailWord_7694716).sum := by decide
  have hdescent : baseEnd_7694716 < baseStart_7694716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694770 : List Nat := [3, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2]
def baseStart_7694770 : Nat := 118140960795 + 7694770 * 2 ^ 59
def prefixEnd_7694770 : Nat := 4983230072969 + 3 ^ 40 * 7694770 * 2
def baseEnd_7694770 : Nat := 3951115535796964410687403

theorem tailTrace_7694770 : CollatzResearch.WordTrace tailWord_7694770 prefixEnd_7694770 3951115535796964410687403 := by
  unfold tailWord_7694770
  simp only [CollatzResearch.WordTrace]
  refine ⟨70162829583292481733830441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187100878888779951290214509 70162829583292481733830441)
  ·
    refine ⟨52622122187469361300372831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70162829583292481733830441 52622122187469361300372831)
    ·
      refine ⟨78933183281204041950559247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52622122187469361300372831 78933183281204041950559247)
      ·
        refine ⟨118399774921806062925838871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78933183281204041950559247 118399774921806062925838871)
        ·
          refine ⟨177599662382709094388758307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118399774921806062925838871 177599662382709094388758307)
          ·
            refine ⟨266399493574063641583137461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177599662382709094388758307 266399493574063641583137461)
            ·
              refine ⟨24974952522568466398419137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 266399493574063641583137461 24974952522568466398419137)
              ·
                refine ⟨18731214391926349798814353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24974952522568466398419137 18731214391926349798814353)
                ·
                  refine ⟨14048410793944762349110765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18731214391926349798814353 14048410793944762349110765)
                  ·
                    refine ⟨5268154047729285880916537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14048410793944762349110765 5268154047729285880916537)
                    ·
                      refine ⟨3951115535796964410687403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268154047729285880916537 3951115535796964410687403)
                      ·
                        rfl

theorem cell23_7694770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_7694770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694770 prefixEnd_7694770 := by exact prefixLift 7694770
  have htrace : WordTrace (prefixWord ++ tailWord_7694770) baseStart_7694770 baseEnd_7694770 := by
    simpa [prefixWord, tailWord_7694770, baseEnd_7694770] using wordTrace_append hprefix tailTrace_7694770
  have hstable : (prefixWord ++ tailWord_7694770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694770).length < 2 ^ (prefixWord ++ tailWord_7694770).sum := by decide
  have hdescent : baseEnd_7694770 < baseStart_7694770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694777 : List Nat := [1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 3]
def baseStart_7694777 : Nat := 118140960795 + 7694777 * 2 ^ 59
def prefixEnd_7694777 : Nat := 4983230072969 + 3 ^ 40 * 7694777 * 2
def baseEnd_7694777 : Nat := 3951119130161545883299871

theorem tailTrace_7694777 : CollatzResearch.WordTrace tailWord_7694777 prefixEnd_7694777 3951119130161545883299871 := by
  unfold tailWord_7694777
  simp only [CollatzResearch.WordTrace]
  refine ⟨280651573644144567130826585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187101049096096378087217723 280651573644144567130826585)
  ·
    refine ⟨210488680233108425348119939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280651573644144567130826585 210488680233108425348119939)
    ·
      refine ⟨315733020349662638022179909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210488680233108425348119939 315733020349662638022179909)
      ·
        refine ⟨59199941315561744629158733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315733020349662638022179909 59199941315561744629158733)
        ·
          refine ⟨22199977993335654235934525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59199941315561744629158733 22199977993335654235934525)
          ·
            refine ⟨8324991747500870338475447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22199977993335654235934525 8324991747500870338475447)
            ·
              refine ⟨12487487621251305507713171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8324991747500870338475447 12487487621251305507713171)
              ·
                refine ⟨18731231431876958261569757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12487487621251305507713171 18731231431876958261569757)
                ·
                  refine ⟨7024211786953859348088659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18731231431876958261569757 7024211786953859348088659)
                  ·
                    refine ⟨10536317680430789022132989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7024211786953859348088659 10536317680430789022132989)
                    ·
                      refine ⟨3951119130161545883299871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536317680430789022132989 3951119130161545883299871)
                      ·
                        rfl

theorem cell23_7694777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_7694777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694777 prefixEnd_7694777 := by exact prefixLift 7694777
  have htrace : WordTrace (prefixWord ++ tailWord_7694777) baseStart_7694777 baseEnd_7694777 := by
    simpa [prefixWord, tailWord_7694777, baseEnd_7694777] using wordTrace_append hprefix tailTrace_7694777
  have hstable : (prefixWord ++ tailWord_7694777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694777).length < 2 ^ (prefixWord ++ tailWord_7694777).sum := by decide
  have hdescent : baseEnd_7694777 < baseStart_7694777 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694833 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_7694833 : Nat := 118140960795 + 7694833 * 2 ^ 59
def prefixEnd_7694833 : Nat := 4983230072969 + 3 ^ 40 * 7694833 * 2
def baseEnd_7694833 : Nat := 3951147885078197664199613

theorem tailTrace_7694833 : CollatzResearch.WordTrace tailWord_7694833 prefixEnd_7694833 3951147885078197664199613 := by
  unfold tailWord_7694833
  simp only [CollatzResearch.WordTrace]
  refine ⟨280653616131941688694865153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187102410754627792463243435 280653616131941688694865153)
  ·
    refine ⟨210490212098956266521148865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280653616131941688694865153 210490212098956266521148865)
    ·
      refine ⟨157867659074217199890861649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210490212098956266521148865 157867659074217199890861649)
      ·
        refine ⟨118400744305662899918146237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157867659074217199890861649 118400744305662899918146237)
        ·
          refine ⟨44400279114623587469304839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118400744305662899918146237 44400279114623587469304839)
          ·
            refine ⟨66600418671935381203957259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44400279114623587469304839 66600418671935381203957259)
            ·
              refine ⟨99900628007903071805935889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66600418671935381203957259 99900628007903071805935889)
              ·
                refine ⟨74925471005927303854451917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99900628007903071805935889 74925471005927303854451917)
                ·
                  refine ⟨28097051627222738945419469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74925471005927303854451917 28097051627222738945419469)
                  ·
                    refine ⟨10536394360208527104532301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28097051627222738945419469 10536394360208527104532301)
                    ·
                      refine ⟨3951147885078197664199613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536394360208527104532301 3951147885078197664199613)
                      ·
                        rfl

theorem cell23_7694833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_7694833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694833 prefixEnd_7694833 := by exact prefixLift 7694833
  have htrace : WordTrace (prefixWord ++ tailWord_7694833) baseStart_7694833 baseEnd_7694833 := by
    simpa [prefixWord, tailWord_7694833, baseEnd_7694833] using wordTrace_append hprefix tailTrace_7694833
  have hstable : (prefixWord ++ tailWord_7694833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694833).length < 2 ^ (prefixWord ++ tailWord_7694833).sum := by decide
  have hdescent : baseEnd_7694833 < baseStart_7694833 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694843 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 9, 2]
def baseStart_7694843 : Nat := 118140960795 + 7694843 * 2 ^ 59
def prefixEnd_7694843 : Nat := 4983230072969 + 3 ^ 40 * 7694843 * 2
def baseEnd_7694843 : Nat := 3951153019884742625074567

theorem tailTrace_7694843 : CollatzResearch.WordTrace tailWord_7694843 prefixEnd_7694843 3951153019884742625074567 := by
  unfold tailWord_7694843
  simp only [CollatzResearch.WordTrace]
  refine ⟨280653980861905460402729183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187102653907936973601819455 280653980861905460402729183)
  ·
    refine ⟨420980971292858190604093775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280653980861905460402729183 420980971292858190604093775)
    ·
      refine ⟨631471456939287285906140663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420980971292858190604093775 631471456939287285906140663)
      ·
        refine ⟨947207185408930928859210995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631471456939287285906140663 947207185408930928859210995)
        ·
          refine ⟨1420810778113396393288816493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947207185408930928859210995 1420810778113396393288816493)
          ·
            refine ⟨532804041792523647483306185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1420810778113396393288816493 532804041792523647483306185)
            ·
              refine ⟨399603031344392735612479639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532804041792523647483306185 399603031344392735612479639)
              ·
                refine ⟨599404547016589103418719459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399603031344392735612479639 599404547016589103418719459)
                ·
                  refine ⟨899106820524883655128079189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 599404547016589103418719459 899106820524883655128079189)
                  ·
                    refine ⟨5268204026512990166766089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 899106820524883655128079189 5268204026512990166766089)
                    ·
                      refine ⟨3951153019884742625074567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268204026512990166766089 3951153019884742625074567)
                      ·
                        rfl

theorem cell23_7694843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 9, 2].length) (baseStart_7694843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694843 prefixEnd_7694843 := by exact prefixLift 7694843
  have htrace : WordTrace (prefixWord ++ tailWord_7694843) baseStart_7694843 baseEnd_7694843 := by
    simpa [prefixWord, tailWord_7694843, baseEnd_7694843] using wordTrace_append hprefix tailTrace_7694843
  have hstable : (prefixWord ++ tailWord_7694843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694843).length < 2 ^ (prefixWord ++ tailWord_7694843).sum := by decide
  have hdescent : baseEnd_7694843 < baseStart_7694843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694868 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_7694868 : Nat := 118140960795 + 7694868 * 2 ^ 59
def prefixEnd_7694868 : Nat := 4983230072969 + 3 ^ 40 * 7694868 * 2
def baseEnd_7694868 : Nat := 3951165856901105027261953

theorem tailTrace_7694868 : CollatzResearch.WordTrace tailWord_7694868 prefixEnd_7694868 3951165856901105027261953 := by
  unfold tailWord_7694868
  simp only [CollatzResearch.WordTrace]
  refine ⟨140327446343407444836194629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187103261791209926448259505 140327446343407444836194629)
  ·
    refine ⟨26311396189388895906786493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140327446343407444836194629 26311396189388895906786493)
    ·
      refine ⟨9866773571020835965044935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26311396189388895906786493 9866773571020835965044935)
      ·
        refine ⟨14800160356531253947567403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9866773571020835965044935 14800160356531253947567403)
        ·
          refine ⟨22200240534796880921351105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14800160356531253947567403 22200240534796880921351105)
          ·
            refine ⟨16650180401097660691013329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22200240534796880921351105 16650180401097660691013329)
            ·
              refine ⟨12487635300823245518259997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16650180401097660691013329 12487635300823245518259997)
              ·
                refine ⟨4682863237808717069347499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12487635300823245518259997 4682863237808717069347499)
                ·
                  refine ⟨7024294856713075604021249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682863237808717069347499 7024294856713075604021249)
                  ·
                    refine ⟨5268221142534806703015937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024294856713075604021249 5268221142534806703015937)
                    ·
                      refine ⟨3951165856901105027261953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268221142534806703015937 3951165856901105027261953)
                      ·
                        rfl

theorem cell23_7694868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_7694868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694868 prefixEnd_7694868 := by exact prefixLift 7694868
  have htrace : WordTrace (prefixWord ++ tailWord_7694868) baseStart_7694868 baseEnd_7694868 := by
    simpa [prefixWord, tailWord_7694868, baseEnd_7694868] using wordTrace_append hprefix tailTrace_7694868
  have hstable : (prefixWord ++ tailWord_7694868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694868).length < 2 ^ (prefixWord ++ tailWord_7694868).sum := by decide
  have hdescent : baseEnd_7694868 < baseStart_7694868 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694871 : List Nat := [1, 1, 3, 6, 1, 2, 2, 1, 1, 2, 3]
def baseStart_7694871 : Nat := 118140960795 + 7694871 * 2 ^ 59
def prefixEnd_7694871 : Nat := 4983230072969 + 3 ^ 40 * 7694871 * 2
def baseEnd_7694871 : Nat := 3951167397343068515524439

theorem tailTrace_7694871 : CollatzResearch.WordTrace tailWord_7694871 prefixEnd_7694871 3951167397343068515524439 := by
  unfold tailWord_7694871
  simp only [CollatzResearch.WordTrace]
  refine ⟨280655002105804021184748467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187103334737202680789832311 280655002105804021184748467)
  ·
    refine ⟨420982503158706031777122701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280655002105804021184748467 420982503158706031777122701)
    ·
      refine ⟨157868438684514761916421013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420982503158706031777122701 157868438684514761916421013)
      ·
        refine ⟨7400083063336629464832235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 157868438684514761916421013 7400083063336629464832235)
        ·
          refine ⟨11100124595004944197248353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400083063336629464832235 11100124595004944197248353)
          ·
            refine ⟨8325093446253708147936265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11100124595004944197248353 8325093446253708147936265)
            ·
              refine ⟨6243820084690281110952199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325093446253708147936265 6243820084690281110952199)
              ·
                refine ⟨9365730127035421666428299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243820084690281110952199 9365730127035421666428299)
                ·
                  refine ⟨14048595190553132499642449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365730127035421666428299 14048595190553132499642449)
                  ·
                    refine ⟨10536446392914849374731837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14048595190553132499642449 10536446392914849374731837)
                    ·
                      refine ⟨3951167397343068515524439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536446392914849374731837 3951167397343068515524439)
                      ·
                        rfl

theorem cell23_7694871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_7694871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694871 prefixEnd_7694871 := by exact prefixLift 7694871
  have htrace : WordTrace (prefixWord ++ tailWord_7694871) baseStart_7694871 baseEnd_7694871 := by
    simpa [prefixWord, tailWord_7694871, baseEnd_7694871] using wordTrace_append hprefix tailTrace_7694871
  have hstable : (prefixWord ++ tailWord_7694871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694871).length < 2 ^ (prefixWord ++ tailWord_7694871).sum := by decide
  have hdescent : baseEnd_7694871 < baseStart_7694871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694883 : List Nat := [1, 1, 1, 4, 4, 1, 1, 2, 2, 6]
def baseStart_7694883 : Nat := 118140960795 + 7694883 * 2 ^ 59
def prefixEnd_7694883 : Nat := 4983230072969 + 3 ^ 40 * 7694883 * 2
def baseEnd_7694883 : Nat := 1317057853036974156191461

theorem tailTrace_7694883 : CollatzResearch.WordTrace tailWord_7694883 prefixEnd_7694883 1317057853036974156191461 := by
  unfold tailWord_7694883
  simp only [CollatzResearch.WordTrace]
  refine ⟨280655439781760547234185303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187103626521173698156123535 280655439781760547234185303)
  ·
    refine ⟨420983159672640820851277955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280655439781760547234185303 420983159672640820851277955)
    ·
      refine ⟨631474739508961231276916933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420983159672640820851277955 631474739508961231276916933)
      ·
        refine ⟨118401513657930230864421925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 631474739508961231276916933 118401513657930230864421925)
        ·
          refine ⟨22200283810861918287079111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118401513657930230864421925 22200283810861918287079111)
          ·
            refine ⟨33300425716292877430618667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22200283810861918287079111 33300425716292877430618667)
            ·
              refine ⟨49950638574439316145928001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33300425716292877430618667 49950638574439316145928001)
              ·
                refine ⟨37462978930829487109446001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49950638574439316145928001 37462978930829487109446001)
                ·
                  refine ⟨28097234198122115332084501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37462978930829487109446001 28097234198122115332084501)
                  ·
                    refine ⟨1317057853036974156191461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28097234198122115332084501 1317057853036974156191461)
                    ·
                      rfl

theorem cell23_7694883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 6].length) (baseStart_7694883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694883 prefixEnd_7694883 := by exact prefixLift 7694883
  have htrace : WordTrace (prefixWord ++ tailWord_7694883) baseStart_7694883 baseEnd_7694883 := by
    simpa [prefixWord, tailWord_7694883, baseEnd_7694883] using wordTrace_append hprefix tailTrace_7694883
  have hstable : (prefixWord ++ tailWord_7694883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694883).length < 2 ^ (prefixWord ++ tailWord_7694883).sum := by decide
  have hdescent : baseEnd_7694883 < baseStart_7694883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694884 : List Nat := [2, 3, 1, 5, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7694884 : Nat := 118140960795 + 7694884 * 2 ^ 59
def prefixEnd_7694884 : Nat := 4983230072969 + 3 ^ 40 * 7694884 * 2
def baseEnd_7694884 : Nat := 3951174072591576964661879

theorem tailTrace_7694884 : CollatzResearch.WordTrace tailWord_7694884 prefixEnd_7694884 3951174072591576964661879 := by
  unfold tailWord_7694884
  simp only [CollatzResearch.WordTrace]
  refine ⟨140327738127378462202485853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187103650836504616269981137 140327738127378462202485853)
  ·
    refine ⟨52622901797766923325932195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140327738127378462202485853 52622901797766923325932195)
    ·
      refine ⟨78934352696650384988898293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52622901797766923325932195 78934352696650384988898293)
      ·
        refine ⟨7400095565310973592709215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78934352696650384988898293 7400095565310973592709215)
        ·
          refine ⟨11100143347966460389063823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400095565310973592709215 11100143347966460389063823)
          ·
            refine ⟨16650215021949690583595735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100143347966460389063823 16650215021949690583595735)
            ·
              refine ⟨24975322532924535875393603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16650215021949690583595735 24975322532924535875393603)
              ·
                refine ⟨37462983799386803813090405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24975322532924535875393603 37462983799386803813090405)
                ·
                  refine ⟨7024309462385025714954451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37462983799386803813090405 7024309462385025714954451)
                  ·
                    refine ⟨10536464193577538572431677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7024309462385025714954451 10536464193577538572431677)
                    ·
                      refine ⟨3951174072591576964661879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536464193577538572431677 3951174072591576964661879)
                      ·
                        rfl

theorem cell23_7694884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7694884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694884 prefixEnd_7694884 := by exact prefixLift 7694884
  have htrace : WordTrace (prefixWord ++ tailWord_7694884) baseStart_7694884 baseEnd_7694884 := by
    simpa [prefixWord, tailWord_7694884, baseEnd_7694884] using wordTrace_append hprefix tailTrace_7694884
  have hstable : (prefixWord ++ tailWord_7694884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694884).length < 2 ^ (prefixWord ++ tailWord_7694884).sum := by decide
  have hdescent : baseEnd_7694884 < baseStart_7694884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694903 : List Nat := [1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_7694903 : Nat := 118140960795 + 7694903 * 2 ^ 59
def prefixEnd_7694903 : Nat := 4983230072969 + 3 ^ 40 * 7694903 * 2
def baseEnd_7694903 : Nat := 3951183828724012390324291

theorem tailTrace_7694903 : CollatzResearch.WordTrace tailWord_7694903 prefixEnd_7694903 3951183828724012390324291 := by
  unfold tailWord_7694903
  simp only [CollatzResearch.WordTrace]
  refine ⟨280656169241688090649913363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187104112827792060433275575 280656169241688090649913363)
  ·
    refine ⟨420984253862532135974870045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280656169241688090649913363 420984253862532135974870045)
    ·
      refine ⟨157869095198449550990576267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420984253862532135974870045 157869095198449550990576267)
      ·
        refine ⟨236803642797674326485864401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157869095198449550990576267 236803642797674326485864401)
        ·
          refine ⟨177602732098255744864398301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236803642797674326485864401 177602732098255744864398301)
          ·
            refine ⟨66601024536845904324149363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177602732098255744864398301 66601024536845904324149363)
            ·
              refine ⟨99901536805268856486224045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66601024536845904324149363 99901536805268856486224045)
              ·
                refine ⟨37463076301975821182334017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99901536805268856486224045 37463076301975821182334017)
                ·
                  refine ⟨28097307226481865886750513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37463076301975821182334017 28097307226481865886750513)
                  ·
                    refine ⟨21072980419861399415062885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28097307226481865886750513 21072980419861399415062885)
                    ·
                      refine ⟨3951183828724012390324291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21072980419861399415062885 3951183828724012390324291)
                      ·
                        rfl

theorem cell23_7694903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_7694903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694903 prefixEnd_7694903 := by exact prefixLift 7694903
  have htrace : WordTrace (prefixWord ++ tailWord_7694903) baseStart_7694903 baseEnd_7694903 := by
    simpa [prefixWord, tailWord_7694903, baseEnd_7694903] using wordTrace_append hprefix tailTrace_7694903
  have hstable : (prefixWord ++ tailWord_7694903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694903).length < 2 ^ (prefixWord ++ tailWord_7694903).sum := by decide
  have hdescent : baseEnd_7694903 < baseStart_7694903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694923 : List Nat := [1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 3]
def baseStart_7694923 : Nat := 118140960795 + 7694923 * 2 ^ 59
def prefixEnd_7694923 : Nat := 4983230072969 + 3 ^ 40 * 7694923 * 2
def baseEnd_7694923 : Nat := 3951194098337102312074199

theorem tailTrace_7694923 : CollatzResearch.WordTrace tailWord_7694923 prefixEnd_7694923 3951194098337102312074199 := by
  unfold tailWord_7694923
  simp only [CollatzResearch.WordTrace]
  refine ⟨280656898701615634065641423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187104599134410422710427615 280656898701615634065641423)
  ·
    refine ⟨420985348052423451098462135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280656898701615634065641423 420985348052423451098462135)
    ·
      refine ⟨631478022078635176647693203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420985348052423451098462135 631478022078635176647693203)
      ·
        refine ⟨947217033117952764971539805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631478022078635176647693203 947217033117952764971539805)
        ·
          refine ⟨355206387419232286864327427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947217033117952764971539805 355206387419232286864327427)
          ·
            refine ⟨532809581128848430296491141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355206387419232286864327427 532809581128848430296491141)
            ·
              refine ⟨99901796461659080680592089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 532809581128848430296491141 99901796461659080680592089)
              ·
                refine ⟨74926347346244310510444067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99901796461659080680592089 74926347346244310510444067)
                ·
                  refine ⟨112389521019366465765666101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74926347346244310510444067 112389521019366465765666101)
                  ·
                    refine ⟨10536517595565606165531197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112389521019366465765666101 10536517595565606165531197)
                    ·
                      refine ⟨3951194098337102312074199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536517595565606165531197 3951194098337102312074199)
                      ·
                        rfl

theorem cell23_7694923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 3].length) (baseStart_7694923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694923 prefixEnd_7694923 := by exact prefixLift 7694923
  have htrace : WordTrace (prefixWord ++ tailWord_7694923) baseStart_7694923 baseEnd_7694923 := by
    simpa [prefixWord, tailWord_7694923, baseEnd_7694923] using wordTrace_append hprefix tailTrace_7694923
  have hstable : (prefixWord ++ tailWord_7694923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694923).length < 2 ^ (prefixWord ++ tailWord_7694923).sum := by decide
  have hdescent : baseEnd_7694923 < baseStart_7694923 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694947 : List Nat := [1, 1, 1, 5, 1, 2, 5, 2, 5]
def baseStart_7694947 : Nat := 118140960795 + 7694947 * 2 ^ 59
def prefixEnd_7694947 : Nat := 4983230072969 + 3 ^ 40 * 7694947 * 2
def baseEnd_7694947 : Nat := 439022935763645579797121

theorem tailTrace_7694947 : CollatzResearch.WordTrace tailWord_7694947 prefixEnd_7694947 439022935763645579797121 := by
  unfold tailWord_7694947
  simp only [CollatzResearch.WordTrace]
  refine ⟨280657774053528686164515095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187105182702352457443010063 280657774053528686164515095)
  ·
    refine ⟨420986661080293029246772643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280657774053528686164515095 420986661080293029246772643)
    ·
      refine ⟨631479991620439543870158965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420986661080293029246772643 631479991620439543870158965)
      ·
        refine ⟨59201249214416207237827403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 631479991620439543870158965 59201249214416207237827403)
        ·
          refine ⟨88801873821624310856741105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59201249214416207237827403 88801873821624310856741105)
          ·
            refine ⟨66601405366218233142555829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88801873821624310856741105 66601405366218233142555829)
            ·
              refine ⟨6243881753082959357114609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66601405366218233142555829 6243881753082959357114609)
              ·
                refine ⟨4682911314812219517835957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6243881753082959357114609 4682911314812219517835957)
                ·
                  refine ⟨439022935763645579797121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4682911314812219517835957 439022935763645579797121)
                  ·
                    rfl

theorem cell23_7694947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 5, 2, 5].length) (baseStart_7694947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694947 prefixEnd_7694947 := by exact prefixLift 7694947
  have htrace : WordTrace (prefixWord ++ tailWord_7694947) baseStart_7694947 baseEnd_7694947 := by
    simpa [prefixWord, tailWord_7694947, baseEnd_7694947] using wordTrace_append hprefix tailTrace_7694947
  have hstable : (prefixWord ++ tailWord_7694947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694947).length < 2 ^ (prefixWord ++ tailWord_7694947).sum := by decide
  have hdescent : baseEnd_7694947 < baseStart_7694947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694958 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_7694958 : Nat := 118140960795 + 7694958 * 2 ^ 59
def prefixEnd_7694958 : Nat := 4983230072969 + 3 ^ 40 * 7694958 * 2
def baseEnd_7694958 : Nat := 3951212070160009675136539

theorem tailTrace_7694958 : CollatzResearch.WordTrace tailWord_7694958 prefixEnd_7694958 3951212070160009675136539 := by
  unfold tailWord_7694958
  simp only [CollatzResearch.WordTrace]
  refine ⟨35082271907061104380395691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187105450170992556695443685 35082271907061104380395691)
  ·
    refine ⟨52623407860591656570593537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35082271907061104380395691 52623407860591656570593537)
    ·
      refine ⟨39467555895443742427945153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52623407860591656570593537 39467555895443742427945153)
      ·
        refine ⟨29600666921582806820958865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39467555895443742427945153 29600666921582806820958865)
        ·
          refine ⟨22200500191187105115719149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29600666921582806820958865 22200500191187105115719149)
          ·
            refine ⟨8325187571695164418394681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22200500191187105115719149 8325187571695164418394681)
            ·
              refine ⟨6243890678771373313796011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325187571695164418394681 6243890678771373313796011)
              ·
                refine ⟨9365836018157059970694017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6243890678771373313796011 9365836018157059970694017)
                ·
                  refine ⟨7024377013617794978020513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9365836018157059970694017 7024377013617794978020513)
                  ·
                    refine ⟨5268282760213346233515385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024377013617794978020513 5268282760213346233515385)
                    ·
                      refine ⟨3951212070160009675136539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268282760213346233515385 3951212070160009675136539)
                      ·
                        rfl

theorem cell23_7694958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_7694958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694958 prefixEnd_7694958 := by exact prefixLift 7694958
  have htrace : WordTrace (prefixWord ++ tailWord_7694958) baseStart_7694958 baseEnd_7694958 := by
    simpa [prefixWord, tailWord_7694958, baseEnd_7694958] using wordTrace_append hprefix tailTrace_7694958
  have hstable : (prefixWord ++ tailWord_7694958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694958).length < 2 ^ (prefixWord ++ tailWord_7694958).sum := by decide
  have hdescent : baseEnd_7694958 < baseStart_7694958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694963 : List Nat := [1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4]
def baseStart_7694963 : Nat := 118140960795 + 7694963 * 2 ^ 59
def prefixEnd_7694963 : Nat := 4983230072969 + 3 ^ 40 * 7694963 * 2
def baseEnd_7694963 : Nat := 3951214637563282155574015

theorem tailTrace_7694963 : CollatzResearch.WordTrace tailWord_7694963 prefixEnd_7694963 3951214637563282155574015 := by
  unfold tailWord_7694963
  simp only [CollatzResearch.WordTrace]
  refine ⟨280658357621470720897097543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187105571747647147264731695 280658357621470720897097543)
  ·
    refine ⟨420987536432206081345646315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280658357621470720897097543 420987536432206081345646315)
    ·
      refine ⟨631481304648309122018469473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420987536432206081345646315 631481304648309122018469473)
      ·
        refine ⟨473610978486231841513852105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631481304648309122018469473 473610978486231841513852105)
        ·
          refine ⟨355208233864673881135389079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473610978486231841513852105 355208233864673881135389079)
          ·
            refine ⟨532812350797010821703083619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355208233864673881135389079 532812350797010821703083619)
            ·
              refine ⟨799218526195516232554625429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532812350797010821703083619 799218526195516232554625429)
              ·
                refine ⟨37463368415414823400998067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 799218526195516232554625429 37463368415414823400998067)
                ·
                  refine ⟨56195052623122235101497101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37463368415414823400998067 56195052623122235101497101)
                  ·
                    refine ⟨21073144733670838163061413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56195052623122235101497101 21073144733670838163061413)
                    ·
                      refine ⟨3951214637563282155574015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21073144733670838163061413 3951214637563282155574015)
                      ·
                        rfl

theorem cell23_7694963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_7694963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694963 prefixEnd_7694963 := by exact prefixLift 7694963
  have htrace : WordTrace (prefixWord ++ tailWord_7694963) baseStart_7694963 baseEnd_7694963 := by
    simpa [prefixWord, tailWord_7694963, baseEnd_7694963] using wordTrace_append hprefix tailTrace_7694963
  have hstable : (prefixWord ++ tailWord_7694963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694963).length < 2 ^ (prefixWord ++ tailWord_7694963).sum := by decide
  have hdescent : baseEnd_7694963 < baseStart_7694963 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7694993 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_7694993 : Nat := 118140960795 + 7694993 * 2 ^ 59
def prefixEnd_7694993 : Nat := 4983230072969 + 3 ^ 40 * 7694993 * 2
def baseEnd_7694993 : Nat := 3951230041982917038198877

theorem tailTrace_7694993 : CollatzResearch.WordTrace tailWord_7694993 prefixEnd_7694993 3951230041982917038198877 := by
  unfold tailWord_7694993
  simp only [CollatzResearch.WordTrace]
  refine ⟨280659451811362036020689633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187106301207574690680459755 280659451811362036020689633)
  ·
    refine ⟨210494588858521527015517225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280659451811362036020689633 210494588858521527015517225)
    ·
      refine ⟨157870941643891145261637919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210494588858521527015517225 157870941643891145261637919)
      ·
        refine ⟨236806412465836717892456879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157870941643891145261637919 236806412465836717892456879)
        ·
          refine ⟨355209618698755076838685319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236806412465836717892456879 355209618698755076838685319)
          ·
            refine ⟨532814428048132615258027979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355209618698755076838685319 532814428048132615258027979)
            ·
              refine ⟨799221642072198922887041969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532814428048132615258027979 799221642072198922887041969)
              ·
                refine ⟨599416231554149192165281477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799221642072198922887041969 599416231554149192165281477)
                ·
                  refine ⟨112390543416402973530990277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599416231554149192165281477 112390543416402973530990277)
                  ·
                    refine ⟨21073226890575557537060677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112390543416402973530990277 21073226890575557537060677)
                    ·
                      refine ⟨3951230041982917038198877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21073226890575557537060677 3951230041982917038198877)
                      ·
                        rfl

theorem cell23_7694993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_7694993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7694993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7694993 prefixEnd_7694993 := by exact prefixLift 7694993
  have htrace : WordTrace (prefixWord ++ tailWord_7694993) baseStart_7694993 baseEnd_7694993 := by
    simpa [prefixWord, tailWord_7694993, baseEnd_7694993] using wordTrace_append hprefix tailTrace_7694993
  have hstable : (prefixWord ++ tailWord_7694993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7694993).length < 2 ^ (prefixWord ++ tailWord_7694993).sum := by decide
  have hdescent : baseEnd_7694993 < baseStart_7694993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7694993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695057 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 4, 3, 2]
def baseStart_7695057 : Nat := 118140960795 + 7695057 * 2 ^ 59
def prefixEnd_7695057 : Nat := 4983230072969 + 3 ^ 40 * 7695057 * 2
def baseEnd_7695057 : Nat := 3951262904744804787798583

theorem tailTrace_7695057 : CollatzResearch.WordTrace tailWord_7695057 prefixEnd_7695057 3951262904744804787798583 := by
  unfold tailWord_7695057
  simp only [CollatzResearch.WordTrace]
  refine ⟨280661786083130174951019425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187107857388753449967346283 280661786083130174951019425)
  ·
    refine ⟨210496339562347631213264569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280661786083130174951019425 210496339562347631213264569)
    ·
      refine ⟨157872254671760723409948427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210496339562347631213264569 157872254671760723409948427)
      ·
        refine ⟨236808382007641085114922641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157872254671760723409948427 236808382007641085114922641)
        ·
          refine ⟨177606286505730813836191981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236808382007641085114922641 177606286505730813836191981)
          ·
            refine ⟨66602357439649055188571993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177606286505730813836191981 66602357439649055188571993)
            ·
              refine ⟨49951768079736791391428995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66602357439649055188571993 49951768079736791391428995)
              ·
                refine ⟨74927652119605187087143493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49951768079736791391428995 74927652119605187087143493)
                ·
                  refine ⟨14048934772425972578839405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74927652119605187087143493 14048934772425972578839405)
                  ·
                    refine ⟨5268350539659739717064777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14048934772425972578839405 5268350539659739717064777)
                    ·
                      refine ⟨3951262904744804787798583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268350539659739717064777 3951262904744804787798583)
                      ·
                        rfl

theorem cell23_7695057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_7695057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695057 prefixEnd_7695057 := by exact prefixLift 7695057
  have htrace : WordTrace (prefixWord ++ tailWord_7695057) baseStart_7695057 baseEnd_7695057 := by
    simpa [prefixWord, tailWord_7695057, baseEnd_7695057] using wordTrace_append hprefix tailTrace_7695057
  have hstable : (prefixWord ++ tailWord_7695057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695057).length < 2 ^ (prefixWord ++ tailWord_7695057).sum := by decide
  have hdescent : baseEnd_7695057 < baseStart_7695057 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695064 : List Nat := [2, 1, 2, 2, 3, 3, 2, 1, 3, 1, 3]
def baseStart_7695064 : Nat := 118140960795 + 7695064 * 2 ^ 59
def prefixEnd_7695064 : Nat := 4983230072969 + 3 ^ 40 * 7695064 * 2
def baseEnd_7695064 : Nat := 3951266499109386260411051

theorem tailTrace_7695064 : CollatzResearch.WordTrace tailWord_7695064 prefixEnd_7695064 3951266499109386260411051 := by
  unfold tailWord_7695064
  simp only [CollatzResearch.WordTrace]
  refine ⟨140331020697052407573262123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187108027596069876764349497 140331020697052407573262123)
  ·
    refine ⟨210496531045578611359893185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140331020697052407573262123 210496531045578611359893185)
    ·
      refine ⟨157872398284183958519919889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210496531045578611359893185 157872398284183958519919889)
      ·
        refine ⟨118404298713137968889939917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157872398284183958519919889 118404298713137968889939917)
        ·
          refine ⟨44401612017426738333727469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118404298713137968889939917 44401612017426738333727469)
          ·
            refine ⟨16650604506535026875147801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44401612017426738333727469 16650604506535026875147801)
            ·
              refine ⟨12487953379901270156360851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16650604506535026875147801 12487953379901270156360851)
              ·
                refine ⟨18731930069851905234541277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12487953379901270156360851 18731930069851905234541277)
                ·
                  refine ⟨7024473776194464462952979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18731930069851905234541277 7024473776194464462952979)
                  ·
                    refine ⟨10536710664291696694429469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7024473776194464462952979 10536710664291696694429469)
                    ·
                      refine ⟨3951266499109386260411051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536710664291696694429469 3951266499109386260411051)
                      ·
                        rfl

theorem cell23_7695064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 2, 1, 3, 1, 3].length) (baseStart_7695064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695064 prefixEnd_7695064 := by exact prefixLift 7695064
  have htrace : WordTrace (prefixWord ++ tailWord_7695064) baseStart_7695064 baseEnd_7695064 := by
    simpa [prefixWord, tailWord_7695064, baseEnd_7695064] using wordTrace_append hprefix tailTrace_7695064
  have hstable : (prefixWord ++ tailWord_7695064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695064).length < 2 ^ (prefixWord ++ tailWord_7695064).sum := by decide
  have hdescent : baseEnd_7695064 < baseStart_7695064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695087 : List Nat := [1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 4]
def baseStart_7695087 : Nat := 118140960795 + 7695087 * 2 ^ 59
def prefixEnd_7695087 : Nat := 4983230072969 + 3 ^ 40 * 7695087 * 2
def baseEnd_7695087 : Nat := 3951278309164439670423445

theorem tailTrace_7695087 : CollatzResearch.WordTrace tailWord_7695087 prefixEnd_7695087 3951278309164439670423445 := by
  unfold tailWord_7695087
  simp only [CollatzResearch.WordTrace]
  refine ⟨280662880273021490074611515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187108586848680993383074343 280662880273021490074611515)
  ·
    refine ⟨420994320409532235111917273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280662880273021490074611515 420994320409532235111917273)
    ·
      refine ⟨315745740307149176333937955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420994320409532235111917273 315745740307149176333937955)
      ·
        refine ⟨473618610460723764500906933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315745740307149176333937955 473618610460723764500906933)
        ·
          refine ⟨44401744730692852921960025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 473618610460723764500906933 44401744730692852921960025)
          ·
            refine ⟨33301308548019639691470019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44401744730692852921960025 33301308548019639691470019)
            ·
              refine ⟨49951962822029459537205029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33301308548019639691470019 49951962822029459537205029)
              ·
                refine ⟨9365993029130523663225943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49951962822029459537205029 9365993029130523663225943)
                ·
                  refine ⟨14048989543695785494838915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9365993029130523663225943 14048989543695785494838915)
                  ·
                    refine ⟨21073484315543678242258373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14048989543695785494838915 21073484315543678242258373)
                    ·
                      refine ⟨3951278309164439670423445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21073484315543678242258373 3951278309164439670423445)
                      ·
                        rfl

theorem cell23_7695087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_7695087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695087 prefixEnd_7695087 := by exact prefixLift 7695087
  have htrace : WordTrace (prefixWord ++ tailWord_7695087) baseStart_7695087 baseEnd_7695087 := by
    simpa [prefixWord, tailWord_7695087, baseEnd_7695087] using wordTrace_append hprefix tailTrace_7695087
  have hstable : (prefixWord ++ tailWord_7695087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695087).length < 2 ^ (prefixWord ++ tailWord_7695087).sum := by decide
  have hdescent : baseEnd_7695087 < baseStart_7695087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695092 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_7695092 : Nat := 118140960795 + 7695092 * 2 ^ 59
def prefixEnd_7695092 : Nat := 4983230072969 + 3 ^ 40 * 7695092 * 2
def baseEnd_7695092 : Nat := 1317093625522570716953641

theorem tailTrace_7695092 : CollatzResearch.WordTrace tailWord_7695092 prefixEnd_7695092 1317093625522570716953641 := by
  unfold tailWord_7695092
  simp only [CollatzResearch.WordTrace]
  refine ⟨140331531319001687964271765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187108708425335583952362353 140331531319001687964271765)
  ·
    refine ⟨6578040530578204123325239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140331531319001687964271765 6578040530578204123325239)
    ·
      refine ⟨9867060795867306184987859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6578040530578204123325239 9867060795867306184987859)
      ·
        refine ⟨14800591193800959277481789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9867060795867306184987859 14800591193800959277481789)
        ·
          refine ⟨5550221697675359729055671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14800591193800959277481789 5550221697675359729055671)
          ·
            refine ⟨8325332546513039593583507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550221697675359729055671 8325332546513039593583507)
            ·
              refine ⟨12487998819769559390375261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8325332546513039593583507 12487998819769559390375261)
              ·
                refine ⟨4682999557413584771390723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12487998819769559390375261 4682999557413584771390723)
                ·
                  refine ⟨7024499336120377157086085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4682999557413584771390723 7024499336120377157086085)
                  ·
                    refine ⟨1317093625522570716953641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024499336120377157086085 1317093625522570716953641)
                    ·
                      rfl

theorem cell23_7695092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_7695092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695092 prefixEnd_7695092 := by exact prefixLift 7695092
  have htrace : WordTrace (prefixWord ++ tailWord_7695092) baseStart_7695092 baseEnd_7695092 := by
    simpa [prefixWord, tailWord_7695092, baseEnd_7695092] using wordTrace_append hprefix tailTrace_7695092
  have hstable : (prefixWord ++ tailWord_7695092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695092).length < 2 ^ (prefixWord ++ tailWord_7695092).sum := by decide
  have hdescent : baseEnd_7695092 < baseStart_7695092 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695121 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 1, 2, 2]
def baseStart_7695121 : Nat := 118140960795 + 7695121 * 2 ^ 59
def prefixEnd_7695121 : Nat := 4983230072969 + 3 ^ 40 * 7695121 * 2
def baseEnd_7695121 : Nat := 3951295767506692537398289

theorem tailTrace_7695121 : CollatzResearch.WordTrace tailWord_7695121 prefixEnd_7695121 3951295767506692537398289 := by
  unfold tailWord_7695121
  simp only [CollatzResearch.WordTrace]
  refine ⟨280664120354898313881349217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187109413569932209254232811 280664120354898313881349217)
  ·
    refine ⟨210498090266173735411011913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280664120354898313881349217 210498090266173735411011913)
    ·
      refine ⟨157873567699630301558258935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210498090266173735411011913 157873567699630301558258935)
      ·
        refine ⟨236810351549445452337388403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157873567699630301558258935 236810351549445452337388403)
        ·
          refine ⟨355215527324168178506082605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236810351549445452337388403 355215527324168178506082605)
          ·
            refine ⟨133205822746563066939780977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355215527324168178506082605 133205822746563066939780977)
            ·
              refine ⟨99904367059922300204835733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133205822746563066939780977 99904367059922300204835733)
              ·
                refine ⟨4683017205933857822101675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99904367059922300204835733 4683017205933857822101675)
                ·
                  refine ⟨7024525808900786733152513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683017205933857822101675 7024525808900786733152513)
                  ·
                    refine ⟨5268394356675590049864385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024525808900786733152513 5268394356675590049864385)
                    ·
                      refine ⟨3951295767506692537398289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268394356675590049864385 3951295767506692537398289)
                      ·
                        rfl

theorem cell23_7695121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_7695121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695121 prefixEnd_7695121 := by exact prefixLift 7695121
  have htrace : WordTrace (prefixWord ++ tailWord_7695121) baseStart_7695121 baseEnd_7695121 := by
    simpa [prefixWord, tailWord_7695121, baseEnd_7695121] using wordTrace_append hprefix tailTrace_7695121
  have hstable : (prefixWord ++ tailWord_7695121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695121).length < 2 ^ (prefixWord ++ tailWord_7695121).sum := by decide
  have hdescent : baseEnd_7695121 < baseStart_7695121 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695127 : List Nat := [1, 1, 3, 4, 3, 1, 2, 8]
def baseStart_7695127 : Nat := 118140960795 + 7695127 * 2 ^ 59
def prefixEnd_7695127 : Nat := 4983230072969 + 3 ^ 40 * 7695127 * 2
def baseEnd_7695127 : Nat := 146344401792245167182343

theorem tailTrace_7695127 : CollatzResearch.WordTrace tailWord_7695127 prefixEnd_7695127 146344401792245167182343 := by
  unfold tailWord_7695127
  simp only [CollatzResearch.WordTrace]
  refine ⟨280664339192876576906067635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187109559461917717937378423 280664339192876576906067635)
  ·
    refine ⟨420996508789314865359101453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280664339192876576906067635 420996508789314865359101453)
    ·
      refine ⟨157873690795993074509663045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420996508789314865359101453 157873690795993074509663045)
      ·
        refine ⟨29601317024248701470561821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157873690795993074509663045 29601317024248701470561821)
        ·
          refine ⟨11100493884093263051460683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29601317024248701470561821 11100493884093263051460683)
          ·
            refine ⟨16650740826139894577191025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100493884093263051460683 16650740826139894577191025)
            ·
              refine ⟨12488055619604920932893269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16650740826139894577191025 12488055619604920932893269)
              ·
                refine ⟨146344401792245167182343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12488055619604920932893269 146344401792245167182343)
                ·
                  rfl

theorem cell23_7695127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 8].length) (baseStart_7695127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695127 prefixEnd_7695127 := by exact prefixLift 7695127
  have htrace : WordTrace (prefixWord ++ tailWord_7695127) baseStart_7695127 baseEnd_7695127 := by
    simpa [prefixWord, tailWord_7695127, baseEnd_7695127] using wordTrace_append hprefix tailTrace_7695127
  have hstable : (prefixWord ++ tailWord_7695127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695127).length < 2 ^ (prefixWord ++ tailWord_7695127).sum := by decide
  have hdescent : baseEnd_7695127 < baseStart_7695127 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695130 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6]
def baseStart_7695130 : Nat := 118140960795 + 7695130 * 2 ^ 59
def prefixEnd_7695130 : Nat := 4983230072969 + 3 ^ 40 * 7695130 * 2
def baseEnd_7695130 : Nat := 3951300388832583002185747

theorem tailTrace_7695130 : CollatzResearch.WordTrace tailWord_7695130 prefixEnd_7695130 3951300388832583002185747 := by
  unfold tailWord_7695130
  simp only [CollatzResearch.WordTrace]
  refine ⟨70166112152966427104606711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187109632407910472278951229 70166112152966427104606711)
  ·
    refine ⟨105249168229449640656910067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70166112152966427104606711 105249168229449640656910067)
    ·
      refine ⟨157873752344174460985365101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105249168229449640656910067 157873752344174460985365101)
      ·
        refine ⟨59202657129065422869511913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157873752344174460985365101 59202657129065422869511913)
        ·
          refine ⟨44401992846799067152133935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59202657129065422869511913 44401992846799067152133935)
          ·
            refine ⟨66602989270198600728200903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44401992846799067152133935 66602989270198600728200903)
            ·
              refine ⟨99904483905297901092301355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66602989270198600728200903 99904483905297901092301355)
              ·
                refine ⟨149856725857946851638452033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99904483905297901092301355 149856725857946851638452033)
                ·
                  refine ⟨112392544393460138728839025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149856725857946851638452033 112392544393460138728839025)
                  ·
                    refine ⟨84294408295095104046629269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112392544393460138728839025 84294408295095104046629269)
                    ·
                      refine ⟨3951300388832583002185747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84294408295095104046629269 3951300388832583002185747)
                      ·
                        rfl

theorem cell23_7695130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_7695130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695130 prefixEnd_7695130 := by exact prefixLift 7695130
  have htrace : WordTrace (prefixWord ++ tailWord_7695130) baseStart_7695130 baseEnd_7695130 := by
    simpa [prefixWord, tailWord_7695130, baseEnd_7695130] using wordTrace_append hprefix tailTrace_7695130
  have hstable : (prefixWord ++ tailWord_7695130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695130).length < 2 ^ (prefixWord ++ tailWord_7695130).sum := by decide
  have hdescent : baseEnd_7695130 < baseStart_7695130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695137 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_7695137 : Nat := 118140960795 + 7695137 * 2 ^ 59
def prefixEnd_7695137 : Nat := 4983230072969 + 3 ^ 40 * 7695137 * 2
def baseEnd_7695137 : Nat := 3951303983197164474798215

theorem tailTrace_7695137 : CollatzResearch.WordTrace tailWord_7695137 prefixEnd_7695137 3951303983197164474798215 := by
  unfold tailWord_7695137
  simp only [CollatzResearch.WordTrace]
  refine ⟨280664703922840348613931665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187109802615226899075954443 280664703922840348613931665)
  ·
    refine ⟨210498527942130261460448749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280664703922840348613931665 210498527942130261460448749)
    ·
      refine ⟨78936947978298848047668281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210498527942130261460448749 78936947978298848047668281)
      ·
        refine ⟨59202710983724136035751211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78936947978298848047668281 59202710983724136035751211)
        ·
          refine ⟨88804066475586204053626817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59202710983724136035751211 88804066475586204053626817)
          ·
            refine ⟨66603049856689653040220113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88804066475586204053626817 66603049856689653040220113)
            ·
              refine ⟨49952287392517239780165085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66603049856689653040220113 49952287392517239780165085)
              ·
                refine ⟨18732107772193964917561907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49952287392517239780165085 18732107772193964917561907)
                ·
                  refine ⟨28098161658290947376342861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18732107772193964917561907 28098161658290947376342861)
                  ·
                    refine ⟨10536810621859105266128573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28098161658290947376342861 10536810621859105266128573)
                    ·
                      refine ⟨3951303983197164474798215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536810621859105266128573 3951303983197164474798215)
                      ·
                        rfl

theorem cell23_7695137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_7695137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695137 prefixEnd_7695137 := by exact prefixLift 7695137
  have htrace : WordTrace (prefixWord ++ tailWord_7695137) baseStart_7695137 baseEnd_7695137 := by
    simpa [prefixWord, tailWord_7695137, baseEnd_7695137] using wordTrace_append hprefix tailTrace_7695137
  have hstable : (prefixWord ++ tailWord_7695137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695137).length < 2 ^ (prefixWord ++ tailWord_7695137).sum := by decide
  have hdescent : baseEnd_7695137 < baseStart_7695137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695158 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_7695158 : Nat := 118140960795 + 7695158 * 2 ^ 59
def prefixEnd_7695158 : Nat := 4983230072969 + 3 ^ 40 * 7695158 * 2
def baseEnd_7695158 : Nat := 3951314766290908892635619

theorem tailTrace_7695158 : CollatzResearch.WordTrace tailWord_7695158 prefixEnd_7695158 3951314766290908892635619 := by
  unfold tailWord_7695158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17541591865985266825027883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187110313237176179466964085 17541591865985266825027883)
  ·
    refine ⟨26312387798977900237541825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17541591865985266825027883 26312387798977900237541825)
    ·
      refine ⟨19734290849233425178156369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26312387798977900237541825 19734290849233425178156369)
      ·
        refine ⟨14800718136925068883617277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19734290849233425178156369 14800718136925068883617277)
        ·
          refine ⟨5550269301346900831356479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14800718136925068883617277 5550269301346900831356479)
          ·
            refine ⟨8325403952020351247034719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550269301346900831356479 8325403952020351247034719)
            ·
              refine ⟨12488105928030526870552079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8325403952020351247034719 12488105928030526870552079)
              ·
                refine ⟨18732158892045790305828119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488105928030526870552079 18732158892045790305828119)
                ·
                  refine ⟨28098238338068685458742179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18732158892045790305828119 28098238338068685458742179)
                  ·
                    refine ⟨42147357507103028188113269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28098238338068685458742179 42147357507103028188113269)
                    ·
                      refine ⟨3951314766290908892635619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42147357507103028188113269 3951314766290908892635619)
                      ·
                        rfl

theorem cell23_7695158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_7695158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695158 prefixEnd_7695158 := by exact prefixLift 7695158
  have htrace : WordTrace (prefixWord ++ tailWord_7695158) baseStart_7695158 baseEnd_7695158 := by
    simpa [prefixWord, tailWord_7695158, baseEnd_7695158] using wordTrace_append hprefix tailTrace_7695158
  have hstable : (prefixWord ++ tailWord_7695158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695158).length < 2 ^ (prefixWord ++ tailWord_7695158).sum := by decide
  have hdescent : baseEnd_7695158 < baseStart_7695158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695172 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_7695172 : Nat := 118140960795 + 7695172 * 2 ^ 59
def prefixEnd_7695172 : Nat := 4983230072969 + 3 ^ 40 * 7695172 * 2
def baseEnd_7695172 : Nat := 3951321955020071837860555

theorem tailTrace_7695172 : CollatzResearch.WordTrace tailWord_7695172 prefixEnd_7695172 3951321955020071837860555 := by
  unfold tailWord_7695172
  simp only [CollatzResearch.WordTrace]
  refine ⟨140332990238856774795727885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187110653651809033060970513 140332990238856774795727885)
  ·
    refine ⟨52624871339571290548397957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140332990238856774795727885 52624871339571290548397957)
    ·
      refine ⟨9867163376169616977824617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52624871339571290548397957 9867163376169616977824617)
      ·
        refine ⟨7400372532127212733368463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9867163376169616977824617 7400372532127212733368463)
        ·
          refine ⟨11100558798190819100052695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7400372532127212733368463 11100558798190819100052695)
          ·
            refine ⟨16650838197286228650079043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11100558798190819100052695 16650838197286228650079043)
            ·
              refine ⟨24976257295929342975118565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16650838197286228650079043 24976257295929342975118565)
              ·
                refine ⟨4683048242986751807834731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24976257295929342975118565 4683048242986751807834731)
                ·
                  refine ⟨7024572364480127711752097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683048242986751807834731 7024572364480127711752097)
                  ·
                    refine ⟨5268429273360095783814073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024572364480127711752097 5268429273360095783814073)
                    ·
                      refine ⟨3951321955020071837860555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268429273360095783814073 3951321955020071837860555)
                      ·
                        rfl

theorem cell23_7695172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_7695172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695172 prefixEnd_7695172 := by exact prefixLift 7695172
  have htrace : WordTrace (prefixWord ++ tailWord_7695172) baseStart_7695172 baseEnd_7695172 := by
    simpa [prefixWord, tailWord_7695172, baseEnd_7695172] using wordTrace_append hprefix tailTrace_7695172
  have hstable : (prefixWord ++ tailWord_7695172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695172).length < 2 ^ (prefixWord ++ tailWord_7695172).sum := by decide
  have hdescent : baseEnd_7695172 < baseStart_7695172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695194 : List Nat := [3, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2]
def baseStart_7695194 : Nat := 118140960795 + 7695194 * 2 ^ 59
def prefixEnd_7695194 : Nat := 4983230072969 + 3 ^ 40 * 7695194 * 2
def baseEnd_7695194 : Nat := 3951333251594470751785453

theorem tailTrace_7695194 : CollatzResearch.WordTrace tailWord_7695194 prefixEnd_7695194 3951333251594470751785453 := by
  unfold tailWord_7695194
  simp only [CollatzResearch.WordTrace]
  refine ⟨70166695720908461837189159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187111188589089231565837757 70166695720908461837189159)
  ·
    refine ⟨105250043581362692755783739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70166695720908461837189159 105250043581362692755783739)
    ·
      refine ⟨157875065372044039133675609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105250043581362692755783739 157875065372044039133675609)
      ·
        refine ⟨118406299029033029350256707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157875065372044039133675609 118406299029033029350256707)
        ·
          refine ⟨177609448543549544025385061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118406299029033029350256707 177609448543549544025385061)
          ·
            refine ⟨33301771601915539504759699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177609448543549544025385061 33301771601915539504759699)
            ·
              refine ⟨49952657402873309257139549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33301771601915539504759699 49952657402873309257139549)
              ·
                refine ⟨18732246526077490971427331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49952657402873309257139549 18732246526077490971427331)
                ·
                  refine ⟨28098369789116236457140997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18732246526077490971427331 28098369789116236457140997)
                  ·
                    refine ⟨5268444335459294335713937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28098369789116236457140997 5268444335459294335713937)
                    ·
                      refine ⟨3951333251594470751785453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268444335459294335713937 3951333251594470751785453)
                      ·
                        rfl

theorem cell23_7695194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_7695194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695194 prefixEnd_7695194 := by exact prefixLift 7695194
  have htrace : WordTrace (prefixWord ++ tailWord_7695194) baseStart_7695194 baseEnd_7695194 := by
    simpa [prefixWord, tailWord_7695194, baseEnd_7695194] using wordTrace_append hprefix tailTrace_7695194
  have hstable : (prefixWord ++ tailWord_7695194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695194).length < 2 ^ (prefixWord ++ tailWord_7695194).sum := by decide
  have hdescent : baseEnd_7695194 < baseStart_7695194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695227 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 3]
def baseStart_7695227 : Nat := 118140960795 + 7695227 * 2 ^ 59
def prefixEnd_7695227 : Nat := 4983230072969 + 3 ^ 40 * 7695227 * 2
def baseEnd_7695227 : Nat := 3951350196456069122672801

theorem tailTrace_7695227 : CollatzResearch.WordTrace tailWord_7695227 prefixEnd_7695227 3951350196456069122672801 := by
  unfold tailWord_7695227
  simp only [CollatzResearch.WordTrace]
  refine ⟨280667986492514293984707935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187111990995009529323138623 280667986492514293984707935)
  ·
    refine ⟨421001979738771440977061903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280667986492514293984707935 421001979738771440977061903)
    ·
      refine ⟨631502969608157161465592855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421001979738771440977061903 631502969608157161465592855)
      ·
        refine ⟨947254454412235742198389283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631502969608157161465592855 947254454412235742198389283)
        ·
          refine ⟨1420881681618353613297583925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947254454412235742198389283 1420881681618353613297583925)
          ·
            refine ⟨133207657651720651246648493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1420881681618353613297583925 133207657651720651246648493)
            ·
              refine ⟨49952871619395244217493185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133207657651720651246648493 49952871619395244217493185)
              ·
                refine ⟨37464653714546433163119889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49952871619395244217493185 37464653714546433163119889)
                ·
                  refine ⟨28098490285909824872339917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37464653714546433163119889 28098490285909824872339917)
                  ·
                    refine ⟨10536933857216184327127469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28098490285909824872339917 10536933857216184327127469)
                    ·
                      refine ⟨3951350196456069122672801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10536933857216184327127469 3951350196456069122672801)
                      ·
                        rfl

theorem cell23_7695227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 3].length) (baseStart_7695227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695227 prefixEnd_7695227 := by exact prefixLift 7695227
  have htrace : WordTrace (prefixWord ++ tailWord_7695227) baseStart_7695227 baseEnd_7695227 := by
    simpa [prefixWord, tailWord_7695227, baseEnd_7695227] using wordTrace_append hprefix tailTrace_7695227
  have hstable : (prefixWord ++ tailWord_7695227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695227).length < 2 ^ (prefixWord ++ tailWord_7695227).sum := by decide
  have hdescent : baseEnd_7695227 < baseStart_7695227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695267 : List Nat := [1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4]
def baseStart_7695267 : Nat := 118140960795 + 7695267 * 2 ^ 59
def prefixEnd_7695267 : Nat := 4983230072969 + 3 ^ 40 * 7695267 * 2
def baseEnd_7695267 : Nat := 3951370735682248966172617

theorem tailTrace_7695267 : CollatzResearch.WordTrace tailWord_7695267 prefixEnd_7695267 3951370735682248966172617 := by
  unfold tailWord_7695267
  simp only [CollatzResearch.WordTrace]
  refine ⟨280669445412369380816164055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187112963608246253877442703 280669445412369380816164055)
  ·
    refine ⟨421004168118554071224246083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280669445412369380816164055 421004168118554071224246083)
    ·
      refine ⟨631506252177831106836369125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421004168118554071224246083 631506252177831106836369125)
      ·
        refine ⟨118407422283343332531819211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 631506252177831106836369125 118407422283343332531819211)
        ·
          refine ⟨177611133425014998797728817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118407422283343332531819211 177611133425014998797728817)
          ·
            refine ⟨133208350068761249098296613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177611133425014998797728817 133208350068761249098296613)
            ·
              refine ⟨24976565637892734205930615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133208350068761249098296613 24976565637892734205930615)
              ·
                refine ⟨37464848456839101308895923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24976565637892734205930615 37464848456839101308895923)
                ·
                  refine ⟨56197272685258651963343885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37464848456839101308895923 56197272685258651963343885)
                  ·
                    refine ⟨21073977256971994486253957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56197272685258651963343885 21073977256971994486253957)
                    ·
                      refine ⟨3951370735682248966172617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21073977256971994486253957 3951370735682248966172617)
                      ·
                        rfl

theorem cell23_7695267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_7695267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695267 prefixEnd_7695267 := by exact prefixLift 7695267
  have htrace : WordTrace (prefixWord ++ tailWord_7695267) baseStart_7695267 baseEnd_7695267 := by
    simpa [prefixWord, tailWord_7695267, baseEnd_7695267] using wordTrace_append hprefix tailTrace_7695267
  have hstable : (prefixWord ++ tailWord_7695267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695267).length < 2 ^ (prefixWord ++ tailWord_7695267).sum := by decide
  have hdescent : baseEnd_7695267 < baseStart_7695267 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695318 : List Nat := [5, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4]
def baseStart_7695318 : Nat := 118140960795 + 7695318 * 2 ^ 59
def prefixEnd_7695318 : Nat := 4983230072969 + 3 ^ 40 * 7695318 * 2
def baseEnd_7695318 : Nat := 3951396923195628266634883

theorem tailTrace_7695318 : CollatzResearch.WordTrace tailWord_7695318 prefixEnd_7695318 3951396923195628266634883 := by
  unfold tailWord_7695318
  simp only [CollatzResearch.WordTrace]
  refine ⟨17541956595949038532891913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187114203690123077684180405 17541956595949038532891913)
  ·
    refine ⟨13156467446961778899668935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17541956595949038532891913 13156467446961778899668935)
    ·
      refine ⟨19734701170442668349503403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13156467446961778899668935 19734701170442668349503403)
      ·
        refine ⟨29602051755664002524255105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19734701170442668349503403 29602051755664002524255105)
        ·
          refine ⟨22201538816748001893191329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29602051755664002524255105 22201538816748001893191329)
          ·
            refine ⟨16651154112561001419893497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22201538816748001893191329 16651154112561001419893497)
            ·
              refine ⟨12488365584420751064920123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16651154112561001419893497 12488365584420751064920123)
              ·
                refine ⟨18732548376631126597380185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488365584420751064920123 18732548376631126597380185)
                ·
                  refine ⟨14049411282473344948035139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18732548376631126597380185 14049411282473344948035139)
                  ·
                    refine ⟨21074116923710017422052709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14049411282473344948035139 21074116923710017422052709)
                    ·
                      refine ⟨3951396923195628266634883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21074116923710017422052709 3951396923195628266634883)
                      ·
                        rfl

theorem cell23_7695318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_7695318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695318 prefixEnd_7695318 := by exact prefixLift 7695318
  have htrace : WordTrace (prefixWord ++ tailWord_7695318) baseStart_7695318 baseEnd_7695318 := by
    simpa [prefixWord, tailWord_7695318, baseEnd_7695318] using wordTrace_append hprefix tailTrace_7695318
  have hstable : (prefixWord ++ tailWord_7695318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695318).length < 2 ^ (prefixWord ++ tailWord_7695318).sum := by decide
  have hdescent : baseEnd_7695318 < baseStart_7695318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695321 : List Nat := [1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_7695321 : Nat := 118140960795 + 7695321 * 2 ^ 59
def prefixEnd_7695321 : Nat := 4983230072969 + 3 ^ 40 * 7695321 * 2
def baseEnd_7695321 : Nat := 3951398463637591754897369

theorem tailTrace_7695321 : CollatzResearch.WordTrace tailWord_7695321 prefixEnd_7695321 3951398463637591754897369 := by
  unfold tailWord_7695321
  simp only [CollatzResearch.WordTrace]
  refine ⟨280671414954173748038629817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187114276636115832025753211 280671414954173748038629817)
  ·
    refine ⟨210503561215630311028972363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280671414954173748038629817 210503561215630311028972363)
    ·
      refine ⟨315755341823445466543458545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210503561215630311028972363 315755341823445466543458545)
      ·
        refine ⟨236816506367584099907593909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315755341823445466543458545 236816506367584099907593909)
        ·
          refine ⟨22201547471961009366336929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236816506367584099907593909 22201547471961009366336929)
          ·
            refine ⟨16651160603970757024752697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22201547471961009366336929 16651160603970757024752697)
            ·
              refine ⟨12488370452978067768564523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16651160603970757024752697 12488370452978067768564523)
              ·
                refine ⟨18732555679467101652846785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488370452978067768564523 18732555679467101652846785)
                ·
                  refine ⟨14049416759600326239635089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18732555679467101652846785 14049416759600326239635089)
                  ·
                    refine ⟨10537062569700244679726317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14049416759600326239635089 10537062569700244679726317)
                    ·
                      refine ⟨3951398463637591754897369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10537062569700244679726317 3951398463637591754897369)
                      ·
                        rfl

theorem cell23_7695321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_7695321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695321 prefixEnd_7695321 := by exact prefixLift 7695321
  have htrace : WordTrace (prefixWord ++ tailWord_7695321) baseStart_7695321 baseEnd_7695321 := by
    simpa [prefixWord, tailWord_7695321, baseEnd_7695321] using wordTrace_append hprefix tailTrace_7695321
  have hstable : (prefixWord ++ tailWord_7695321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695321).length < 2 ^ (prefixWord ++ tailWord_7695321).sum := by decide
  have hdescent : baseEnd_7695321 < baseStart_7695321 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695344 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 3, 5, 2]
def baseStart_7695344 : Nat := 118140960795 + 7695344 * 2 ^ 59
def prefixEnd_7695344 : Nat := 4983230072969 + 3 ^ 40 * 7695344 * 2
def baseEnd_7695344 : Nat := 3951410273692645164909763

theorem tailTrace_7695344 : CollatzResearch.WordTrace tailWord_7695344 prefixEnd_7695344 3951410273692645164909763 := by
  unfold tailWord_7695344
  simp only [CollatzResearch.WordTrace]
  refine ⟨140336126916545211483358543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187114835888726948644478057 140336126916545211483358543)
  ·
    refine ⟨210504190374817817225037815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140336126916545211483358543 210504190374817817225037815)
    ·
      refine ⟨315756285562226725837556723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210504190374817817225037815 315756285562226725837556723)
      ·
        refine ⟨473634428343340088756335085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315756285562226725837556723 473634428343340088756335085)
        ·
          refine ⟨177612910628752533283625657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473634428343340088756335085 177612910628752533283625657)
          ·
            refine ⟨133209682971564399962719243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177612910628752533283625657 133209682971564399962719243)
            ·
              refine ⟨199814524457346599944078865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133209682971564399962719243 199814524457346599944078865)
              ·
                refine ⟨149860893343009949958059149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199814524457346599944078865 149860893343009949958059149)
                ·
                  refine ⟨56197835003628731234272181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149860893343009949958059149 56197835003628731234272181)
                  ·
                    refine ⟨5268547031590193553213017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56197835003628731234272181 5268547031590193553213017)
                    ·
                      refine ⟨3951410273692645164909763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268547031590193553213017 3951410273692645164909763)
                      ·
                        rfl

theorem cell23_7695344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 3, 5, 2].length) (baseStart_7695344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695344 prefixEnd_7695344 := by exact prefixLift 7695344
  have htrace : WordTrace (prefixWord ++ tailWord_7695344) baseStart_7695344 baseEnd_7695344 := by
    simpa [prefixWord, tailWord_7695344, baseEnd_7695344] using wordTrace_append hprefix tailTrace_7695344
  have hstable : (prefixWord ++ tailWord_7695344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695344).length < 2 ^ (prefixWord ++ tailWord_7695344).sum := by decide
  have hdescent : baseEnd_7695344 < baseStart_7695344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695345 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 1, 4]
def baseStart_7695345 : Nat := 118140960795 + 7695345 * 2 ^ 59
def prefixEnd_7695345 : Nat := 4983230072969 + 3 ^ 40 * 7695345 * 2
def baseEnd_7695345 : Nat := 1317136929057766553665753

theorem tailTrace_7695345 : CollatzResearch.WordTrace tailWord_7695345 prefixEnd_7695345 1317136929057766553665753 := by
  unfold tailWord_7695345
  simp only [CollatzResearch.WordTrace]
  refine ⟨280672290306086800137503489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187114860204057866758335659 280672290306086800137503489)
  ·
    refine ⟨210504217729565100103127617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280672290306086800137503489 210504217729565100103127617)
    ·
      refine ⟨157878163297173825077345713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210504217729565100103127617 157878163297173825077345713)
      ·
        refine ⟨118408622472880368808009285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157878163297173825077345713 118408622472880368808009285)
        ·
          refine ⟨22201616713665069151501741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118408622472880368808009285 22201616713665069151501741)
          ·
            refine ⟨8325606267624400931813153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22201616713665069151501741 8325606267624400931813153)
            ·
              refine ⟨6244204700718300698859865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325606267624400931813153 6244204700718300698859865)
              ·
                refine ⟨4683153525538725524144899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6244204700718300698859865 4683153525538725524144899)
                ·
                  refine ⟨7024730288308088286217349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683153525538725524144899 7024730288308088286217349)
                  ·
                    refine ⟨1317136929057766553665753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024730288308088286217349 1317136929057766553665753)
                    ·
                      rfl

theorem cell23_7695345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_7695345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695345 prefixEnd_7695345 := by exact prefixLift 7695345
  have htrace : WordTrace (prefixWord ++ tailWord_7695345) baseStart_7695345 baseEnd_7695345 := by
    simpa [prefixWord, tailWord_7695345, baseEnd_7695345] using wordTrace_append hprefix tailTrace_7695345
  have hstable : (prefixWord ++ tailWord_7695345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695345).length < 2 ^ (prefixWord ++ tailWord_7695345).sum := by decide
  have hdescent : baseEnd_7695345 < baseStart_7695345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695384 : List Nat := [2, 1, 2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_7695384 : Nat := 118140960795 + 7695384 * 2 ^ 59
def prefixEnd_7695384 : Nat := 4983230072969 + 3 ^ 40 * 7695384 * 2
def baseEnd_7695384 : Nat := 1317143604306275002803193

theorem tailTrace_7695384 : CollatzResearch.WordTrace tailWord_7695384 prefixEnd_7695384 1317143604306275002803193 := by
  unfold tailWord_7695384
  simp only [CollatzResearch.WordTrace]
  refine ⟨140336856376472754899086603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187115808501963673198782137 140336856376472754899086603)
  ·
    refine ⟨210505284564709132348629905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140336856376472754899086603 210505284564709132348629905)
    ·
      refine ⟨157878963423531849261472429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210505284564709132348629905 157878963423531849261472429)
      ·
        refine ⟨59204611283824443473052161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157878963423531849261472429 59204611283824443473052161)
        ·
          refine ⟨44403458462868332604789121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59204611283824443473052161 44403458462868332604789121)
          ·
            refine ⟨33302593847151249453591841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44403458462868332604789121 33302593847151249453591841)
            ·
              refine ⟨24976945385363437090193881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33302593847151249453591841 24976945385363437090193881)
              ·
                refine ⟨18732709039022577817645411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24976945385363437090193881 18732709039022577817645411)
                ·
                  refine ⟨28099063558533866726468117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18732709039022577817645411 28099063558533866726468117)
                  ·
                    refine ⟨1317143604306275002803193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28099063558533866726468117 1317143604306275002803193)
                    ·
                      rfl

theorem cell23_7695384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_7695384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695384 prefixEnd_7695384 := by exact prefixLift 7695384
  have htrace : WordTrace (prefixWord ++ tailWord_7695384) baseStart_7695384 baseEnd_7695384 := by
    simpa [prefixWord, tailWord_7695384, baseEnd_7695384] using wordTrace_append hprefix tailTrace_7695384
  have hstable : (prefixWord ++ tailWord_7695384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695384).length < 2 ^ (prefixWord ++ tailWord_7695384).sum := by decide
  have hdescent : baseEnd_7695384 < baseStart_7695384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695387 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4]
def baseStart_7695387 : Nat := 118140960795 + 7695387 * 2 ^ 59
def prefixEnd_7695387 : Nat := 4983230072969 + 3 ^ 40 * 7695387 * 2
def baseEnd_7695387 : Nat := 3951432353360788496672065

theorem tailTrace_7695387 : CollatzResearch.WordTrace tailWord_7695387 prefixEnd_7695387 3951432353360788496672065 := by
  unfold tailWord_7695387
  simp only [CollatzResearch.WordTrace]
  refine ⟨280673822171934641310532415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187115881447956427540354943 280673822171934641310532415)
  ·
    refine ⟨421010733257901961965798623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280673822171934641310532415 421010733257901961965798623)
    ·
      refine ⟨631516099886852942948697935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421010733257901961965798623 631516099886852942948697935)
      ·
        refine ⟨947274149830279414423046903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631516099886852942948697935 947274149830279414423046903)
        ·
          refine ⟨1420911224745419121634570355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947274149830279414423046903 1420911224745419121634570355)
          ·
            refine ⟨2131366837118128682451855533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1420911224745419121634570355 2131366837118128682451855533)
            ·
              refine ⟨799262563919298255919445825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2131366837118128682451855533 799262563919298255919445825)
              ·
                refine ⟨599446922939473691939584369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799262563919298255919445825 599446922939473691939584369)
                ·
                  refine ⟨449585192204605268954688277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 599446922939473691939584369 449585192204605268954688277)
                  ·
                    refine ⟨21074305884590871982251013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 449585192204605268954688277 21074305884590871982251013)
                    ·
                      refine ⟨3951432353360788496672065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21074305884590871982251013 3951432353360788496672065)
                      ·
                        rfl

theorem cell23_7695387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_7695387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695387 prefixEnd_7695387 := by exact prefixLift 7695387
  have htrace : WordTrace (prefixWord ++ tailWord_7695387) baseStart_7695387 baseEnd_7695387 := by
    simpa [prefixWord, tailWord_7695387, baseEnd_7695387] using wordTrace_append hprefix tailTrace_7695387
  have hstable : (prefixWord ++ tailWord_7695387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695387).length < 2 ^ (prefixWord ++ tailWord_7695387).sum := by decide
  have hdescent : baseEnd_7695387 < baseStart_7695387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695391 : List Nat := [1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 4]
def baseStart_7695391 : Nat := 118140960795 + 7695391 * 2 ^ 59
def prefixEnd_7695391 : Nat := 4983230072969 + 3 ^ 40 * 7695391 * 2
def baseEnd_7695391 : Nat := 3951434407283406481022047

theorem tailTrace_7695391 : CollatzResearch.WordTrace tailWord_7695391 prefixEnd_7695391 3951434407283406481022047 := by
  unfold tailWord_7695391
  simp only [CollatzResearch.WordTrace]
  refine ⟨280673968063920149993678027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187115978709280099995785351 280673968063920149993678027)
  ·
    refine ⟨421010952095880224990517041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280673968063920149993678027 421010952095880224990517041)
    ·
      refine ⟨315758214071910168742887781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421010952095880224990517041 315758214071910168742887781)
      ·
        refine ⟨59204665138483156639291459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315758214071910168742887781 59204665138483156639291459)
        ·
          refine ⟨88806997707724734958937189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59204665138483156639291459 88806997707724734958937189)
          ·
            refine ⟨16651312070198387804800723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88806997707724734958937189 16651312070198387804800723)
            ·
              refine ⟨24976968105297581707201085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16651312070198387804800723 24976968105297581707201085)
              ·
                refine ⟨9366363039486593140200407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24976968105297581707201085 9366363039486593140200407)
                ·
                  refine ⟨14049544559229889710300611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9366363039486593140200407 14049544559229889710300611)
                  ·
                    refine ⟨21074316838844834565450917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14049544559229889710300611 21074316838844834565450917)
                    ·
                      refine ⟨3951434407283406481022047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21074316838844834565450917 3951434407283406481022047)
                      ·
                        rfl

theorem cell23_7695391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_7695391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695391 prefixEnd_7695391 := by exact prefixLift 7695391
  have htrace : WordTrace (prefixWord ++ tailWord_7695391) baseStart_7695391 baseEnd_7695391 := by
    simpa [prefixWord, tailWord_7695391, baseEnd_7695391] using wordTrace_append hprefix tailTrace_7695391
  have hstable : (prefixWord ++ tailWord_7695391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695391).length < 2 ^ (prefixWord ++ tailWord_7695391).sum := by decide
  have hdescent : baseEnd_7695391 < baseStart_7695391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695397 : List Nat := [1, 3, 1, 2, 2, 2, 12]
def baseStart_7695397 : Nat := 118140960795 + 7695397 * 2 ^ 59
def prefixEnd_7695397 : Nat := 4983230072969 + 3 ^ 40 * 7695397 * 2
def baseEnd_7695397 : Nat := 48783178866263376019099

theorem tailTrace_7695397 : CollatzResearch.WordTrace tailWord_7695397 prefixEnd_7695397 48783178866263376019099 := by
  unfold tailWord_7695397
  simp only [CollatzResearch.WordTrace]
  refine ⟨280674186901898413018396445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187116124601265608678930963 280674186901898413018396445)
  ·
    refine ⟨105252820088211904881898667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280674186901898413018396445 105252820088211904881898667)
    ·
      refine ⟨157879230132317857322848001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105252820088211904881898667 157879230132317857322848001)
      ·
        refine ⟨118409422599238392992136001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157879230132317857322848001 118409422599238392992136001)
        ·
          refine ⟨88807066949428794744102001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118409422599238392992136001 88807066949428794744102001)
          ·
            refine ⟨66605300212071596058076501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88807066949428794744102001 66605300212071596058076501)
            ·
              refine ⟨48783178866263376019099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 66605300212071596058076501 48783178866263376019099)
              ·
                rfl

theorem cell23_7695397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 12].length) (baseStart_7695397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695397 prefixEnd_7695397 := by exact prefixLift 7695397
  have htrace : WordTrace (prefixWord ++ tailWord_7695397) baseStart_7695397 baseEnd_7695397 := by
    simpa [prefixWord, tailWord_7695397, baseEnd_7695397] using wordTrace_append hprefix tailTrace_7695397
  have hstable : (prefixWord ++ tailWord_7695397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695397).length < 2 ^ (prefixWord ++ tailWord_7695397).sum := by decide
  have hdescent : baseEnd_7695397 < baseStart_7695397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695408 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 3, 2, 2]
def baseStart_7695408 : Nat := 118140960795 + 7695408 * 2 ^ 59
def prefixEnd_7695408 : Nat := 4983230072969 + 3 ^ 40 * 7695408 * 2
def baseEnd_7695408 : Nat := 3951443136454532914509469

theorem tailTrace_7695408 : CollatzResearch.WordTrace tailWord_7695408 prefixEnd_7695408 3951443136454532914509469 := by
  unfold tailWord_7695408
  simp only [CollatzResearch.WordTrace]
  refine ⟨140337294052429280948523439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187116392069905707931364585 140337294052429280948523439)
  ·
    refine ⟨210505941078643921422785159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140337294052429280948523439 210505941078643921422785159)
    ·
      refine ⟨315758911617965882134177739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210505941078643921422785159 315758911617965882134177739)
      ·
        refine ⟨473638367426948823201266609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315758911617965882134177739 473638367426948823201266609)
        ·
          refine ⟨355228775570211617400949957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473638367426948823201266609 355228775570211617400949957)
          ·
            refine ⟨66605395419414678262678117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355228775570211617400949957 66605395419414678262678117)
            ·
              refine ⟨12488511641140252174252147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66605395419414678262678117 12488511641140252174252147)
              ·
                refine ⟨18732767461710378261378221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488511641140252174252147 18732767461710378261378221)
                ·
                  refine ⟨7024787798141391848016833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18732767461710378261378221 7024787798141391848016833)
                  ·
                    refine ⟨5268590848606043886012625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024787798141391848016833 5268590848606043886012625)
                    ·
                      refine ⟨3951443136454532914509469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268590848606043886012625 3951443136454532914509469)
                      ·
                        rfl

theorem cell23_7695408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 3, 2, 2].length) (baseStart_7695408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695408 prefixEnd_7695408 := by exact prefixLift 7695408
  have htrace : WordTrace (prefixWord ++ tailWord_7695408) baseStart_7695408 baseEnd_7695408 := by
    simpa [prefixWord, tailWord_7695408, baseEnd_7695408] using wordTrace_append hprefix tailTrace_7695408
  have hstable : (prefixWord ++ tailWord_7695408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695408).length < 2 ^ (prefixWord ++ tailWord_7695408).sum := by decide
  have hdescent : baseEnd_7695408 < baseStart_7695408 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695421 : List Nat := [1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 4]
def baseStart_7695421 : Nat := 118140960795 + 7695421 * 2 ^ 59
def prefixEnd_7695421 : Nat := 4983230072969 + 3 ^ 40 * 7695421 * 2
def baseEnd_7695421 : Nat := 3951449811703041363646909

theorem tailTrace_7695421 : CollatzResearch.WordTrace tailWord_7695421 prefixEnd_7695421 3951449811703041363646909 := by
  unfold tailWord_7695421
  simp only [CollatzResearch.WordTrace]
  refine ⟨280675062253811465117270117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187116708169207643411513411 280675062253811465117270117)
  ·
    refine ⟨52626574172589649709488147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280675062253811465117270117 52626574172589649709488147)
    ·
      refine ⟨78939861258884474564232221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52626574172589649709488147 78939861258884474564232221)
      ·
        refine ⟨29602447972081677961587083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78939861258884474564232221 29602447972081677961587083)
        ·
          refine ⟨44403671958122516942380625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29602447972081677961587083 44403671958122516942380625)
          ·
            refine ⟨33302753968591887706785469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44403671958122516942380625 33302753968591887706785469)
            ·
              refine ⟨12488532738221957890044551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33302753968591887706785469 12488532738221957890044551)
              ·
                refine ⟨18732799107332936835066827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488532738221957890044551 18732799107332936835066827)
                ·
                  refine ⟨28099198660999405252600241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18732799107332936835066827 28099198660999405252600241)
                  ·
                    refine ⟨21074398995749553939450181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28099198660999405252600241 21074398995749553939450181)
                    ·
                      refine ⟨3951449811703041363646909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21074398995749553939450181 3951449811703041363646909)
                      ·
                        rfl

theorem cell23_7695421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_7695421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695421 prefixEnd_7695421 := by exact prefixLift 7695421
  have htrace : WordTrace (prefixWord ++ tailWord_7695421) baseStart_7695421 baseEnd_7695421 := by
    simpa [prefixWord, tailWord_7695421, baseEnd_7695421] using wordTrace_append hprefix tailTrace_7695421
  have hstable : (prefixWord ++ tailWord_7695421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695421).length < 2 ^ (prefixWord ++ tailWord_7695421).sum := by decide
  have hdescent : baseEnd_7695421 < baseStart_7695421 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695431 : List Nat := [1, 1, 4, 1, 3, 4, 2, 7]
def baseStart_7695431 : Nat := 118140960795 + 7695431 * 2 ^ 59
def prefixEnd_7695431 : Nat := 4983230072969 + 3 ^ 40 * 7695431 * 2
def baseEnd_7695431 : Nat := 146350183204058752760069

theorem tailTrace_7695431 : CollatzResearch.WordTrace tailWord_7695431 prefixEnd_7695431 146350183204058752760069 := by
  unfold tailWord_7695431
  simp only [CollatzResearch.WordTrace]
  refine ⟨280675426983775236825134147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187116951322516824550089431 280675426983775236825134147)
  ·
    refine ⟨421013140475662855237701221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280675426983775236825134147 421013140475662855237701221)
    ·
      refine ⟨78939963839186785357068979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421013140475662855237701221 78939963839186785357068979)
      ·
        refine ⟨118409945758780178035603469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78939963839186785357068979 118409945758780178035603469)
        ·
          refine ⟨44403729659542566763351301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118409945758780178035603469 44403729659542566763351301)
          ·
            refine ⟨8325699311164231268128369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44403729659542566763351301 8325699311164231268128369)
            ·
              refine ⟨6244274483373173451096277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8325699311164231268128369 6244274483373173451096277)
              ·
                refine ⟨146350183204058752760069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6244274483373173451096277 146350183204058752760069)
                ·
                  rfl

theorem cell23_7695431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 2, 7].length) (baseStart_7695431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695431 prefixEnd_7695431 := by exact prefixLift 7695431
  have htrace : WordTrace (prefixWord ++ tailWord_7695431) baseStart_7695431 baseEnd_7695431 := by
    simpa [prefixWord, tailWord_7695431, baseEnd_7695431] using wordTrace_append hprefix tailTrace_7695431
  have hstable : (prefixWord ++ tailWord_7695431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695431).length < 2 ^ (prefixWord ++ tailWord_7695431).sum := by decide
  have hdescent : baseEnd_7695431 < baseStart_7695431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695441 : List Nat := [1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_7695441 : Nat := 118140960795 + 7695441 * 2 ^ 59
def prefixEnd_7695441 : Nat := 4983230072969 + 3 ^ 40 * 7695441 * 2
def baseEnd_7695441 : Nat := 3951460081316131285396817

theorem tailTrace_7695441 : CollatzResearch.WordTrace tailWord_7695441 prefixEnd_7695441 3951460081316131285396817 := by
  unfold tailWord_7695441
  simp only [CollatzResearch.WordTrace]
  refine ⟨280675791713739008532998177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187117194475826005688665451 280675791713739008532998177)
  ·
    refine ⟨210506843785304256399748633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280675791713739008532998177 210506843785304256399748633)
    ·
      refine ⟨157880132838978192299811475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210506843785304256399748633 157880132838978192299811475)
      ·
        refine ⟨236820199258467288449717213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157880132838978192299811475 236820199258467288449717213)
        ·
          refine ⟨88807574721925233168643955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236820199258467288449717213 88807574721925233168643955)
          ·
            refine ⟨133211362082887849752965933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88807574721925233168643955 133211362082887849752965933)
            ·
              refine ⟨49954260781082943657362225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133211362082887849752965933 49954260781082943657362225)
              ·
                refine ⟨37465695585812207743021669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49954260781082943657362225 37465695585812207743021669)
                ·
                  refine ⟨7024817922339788951816563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37465695585812207743021669 7024817922339788951816563)
                  ·
                    refine ⟨10537226883509683427724845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7024817922339788951816563 10537226883509683427724845)
                    ·
                      refine ⟨3951460081316131285396817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10537226883509683427724845 3951460081316131285396817)
                      ·
                        rfl

theorem cell23_7695441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_7695441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695441 prefixEnd_7695441 := by exact prefixLift 7695441
  have htrace : WordTrace (prefixWord ++ tailWord_7695441) baseStart_7695441 baseEnd_7695441 := by
    simpa [prefixWord, tailWord_7695441, baseEnd_7695441] using wordTrace_append hprefix tailTrace_7695441
  have hstable : (prefixWord ++ tailWord_7695441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695441).length < 2 ^ (prefixWord ++ tailWord_7695441).sum := by decide
  have hdescent : baseEnd_7695441 < baseStart_7695441 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695442 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 1, 2, 2]
def baseStart_7695442 : Nat := 118140960795 + 7695442 * 2 ^ 59
def prefixEnd_7695442 : Nat := 4983230072969 + 3 ^ 40 * 7695442 * 2
def baseEnd_7695442 : Nat := 3951460594796785781484313

theorem tailTrace_7695442 : CollatzResearch.WordTrace tailWord_7695442 prefixEnd_7695442 3951460594796785781484313 := by
  unfold tailWord_7695442
  simp only [CollatzResearch.WordTrace]
  refine ⟨70168957046683846425946145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187117218791156923802523053 70168957046683846425946145)
  ·
    refine ⟨52626717785012884819459609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70168957046683846425946145 52626717785012884819459609)
    ·
      refine ⟨39470038338759663614594707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52626717785012884819459609 39470038338759663614594707)
      ·
        refine ⟨59205057508139495421892061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39470038338759663614594707 59205057508139495421892061)
        ·
          refine ⟨22201896565552310783209523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59205057508139495421892061 22201896565552310783209523)
          ·
            refine ⟨33302844848328466174814285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22201896565552310783209523 33302844848328466174814285)
            ·
              refine ⟨12488566818123174815555357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33302844848328466174814285 12488566818123174815555357)
              ·
                refine ⟨4683212556796190555833259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12488566818123174815555357 4683212556796190555833259)
                ·
                  refine ⟨7024818835194285833749889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683212556796190555833259 7024818835194285833749889)
                  ·
                    refine ⟨5268614126395714375312417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7024818835194285833749889 5268614126395714375312417)
                    ·
                      refine ⟨3951460594796785781484313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268614126395714375312417 3951460594796785781484313)
                      ·
                        rfl

theorem cell23_7695442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_7695442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695442 prefixEnd_7695442 := by exact prefixLift 7695442
  have htrace : WordTrace (prefixWord ++ tailWord_7695442) baseStart_7695442 baseEnd_7695442 := by
    simpa [prefixWord, tailWord_7695442, baseEnd_7695442] using wordTrace_append hprefix tailTrace_7695442
  have hstable : (prefixWord ++ tailWord_7695442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695442).length < 2 ^ (prefixWord ++ tailWord_7695442).sum := by decide
  have hdescent : baseEnd_7695442 < baseStart_7695442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695474 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 1, 8]
def baseStart_7695474 : Nat := 118140960795 + 7695474 * 2 ^ 59
def prefixEnd_7695474 : Nat := 4983230072969 + 3 ^ 40 * 7695474 * 2
def baseEnd_7695474 : Nat := 1317159008725909885428055

theorem tailTrace_7695474 : CollatzResearch.WordTrace tailWord_7695474 prefixEnd_7695474 1317159008725909885428055 := by
  unfold tailWord_7695474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70169248830654863792237369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187117996881746303445966317 70169248830654863792237369)
  ·
    refine ⟨52626936622991147844178027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70169248830654863792237369 52626936622991147844178027)
    ·
      refine ⟨78940404934486721766267041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52626936622991147844178027 78940404934486721766267041)
      ·
        refine ⟨59205303700865041324700281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78940404934486721766267041 59205303700865041324700281)
        ·
          refine ⟨44403977775648780993525211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59205303700865041324700281 44403977775648780993525211)
          ·
            refine ⟨66605966663473171490287817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44403977775648780993525211 66605966663473171490287817)
            ·
              refine ⟨49954474997604878617715863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66605966663473171490287817 49954474997604878617715863)
              ·
                refine ⟨74931712496407317926573795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49954474997604878617715863 74931712496407317926573795)
                ·
                  refine ⟨112397568744610976889860693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74931712496407317926573795 112397568744610976889860693)
                  ·
                    refine ⟨1317159008725909885428055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112397568744610976889860693 1317159008725909885428055)
                    ·
                      rfl

theorem cell23_7695474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 1, 8].length) (baseStart_7695474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695474 prefixEnd_7695474 := by exact prefixLift 7695474
  have htrace : WordTrace (prefixWord ++ tailWord_7695474) baseStart_7695474 baseEnd_7695474 := by
    simpa [prefixWord, tailWord_7695474, baseEnd_7695474] using wordTrace_append hprefix tailTrace_7695474
  have hstable : (prefixWord ++ tailWord_7695474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695474).length < 2 ^ (prefixWord ++ tailWord_7695474).sum := by decide
  have hdescent : baseEnd_7695474 < baseStart_7695474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695484 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_7695484 : Nat := 118140960795 + 7695484 * 2 ^ 59
def prefixEnd_7695484 : Nat := 4983230072969 + 3 ^ 40 * 7695484 * 2
def baseEnd_7695484 : Nat := 3951482160984274617159119

theorem tailTrace_7695484 : CollatzResearch.WordTrace tailWord_7695484 prefixEnd_7695484 3951482160984274617159119 := by
  unfold tailWord_7695484
  simp only [CollatzResearch.WordTrace]
  refine ⟨140338680026291613438406753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187118240035055484584542337 140338680026291613438406753)
  ·
    refine ⟨105254010019718710078805065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140338680026291613438406753 105254010019718710078805065)
    ·
      refine ⟨78940507514789032559103799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105254010019718710078805065 78940507514789032559103799)
      ·
        refine ⟨118410761272183548838655699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78940507514789032559103799 118410761272183548838655699)
        ·
          refine ⟨177616141908275323257983549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118410761272183548838655699 177616141908275323257983549)
          ·
            refine ⟨66606053215603246221743831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177616141908275323257983549 66606053215603246221743831)
            ·
              refine ⟨99909079823404869332615747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66606053215603246221743831 99909079823404869332615747)
              ·
                refine ⟨149863619735107303998923621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99909079823404869332615747 149863619735107303998923621)
                ·
                  refine ⟨28099428700332619499798179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149863619735107303998923621 28099428700332619499798179)
                  ·
                    refine ⟨42149143050498929249697269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28099428700332619499798179 42149143050498929249697269)
                    ·
                      refine ⟨3951482160984274617159119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42149143050498929249697269 3951482160984274617159119)
                      ·
                        rfl

theorem cell23_7695484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_7695484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695484 prefixEnd_7695484 := by exact prefixLift 7695484
  have htrace : WordTrace (prefixWord ++ tailWord_7695484) baseStart_7695484 baseEnd_7695484 := by
    simpa [prefixWord, tailWord_7695484, baseEnd_7695484] using wordTrace_append hprefix tailTrace_7695484
  have hstable : (prefixWord ++ tailWord_7695484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695484).length < 2 ^ (prefixWord ++ tailWord_7695484).sum := by decide
  have hdescent : baseEnd_7695484 < baseStart_7695484 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695498 : List Nat := [3, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_7695498 : Nat := 118140960795 + 7695498 * 2 ^ 59
def prefixEnd_7695498 : Nat := 4983230072969 + 3 ^ 40 * 7695498 * 2
def baseEnd_7695498 : Nat := 3951489349713437562384055

theorem tailTrace_7695498 : CollatzResearch.WordTrace tailWord_7695498 prefixEnd_7695498 3951489349713437562384055 := by
  unfold tailWord_7695498
  simp only [CollatzResearch.WordTrace]
  refine ⟨70169467668633126816955787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187118580449688338178548765 70169467668633126816955787)
  ·
    refine ⟨105254201502949690225433681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70169467668633126816955787 105254201502949690225433681)
    ·
      refine ⟨78940651127212267669075261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105254201502949690225433681 78940651127212267669075261)
      ·
        refine ⟨29602744172704600375903223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78940651127212267669075261 29602744172704600375903223)
        ·
          refine ⟨44404116259056900563854835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29602744172704600375903223 44404116259056900563854835)
          ·
            refine ⟨66606174388585350845782253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44404116259056900563854835 66606174388585350845782253)
            ·
              refine ⟨24977315395719506567168345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66606174388585350845782253 24977315395719506567168345)
              ·
                refine ⟨18732986546789629925376259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24977315395719506567168345 18732986546789629925376259)
                ·
                  refine ⟨28099479820184444888064389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18732986546789629925376259 28099479820184444888064389)
                  ·
                    refine ⟨5268652466284583416512073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28099479820184444888064389 5268652466284583416512073)
                    ·
                      refine ⟨3951489349713437562384055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268652466284583416512073 3951489349713437562384055)
                      ·
                        rfl

theorem cell23_7695498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_7695498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695498 prefixEnd_7695498 := by exact prefixLift 7695498
  have htrace : WordTrace (prefixWord ++ tailWord_7695498) baseStart_7695498 baseEnd_7695498 := by
    simpa [prefixWord, tailWord_7695498, baseEnd_7695498] using wordTrace_append hprefix tailTrace_7695498
  have hstable : (prefixWord ++ tailWord_7695498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695498).length < 2 ^ (prefixWord ++ tailWord_7695498).sum := by decide
  have hdescent : baseEnd_7695498 < baseStart_7695498 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695502 : List Nat := [4, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_7695502 : Nat := 118140960795 + 7695502 * 2 ^ 59
def prefixEnd_7695502 : Nat := 4983230072969 + 3 ^ 40 * 7695502 * 2
def baseEnd_7695502 : Nat := 3951491403636055546734037

theorem tailTrace_7695502 : CollatzResearch.WordTrace tailWord_7695502 prefixEnd_7695502 3951491403636055546734037 := by
  unfold tailWord_7695502
  simp only [CollatzResearch.WordTrace]
  refine ⟨35084752070814751993871095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187118677711012010633979173 35084752070814751993871095)
  ·
    refine ⟨52627128106222127990806643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35084752070814751993871095 52627128106222127990806643)
    ·
      refine ⟨78940692159333191986209965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52627128106222127990806643 78940692159333191986209965)
      ·
        refine ⟨29602759559749946994828737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78940692159333191986209965 29602759559749946994828737)
        ·
          refine ⟨22202069669812460246121553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29602759559749946994828737 22202069669812460246121553)
          ·
            refine ⟨16651552252359345184591165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22202069669812460246121553 16651552252359345184591165)
            ·
              refine ⟨6244332094634754444221687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16651552252359345184591165 6244332094634754444221687)
              ·
                refine ⟨9366498141952131666332531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244332094634754444221687 9366498141952131666332531)
                ·
                  refine ⟨14049747212928197499498797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9366498141952131666332531 14049747212928197499498797)
                  ·
                    refine ⟨5268655204848074062312049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14049747212928197499498797 5268655204848074062312049)
                    ·
                      refine ⟨3951491403636055546734037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268655204848074062312049 3951491403636055546734037)
                      ·
                        rfl

theorem cell23_7695502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_7695502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695502 prefixEnd_7695502 := by exact prefixLift 7695502
  have htrace : WordTrace (prefixWord ++ tailWord_7695502) baseStart_7695502 baseEnd_7695502 := by
    simpa [prefixWord, tailWord_7695502, baseEnd_7695502] using wordTrace_append hprefix tailTrace_7695502
  have hstable : (prefixWord ++ tailWord_7695502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695502).length < 2 ^ (prefixWord ++ tailWord_7695502).sum := by decide
  have hdescent : baseEnd_7695502 < baseStart_7695502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695518 : List Nat := [4, 3, 1, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_7695518 : Nat := 118140960795 + 7695518 * 2 ^ 59
def prefixEnd_7695518 : Nat := 4983230072969 + 3 ^ 40 * 7695518 * 2
def baseEnd_7695518 : Nat := 3951499619326527484133963

theorem tailTrace_7695518 : CollatzResearch.WordTrace tailWord_7695518 prefixEnd_7695518 3951499619326527484133963 := by
  unfold tailWord_7695518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35084825016807506335443901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187119066756306700455700805 35084825016807506335443901)
  ·
    refine ⟨13156809381302814875791463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35084825016807506335443901 13156809381302814875791463)
    ·
      refine ⟨19735214071954222313687195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13156809381302814875791463 19735214071954222313687195)
      ·
        refine ⟨29602821107931333470530793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19735214071954222313687195 29602821107931333470530793)
        ·
          refine ⟨22202115830948500102898095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29602821107931333470530793 22202115830948500102898095)
          ·
            refine ⟨33303173746422750154347143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22202115830948500102898095 33303173746422750154347143)
            ·
              refine ⟨49954760619634125231520715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33303173746422750154347143 49954760619634125231520715)
              ·
                refine ⟨74932140929451187847281073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49954760619634125231520715 74932140929451187847281073)
                ·
                  refine ⟨56199105697088390885460805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74932140929451187847281073 56199105697088390885460805)
                  ·
                    refine ⟨10537332318204073291023901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56199105697088390885460805 10537332318204073291023901)
                    ·
                      refine ⟨3951499619326527484133963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10537332318204073291023901 3951499619326527484133963)
                      ·
                        rfl

theorem cell23_7695518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_7695518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695518 prefixEnd_7695518 := by exact prefixLift 7695518
  have htrace : WordTrace (prefixWord ++ tailWord_7695518) baseStart_7695518 baseEnd_7695518 := by
    simpa [prefixWord, tailWord_7695518, baseEnd_7695518] using wordTrace_append hprefix tailTrace_7695518
  have hstable : (prefixWord ++ tailWord_7695518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695518).length < 2 ^ (prefixWord ++ tailWord_7695518).sum := by decide
  have hdescent : baseEnd_7695518 < baseStart_7695518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695544 : List Nat := [2, 1, 2, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_7695544 : Nat := 118140960795 + 7695544 * 2 ^ 59
def prefixEnd_7695544 : Nat := 4983230072969 + 3 ^ 40 * 7695544 * 2
def baseEnd_7695544 : Nat := 3951512969823544382408843

theorem tailTrace_7695544 : CollatzResearch.WordTrace tailWord_7695544 prefixEnd_7695544 3951512969823544382408843 := by
  unfold tailWord_7695544
  simp only [CollatzResearch.WordTrace]
  refine ⟨140339774216182928561998843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187119698954910571415998457 140339774216182928561998843)
  ·
    refine ⟨210509661324274392842998265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140339774216182928561998843 210509661324274392842998265)
    ·
      refine ⟨157882245993205794632248699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210509661324274392842998265 157882245993205794632248699)
      ·
        refine ⟨236823368989808691948373049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157882245993205794632248699 236823368989808691948373049)
        ·
          refine ⟨177617526742356518961279787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236823368989808691948373049 177617526742356518961279787)
          ·
            refine ⟨266426290113534778441919681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177617526742356518961279787 266426290113534778441919681)
            ·
              refine ⟨199819717585151083831439761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266426290113534778441919681 199819717585151083831439761)
              ·
                refine ⟨149864788188863312873579821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199819717585151083831439761 149864788188863312873579821)
                ·
                  refine ⟨56199295570823742327592433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149864788188863312873579821 56199295570823742327592433)
                  ·
                    refine ⟨42149471678117806745694325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56199295570823742327592433 42149471678117806745694325)
                    ·
                      refine ⟨3951512969823544382408843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42149471678117806745694325 3951512969823544382408843)
                      ·
                        rfl

theorem cell23_7695544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_7695544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695544 prefixEnd_7695544 := by exact prefixLift 7695544
  have htrace : WordTrace (prefixWord ++ tailWord_7695544) baseStart_7695544 baseEnd_7695544 := by
    simpa [prefixWord, tailWord_7695544, baseEnd_7695544] using wordTrace_append hprefix tailTrace_7695544
  have hstable : (prefixWord ++ tailWord_7695544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695544).length < 2 ^ (prefixWord ++ tailWord_7695544).sum := by decide
  have hdescent : baseEnd_7695544 < baseStart_7695544 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695551 : List Nat := [1, 1, 2, 2, 2, 2, 5, 1, 2, 5]
def baseStart_7695551 : Nat := 118140960795 + 7695551 * 2 ^ 59
def prefixEnd_7695551 : Nat := 4983230072969 + 3 ^ 40 * 7695551 * 2
def baseEnd_7695551 : Nat := 1317172188062708618340437

theorem tailTrace_7695551 : CollatzResearch.WordTrace tailWord_7695551 prefixEnd_7695551 1317172188062708618340437 := by
  unfold tailWord_7695551
  simp only [CollatzResearch.WordTrace]
  refine ⟨280679803743340497319502507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187119869162226998213001671 280679803743340497319502507)
  ·
    refine ⟨421019705615010745979253761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280679803743340497319502507 421019705615010745979253761)
    ·
      refine ⟨315764779211258059484440321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421019705615010745979253761 315764779211258059484440321)
      ·
        refine ⟨236823584408443544613330241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315764779211258059484440321 236823584408443544613330241)
        ·
          refine ⟨177617688306332658459997681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236823584408443544613330241 177617688306332658459997681)
          ·
            refine ⟨133213266229749493844998261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177617688306332658459997681 133213266229749493844998261)
            ·
              refine ⟨12488743709039015047968587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133213266229749493844998261 12488743709039015047968587)
              ·
                refine ⟨18733115563558522571952881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12488743709039015047968587 18733115563558522571952881)
                ·
                  refine ⟨14049836672668891928964661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18733115563558522571952881 14049836672668891928964661)
                  ·
                    refine ⟨1317172188062708618340437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14049836672668891928964661 1317172188062708618340437)
                    ·
                      rfl

theorem cell23_7695551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 1, 2, 5].length) (baseStart_7695551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695551 prefixEnd_7695551 := by exact prefixLift 7695551
  have htrace : WordTrace (prefixWord ++ tailWord_7695551) baseStart_7695551 baseEnd_7695551 := by
    simpa [prefixWord, tailWord_7695551, baseEnd_7695551] using wordTrace_append hprefix tailTrace_7695551
  have hstable : (prefixWord ++ tailWord_7695551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695551).length < 2 ^ (prefixWord ++ tailWord_7695551).sum := by decide
  have hdescent : baseEnd_7695551 < baseStart_7695551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695571 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 3, 6, 2]
def baseStart_7695571 : Nat := 118140960795 + 7695571 * 2 ^ 59
def prefixEnd_7695571 : Nat := 4983230072969 + 3 ^ 40 * 7695571 * 2
def baseEnd_7695571 : Nat := 3951526833801215776771219

theorem tailTrace_7695571 : CollatzResearch.WordTrace tailWord_7695571 prefixEnd_7695571 3951526833801215776771219 := by
  unfold tailWord_7695571
  simp only [CollatzResearch.WordTrace]
  refine ⟨280680533203268040735230567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187120355468845360490153711 280680533203268040735230567)
  ·
    refine ⟨421020799804902061102845851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280680533203268040735230567 421020799804902061102845851)
    ·
      refine ⟨631531199707353091654268777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421020799804902061102845851 631531199707353091654268777)
      ·
        refine ⟨473648399780514818740701583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631531199707353091654268777 473648399780514818740701583)
        ·
          refine ⟨710472599670772228111052375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473648399780514818740701583 710472599670772228111052375)
          ·
            refine ⟨1065708899506158342166578563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710472599670772228111052375 1065708899506158342166578563)
            ·
              refine ⟨1598563349259237513249867845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1065708899506158342166578563 1598563349259237513249867845)
              ·
                refine ⟨299730627986107033734350221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1598563349259237513249867845 299730627986107033734350221)
                ·
                  refine ⟨112398985494790137650381333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299730627986107033734350221 112398985494790137650381333)
                  ·
                    refine ⟨5268702445068287702361625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112398985494790137650381333 5268702445068287702361625)
                    ·
                      refine ⟨3951526833801215776771219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268702445068287702361625 3951526833801215776771219)
                      ·
                        rfl

theorem cell23_7695571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 6, 2].length) (baseStart_7695571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695571 prefixEnd_7695571 := by exact prefixLift 7695571
  have htrace : WordTrace (prefixWord ++ tailWord_7695571) baseStart_7695571 baseEnd_7695571 := by
    simpa [prefixWord, tailWord_7695571, baseEnd_7695571] using wordTrace_append hprefix tailTrace_7695571
  have hstable : (prefixWord ++ tailWord_7695571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695571).length < 2 ^ (prefixWord ++ tailWord_7695571).sum := by decide
  have hdescent : baseEnd_7695571 < baseStart_7695571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695588 : List Nat := [2, 3, 1, 1, 1, 2, 4, 1, 2, 4, 2]
def baseStart_7695588 : Nat := 118140960795 + 7695588 * 2 ^ 59
def prefixEnd_7695588 : Nat := 4983230072969 + 3 ^ 40 * 7695588 * 2
def baseEnd_7695588 : Nat := 3951535562972342210258641

theorem tailTrace_7695588 : CollatzResearch.WordTrace tailWord_7695588 prefixEnd_7695588 3951535562972342210258641 := by
  unfold tailWord_7695588
  simp only [CollatzResearch.WordTrace]
  refine ⟨140340576622103226319299709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187120768829470968425732945 140340576622103226319299709)
  ·
    refine ⟨52627716233288709869737391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140340576622103226319299709 52627716233288709869737391)
    ·
      refine ⟨78941574349933064804606087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52627716233288709869737391 78941574349933064804606087)
      ·
        refine ⟨118412361524899597206909131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78941574349933064804606087 118412361524899597206909131)
        ·
          refine ⟨177618542287349395810363697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118412361524899597206909131 177618542287349395810363697)
          ·
            refine ⟨133213906715512046857772773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177618542287349395810363697 133213906715512046857772773)
            ·
              refine ⟨24977607509158508785832395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133213906715512046857772773 24977607509158508785832395)
              ·
                refine ⟨37466411263737763178748593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24977607509158508785832395 37466411263737763178748593)
                ·
                  refine ⟨28099808447803322384061445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37466411263737763178748593 28099808447803322384061445)
                  ·
                    refine ⟨5268714083963122947011521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28099808447803322384061445 5268714083963122947011521)
                    ·
                      refine ⟨3951535562972342210258641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268714083963122947011521 3951535562972342210258641)
                      ·
                        rfl

theorem cell23_7695588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_7695588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695588 prefixEnd_7695588 := by exact prefixLift 7695588
  have htrace : WordTrace (prefixWord ++ tailWord_7695588) baseStart_7695588 baseEnd_7695588 := by
    simpa [prefixWord, tailWord_7695588, baseEnd_7695588] using wordTrace_append hprefix tailTrace_7695588
  have hstable : (prefixWord ++ tailWord_7695588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695588).length < 2 ^ (prefixWord ++ tailWord_7695588).sum := by decide
  have hdescent : baseEnd_7695588 < baseStart_7695588 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695598 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7695598 : Nat := 118140960795 + 7695598 * 2 ^ 59
def prefixEnd_7695598 : Nat := 4983230072969 + 3 ^ 40 * 7695598 * 2
def baseEnd_7695598 : Nat := 1317180232592962390377865

theorem tailTrace_7695598 : CollatzResearch.WordTrace tailWord_7695598 prefixEnd_7695598 1317180232592962390377865 := by
  unfold tailWord_7695598
  simp only [CollatzResearch.WordTrace]
  refine ⟨35085189746771278043307931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187121011982780149564308965 35085189746771278043307931)
  ·
    refine ⟨52627784620156917064961897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35085189746771278043307931 52627784620156917064961897)
    ·
      refine ⟨39470838465117687798721423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52627784620156917064961897 39470838465117687798721423)
      ·
        refine ⟨59206257697676531698082135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39470838465117687798721423 59206257697676531698082135)
        ·
          refine ⟨88809386546514797547123203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59206257697676531698082135 88809386546514797547123203)
          ·
            refine ⟨133214079819772196320684805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88809386546514797547123203 133214079819772196320684805)
            ·
              refine ⟨24977639966207286810128401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133214079819772196320684805 24977639966207286810128401)
              ·
                refine ⟨18733229974655465107596301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24977639966207286810128401 18733229974655465107596301)
                ·
                  refine ⟨7024961240495799415348613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18733229974655465107596301 7024961240495799415348613)
                  ·
                    refine ⟨1317180232592962390377865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024961240495799415348613 1317180232592962390377865)
                    ·
                      rfl

theorem cell23_7695598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7695598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695598 prefixEnd_7695598 := by exact prefixLift 7695598
  have htrace : WordTrace (prefixWord ++ tailWord_7695598) baseStart_7695598 baseEnd_7695598 := by
    simpa [prefixWord, tailWord_7695598, baseEnd_7695598] using wordTrace_append hprefix tailTrace_7695598
  have hstable : (prefixWord ++ tailWord_7695598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695598).length < 2 ^ (prefixWord ++ tailWord_7695598).sum := by decide
  have hdescent : baseEnd_7695598 < baseStart_7695598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695615 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 1, 4]
def baseStart_7695615 : Nat := 118140960795 + 7695615 * 2 ^ 59
def prefixEnd_7695615 : Nat := 4983230072969 + 3 ^ 40 * 7695615 * 2
def baseEnd_7695615 : Nat := 1317183142316671201540339

theorem tailTrace_7695615 : CollatzResearch.WordTrace tailWord_7695615 prefixEnd_7695615 1317183142316671201540339 := by
  unfold tailWord_7695615
  simp only [CollatzResearch.WordTrace]
  refine ⟨280682138015108636249832299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187121425343405757499888199 280682138015108636249832299)
  ·
    refine ⟨421023207022662954374748449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280682138015108636249832299 421023207022662954374748449)
    ·
      refine ⟨315767405266997215781061337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421023207022662954374748449 315767405266997215781061337)
      ·
        refine ⟨236825553950247911835796003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315767405266997215781061337 236825553950247911835796003)
        ·
          refine ⟨355238330925371867753694005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236825553950247911835796003 355238330925371867753694005)
          ·
            refine ⟨33303593524253612601908813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 355238330925371867753694005 33303593524253612601908813)
            ·
              refine ⟨12488847571595104725715805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33303593524253612601908813 12488847571595104725715805)
              ·
                refine ⟨4683317839348164272143427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12488847571595104725715805 4683317839348164272143427)
                ·
                  refine ⟨7024976759022246408215141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683317839348164272143427 7024976759022246408215141)
                  ·
                    refine ⟨1317183142316671201540339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7024976759022246408215141 1317183142316671201540339)
                    ·
                      rfl

theorem cell23_7695615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 1, 4].length) (baseStart_7695615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695615 prefixEnd_7695615 := by exact prefixLift 7695615
  have htrace : WordTrace (prefixWord ++ tailWord_7695615) baseStart_7695615 baseEnd_7695615 := by
    simpa [prefixWord, tailWord_7695615, baseEnd_7695615] using wordTrace_append hprefix tailTrace_7695615
  have hstable : (prefixWord ++ tailWord_7695615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695615).length < 2 ^ (prefixWord ++ tailWord_7695615).sum := by decide
  have hdescent : baseEnd_7695615 < baseStart_7695615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695645 : List Nat := [1, 4, 2, 3, 1, 1, 4, 1, 6]
def baseStart_7695645 : Nat := 118140960795 + 7695645 * 2 ^ 59
def prefixEnd_7695645 : Nat := 4983230072969 + 3 ^ 40 * 7695645 * 2
def baseEnd_7695645 : Nat := 439062759041072054138431

theorem tailTrace_7695645 : CollatzResearch.WordTrace tailWord_7695645 prefixEnd_7695645 439062759041072054138431 := by
  unfold tailWord_7695645
  simp only [CollatzResearch.WordTrace]
  refine ⟨280683232204999951373424389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187122154803333300915616259 280683232204999951373424389)
  ·
    refine ⟨52628106038437490882517073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280683232204999951373424389 52628106038437490882517073)
    ·
      refine ⟨39471079528828118161887805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52628106038437490882517073 39471079528828118161887805)
      ·
        refine ⟨14801654823310544310707927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39471079528828118161887805 14801654823310544310707927)
        ·
          refine ⟨22202482234965816466061891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801654823310544310707927 22202482234965816466061891)
          ·
            refine ⟨33303723352448724699092837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22202482234965816466061891 33303723352448724699092837)
            ·
              refine ⟨6244448128584135881079907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33303723352448724699092837 6244448128584135881079907)
              ·
                refine ⟨9366672192876203821619861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244448128584135881079907 9366672192876203821619861)
                ·
                  refine ⟨439062759041072054138431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9366672192876203821619861 439062759041072054138431)
                  ·
                    rfl

theorem cell23_7695645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 6].length) (baseStart_7695645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695645 prefixEnd_7695645 := by exact prefixLift 7695645
  have htrace : WordTrace (prefixWord ++ tailWord_7695645) baseStart_7695645 baseEnd_7695645 := by
    simpa [prefixWord, tailWord_7695645, baseEnd_7695645] using wordTrace_append hprefix tailTrace_7695645
  have hstable : (prefixWord ++ tailWord_7695645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695645).length < 2 ^ (prefixWord ++ tailWord_7695645).sum := by decide
  have hdescent : baseEnd_7695645 < baseStart_7695645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695665 : List Nat := [1, 2, 2, 3, 3, 1, 1, 3, 2, 3, 2]
def baseStart_7695665 : Nat := 118140960795 + 7695665 * 2 ^ 59
def prefixEnd_7695665 : Nat := 4983230072969 + 3 ^ 40 * 7695665 * 2
def baseEnd_7695665 : Nat := 3951575100982738408995787

theorem tailTrace_7695665 : CollatzResearch.WordTrace tailWord_7695665 prefixEnd_7695665 3951575100982738408995787 := by
  unfold tailWord_7695665
  simp only [CollatzResearch.WordTrace]
  refine ⟨280683961664927494789152449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187122641109951663192768299 280683961664927494789152449)
  ·
    refine ⟨210512971248695621091864337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280683961664927494789152449 210512971248695621091864337)
    ·
      refine ⟨157884728436521715818898253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210512971248695621091864337 157884728436521715818898253)
      ·
        refine ⟨59206773163695643432086845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157884728436521715818898253 59206773163695643432086845)
        ·
          refine ⟨22202539936385866287032567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59206773163695643432086845 22202539936385866287032567)
          ·
            refine ⟨33303809904578799430548851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22202539936385866287032567 33303809904578799430548851)
            ·
              refine ⟨49955714856868199145823277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33303809904578799430548851 49955714856868199145823277)
              ·
                refine ⟨18733393071325574679683729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49955714856868199145823277 18733393071325574679683729)
                ·
                  refine ⟨14050044803494181009762797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18733393071325574679683729 14050044803494181009762797)
                  ·
                    refine ⟨5268766801310317878661049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14050044803494181009762797 5268766801310317878661049)
                    ·
                      refine ⟨3951575100982738408995787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268766801310317878661049 3951575100982738408995787)
                      ·
                        rfl

theorem cell23_7695665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_7695665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695665 prefixEnd_7695665 := by exact prefixLift 7695665
  have htrace : WordTrace (prefixWord ++ tailWord_7695665) baseStart_7695665 baseEnd_7695665 := by
    simpa [prefixWord, tailWord_7695665, baseEnd_7695665] using wordTrace_append hprefix tailTrace_7695665
  have hstable : (prefixWord ++ tailWord_7695665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695665).length < 2 ^ (prefixWord ++ tailWord_7695665).sum := by decide
  have hdescent : baseEnd_7695665 < baseStart_7695665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695712 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 3, 2, 2]
def baseStart_7695712 : Nat := 118140960795 + 7695712 * 2 ^ 59
def prefixEnd_7695712 : Nat := 4983230072969 + 3 ^ 40 * 7695712 * 2
def baseEnd_7695712 : Nat := 3951599234573499725108071

theorem tailTrace_7695712 : CollatzResearch.WordTrace tailWord_7695712 prefixEnd_7695712 3951599234573499725108071 := by
  unfold tailWord_7695712
  simp only [CollatzResearch.WordTrace]
  refine ⟨140342837947878610908056695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187123783930504814544075593 140342837947878610908056695)
  ·
    refine ⟨210514256921817916362085043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140342837947878610908056695 210514256921817916362085043)
    ·
      refine ⟨315771385382726874543127565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210514256921817916362085043 315771385382726874543127565)
      ·
        refine ⟨118414269518522577953672837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315771385382726874543127565 118414269518522577953672837)
        ·
          refine ⟨22202675534722983366313657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118414269518522577953672837 22202675534722983366313657)
          ·
            refine ⟨16652006651042237524735243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22202675534722983366313657 16652006651042237524735243)
            ·
              refine ⟨24978009976563356287102865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16652006651042237524735243 24978009976563356287102865)
              ·
                refine ⟨18733507482422517215327149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24978009976563356287102865 18733507482422517215327149)
                ·
                  refine ⟨7025065305908443955747681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18733507482422517215327149 7025065305908443955747681)
                  ·
                    refine ⟨5268798979431332966810761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025065305908443955747681 5268798979431332966810761)
                    ·
                      refine ⟨3951599234573499725108071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268798979431332966810761 3951599234573499725108071)
                      ·
                        rfl

theorem cell23_7695712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 3, 2, 2].length) (baseStart_7695712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695712 prefixEnd_7695712 := by exact prefixLift 7695712
  have htrace : WordTrace (prefixWord ++ tailWord_7695712) baseStart_7695712 baseEnd_7695712 := by
    simpa [prefixWord, tailWord_7695712, baseEnd_7695712] using wordTrace_append hprefix tailTrace_7695712
  have hstable : (prefixWord ++ tailWord_7695712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695712).length < 2 ^ (prefixWord ++ tailWord_7695712).sum := by decide
  have hdescent : baseEnd_7695712 < baseStart_7695712 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695726 : List Nat := [4, 1, 2, 4, 2, 1, 2, 1, 1, 5]
def baseStart_7695726 : Nat := 118140960795 + 7695726 * 2 ^ 59
def prefixEnd_7695726 : Nat := 4983230072969 + 3 ^ 40 * 7695726 * 2
def baseEnd_7695726 : Nat := 1317202141100887556777669

theorem tailTrace_7695726 : CollatzResearch.WordTrace tailWord_7695726 prefixEnd_7695726 1317202141100887556777669 := by
  unfold tailWord_7695726
  simp only [CollatzResearch.WordTrace]
  refine ⟨35085773314713312775890379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187124124345137668138082021 35085773314713312775890379)
  ·
    refine ⟨52628659972069969163835569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35085773314713312775890379 52628659972069969163835569)
    ·
      refine ⟨39471494979052476872876677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52628659972069969163835569 39471494979052476872876677)
      ·
        refine ⟨7400905308572339413664377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39471494979052476872876677 7400905308572339413664377)
        ·
          refine ⟨5550678981429254560248283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7400905308572339413664377 5550678981429254560248283)
          ·
            refine ⟨8326018472143881840372425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5550678981429254560248283 8326018472143881840372425)
            ·
              refine ⟨6244513854107911380279319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8326018472143881840372425 6244513854107911380279319)
              ·
                refine ⟨9366770781161867070418979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244513854107911380279319 9366770781161867070418979)
                ·
                  refine ⟨14050156171742800605628469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9366770781161867070418979 14050156171742800605628469)
                  ·
                    refine ⟨1317202141100887556777669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14050156171742800605628469 1317202141100887556777669)
                    ·
                      rfl

theorem cell23_7695726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_7695726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695726 prefixEnd_7695726 := by exact prefixLift 7695726
  have htrace : WordTrace (prefixWord ++ tailWord_7695726) baseStart_7695726 baseEnd_7695726 := by
    simpa [prefixWord, tailWord_7695726, baseEnd_7695726] using wordTrace_append hprefix tailTrace_7695726
  have hstable : (prefixWord ++ tailWord_7695726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695726).length < 2 ^ (prefixWord ++ tailWord_7695726).sum := by decide
  have hdescent : baseEnd_7695726 < baseStart_7695726 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695728 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3]
def baseStart_7695728 : Nat := 118140960795 + 7695728 * 2 ^ 59
def prefixEnd_7695728 : Nat := 4983230072969 + 3 ^ 40 * 7695728 * 2
def baseEnd_7695728 : Nat := 3951607450263971662507997

theorem tailTrace_7695728 : CollatzResearch.WordTrace tailWord_7695728 prefixEnd_7695728 3951607450263971662507997 := by
  unfold tailWord_7695728
  simp only [CollatzResearch.WordTrace]
  refine ⟨140343129731849628274347919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187124172975799504365797225 140343129731849628274347919)
  ·
    refine ⟨210514694597774442411521879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140343129731849628274347919 210514694597774442411521879)
    ·
      refine ⟨315772041896661663617282819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210514694597774442411521879 315772041896661663617282819)
      ·
        refine ⟨473658062844992495425924229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315772041896661663617282819 473658062844992495425924229)
        ·
          refine ⟨88810886783436092892360793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473658062844992495425924229 88810886783436092892360793)
          ·
            refine ⟨66608165087577069669270595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88810886783436092892360793 66608165087577069669270595)
            ·
              refine ⟨99912247631365604503905893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66608165087577069669270595 99912247631365604503905893)
              ·
                refine ⟨18733546430881050844482355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99912247631365604503905893 18733546430881050844482355)
                ·
                  refine ⟨28100319646321576266723533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18733546430881050844482355 28100319646321576266723533)
                  ·
                    refine ⟨10537619867370591100021325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28100319646321576266723533 10537619867370591100021325)
                    ·
                      refine ⟨3951607450263971662507997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10537619867370591100021325 3951607450263971662507997)
                      ·
                        rfl

theorem cell23_7695728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3].length) (baseStart_7695728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695728 prefixEnd_7695728 := by exact prefixLift 7695728
  have htrace : WordTrace (prefixWord ++ tailWord_7695728) baseStart_7695728 baseEnd_7695728 := by
    simpa [prefixWord, tailWord_7695728, baseEnd_7695728] using wordTrace_append hprefix tailTrace_7695728
  have hstable : (prefixWord ++ tailWord_7695728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695728).length < 2 ^ (prefixWord ++ tailWord_7695728).sum := by decide
  have hdescent : baseEnd_7695728 < baseStart_7695728 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695746 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_7695746 : Nat := 118140960795 + 7695746 * 2 ^ 59
def prefixEnd_7695746 : Nat := 4983230072969 + 3 ^ 40 * 7695746 * 2
def baseEnd_7695746 : Nat := 3951616692915752592082915

theorem tailTrace_7695746 : CollatzResearch.WordTrace tailWord_7695746 prefixEnd_7695746 3951616692915752592082915 := by
  unfold tailWord_7695746
  simp only [CollatzResearch.WordTrace]
  refine ⟨70171728994408511405712773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187124610651756030415234061 70171728994408511405712773)
  ·
    refine ⟨13157199186451595888571145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70171728994408511405712773 13157199186451595888571145)
    ·
      refine ⟨9867899389838696916428359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13157199186451595888571145 9867899389838696916428359)
      ·
        refine ⟨14801849084758045374642539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9867899389838696916428359 14801849084758045374642539)
        ·
          refine ⟨22202773627137068061963809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801849084758045374642539 22202773627137068061963809)
          ·
            refine ⟨16652080220352801046472857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22202773627137068061963809 16652080220352801046472857)
            ·
              refine ⟨12489060165264600784854643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16652080220352801046472857 12489060165264600784854643)
              ·
                refine ⟨18733590247896901177281965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489060165264600784854643 18733590247896901177281965)
                ·
                  refine ⟨7025096342961337941480737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18733590247896901177281965 7025096342961337941480737)
                  ·
                    refine ⟨5268822257221003456110553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025096342961337941480737 5268822257221003456110553)
                    ·
                      refine ⟨3951616692915752592082915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268822257221003456110553 3951616692915752592082915)
                      ·
                        rfl

theorem cell23_7695746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_7695746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695746 prefixEnd_7695746 := by exact prefixLift 7695746
  have htrace : WordTrace (prefixWord ++ tailWord_7695746) baseStart_7695746 baseEnd_7695746 := by
    simpa [prefixWord, tailWord_7695746, baseEnd_7695746] using wordTrace_append hprefix tailTrace_7695746
  have hstable : (prefixWord ++ tailWord_7695746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695746).length < 2 ^ (prefixWord ++ tailWord_7695746).sum := by decide
  have hdescent : baseEnd_7695746 < baseStart_7695746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695789 : List Nat := [1, 5, 2, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_7695789 : Nat := 118140960795 + 7695789 * 2 ^ 59
def prefixEnd_7695789 : Nat := 4983230072969 + 3 ^ 40 * 7695789 * 2
def baseEnd_7695789 : Nat := 3951638772583895923845217

theorem tailTrace_7695789 : CollatzResearch.WordTrace tailWord_7695789 prefixEnd_7695789 3951638772583895923845217 := by
  unfold tailWord_7695789
  simp only [CollatzResearch.WordTrace]
  refine ⟨280688484316478263966666421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187125656210985509311110947 280688484316478263966666421)
  ·
    refine ⟨26314545404669837246874977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280688484316478263966666421 26314545404669837246874977)
    ·
      refine ⟨19735909053502377935156233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26314545404669837246874977 19735909053502377935156233)
      ·
        refine ⟨14801931790126783451367175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19735909053502377935156233 14801931790126783451367175)
        ·
          refine ⟨22202897685190175177050763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14801931790126783451367175 22202897685190175177050763)
          ·
            refine ⟨33304346527785262765576145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22202897685190175177050763 33304346527785262765576145)
            ·
              refine ⟨24978259895838947074182109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33304346527785262765576145 24978259895838947074182109)
              ·
                refine ⟨9366847460939605152818291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24978259895838947074182109 9366847460939605152818291)
                ·
                  refine ⟨14050271191409407729227437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9366847460939605152818291 14050271191409407729227437)
                  ·
                    refine ⟨5268851696778527898460289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14050271191409407729227437 5268851696778527898460289)
                    ·
                      refine ⟨3951638772583895923845217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268851696778527898460289 3951638772583895923845217)
                      ·
                        rfl

theorem cell23_7695789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_7695789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695789 prefixEnd_7695789 := by exact prefixLift 7695789
  have htrace : WordTrace (prefixWord ++ tailWord_7695789) baseStart_7695789 baseEnd_7695789 := by
    simpa [prefixWord, tailWord_7695789, baseEnd_7695789] using wordTrace_append hprefix tailTrace_7695789
  have hstable : (prefixWord ++ tailWord_7695789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695789).length < 2 ^ (prefixWord ++ tailWord_7695789).sum := by decide
  have hdescent : baseEnd_7695789 < baseStart_7695789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695791 : List Nat := [1, 1, 2, 1, 2, 2, 1, 4, 9]
def baseStart_7695791 : Nat := 118140960795 + 7695791 * 2 ^ 59
def prefixEnd_7695791 : Nat := 4983230072969 + 3 ^ 40 * 7695791 * 2
def baseEnd_7695791 : Nat := 439071088838356101780023

theorem tailTrace_7695791 : CollatzResearch.WordTrace tailWord_7695791 prefixEnd_7695791 439071088838356101780023 := by
  unfold tailWord_7695791
  simp only [CollatzResearch.WordTrace]
  refine ⟨280688557262471018308239227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187125704841647345538826151 280688557262471018308239227)
  ·
    refine ⟨421032835893706527462358841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280688557262471018308239227 421032835893706527462358841)
    ·
      refine ⟨315774626920279895596769131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421032835893706527462358841 315774626920279895596769131)
      ·
        refine ⟨473661940380419843395153697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315774626920279895596769131 473661940380419843395153697)
        ·
          refine ⟨355246455285314882546365273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473661940380419843395153697 355246455285314882546365273)
          ·
            refine ⟨266434841463986161909773955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355246455285314882546365273 266434841463986161909773955)
            ·
              refine ⟨399652262195979242864660933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266434841463986161909773955 399652262195979242864660933)
              ·
                refine ⟨74934799161746108037123925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 399652262195979242864660933 74934799161746108037123925)
                ·
                  refine ⟨439071088838356101780023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74934799161746108037123925 439071088838356101780023)
                  ·
                    rfl

theorem cell23_7695791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 9].length) (baseStart_7695791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695791 prefixEnd_7695791 := by exact prefixLift 7695791
  have htrace : WordTrace (prefixWord ++ tailWord_7695791) baseStart_7695791 baseEnd_7695791 := by
    simpa [prefixWord, tailWord_7695791, baseEnd_7695791] using wordTrace_append hprefix tailTrace_7695791
  have hstable : (prefixWord ++ tailWord_7695791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695791).length < 2 ^ (prefixWord ++ tailWord_7695791).sum := by decide
  have hdescent : baseEnd_7695791 < baseStart_7695791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695808 : List Nat := [2, 1, 1, 2, 3, 1, 5, 1, 7]
def baseStart_7695808 : Nat := 118140960795 + 7695808 * 2 ^ 59
def prefixEnd_7695808 : Nat := 4983230072969 + 3 ^ 40 * 7695808 * 2
def baseEnd_7695808 : Nat := 439072058746259038834181

theorem tailTrace_7695808 : CollatzResearch.WordTrace tailWord_7695808 prefixEnd_7695808 439072058746259038834181 := by
  unfold tailWord_7695808
  simp only [CollatzResearch.WordTrace]
  refine ⟨140344588651704715105804039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187126118202272953474405385 140344588651704715105804039)
  ·
    refine ⟨210516882977557072658706059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140344588651704715105804039 210516882977557072658706059)
    ·
      refine ⟨315775324466335608988059089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210516882977557072658706059 315775324466335608988059089)
      ·
        refine ⟨236831493349751706741044317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315775324466335608988059089 236831493349751706741044317)
        ·
          refine ⟨88811810006156890027891619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236831493349751706741044317 88811810006156890027891619)
          ·
            refine ⟨133217715009235335041837429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88811810006156890027891619 133217715009235335041837429)
            ·
              refine ⟨12489160782115812660172259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133217715009235335041837429 12489160782115812660172259)
              ·
                refine ⟨18733741173173718990258389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489160782115812660172259 18733741173173718990258389)
                ·
                  refine ⟨439072058746259038834181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18733741173173718990258389 439072058746259038834181)
                  ·
                    rfl

theorem cell23_7695808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 5, 1, 7].length) (baseStart_7695808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695808 prefixEnd_7695808 := by exact prefixLift 7695808
  have htrace : WordTrace (prefixWord ++ tailWord_7695808) baseStart_7695808 baseEnd_7695808 := by
    simpa [prefixWord, tailWord_7695808, baseEnd_7695808] using wordTrace_append hprefix tailTrace_7695808
  have hstable : (prefixWord ++ tailWord_7695808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695808).length < 2 ^ (prefixWord ++ tailWord_7695808).sum := by decide
  have hdescent : baseEnd_7695808 < baseStart_7695808 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695819 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 2, 2, 2]
def baseStart_7695819 : Nat := 118140960795 + 7695819 * 2 ^ 59
def prefixEnd_7695819 : Nat := 4983230072969 + 3 ^ 40 * 7695819 * 2
def baseEnd_7695819 : Nat := 3951654177003530806470079

theorem tailTrace_7695819 : CollatzResearch.WordTrace tailWord_7695819 prefixEnd_7695819 3951654177003530806470079 := by
  unfold tailWord_7695819
  simp only [CollatzResearch.WordTrace]
  refine ⟨280689578506369579090258511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187126385670913052726839007 280689578506369579090258511)
  ·
    refine ⟨421034367759554368635387767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280689578506369579090258511 421034367759554368635387767)
    ·
      refine ⟨631551551639331552953081651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421034367759554368635387767 631551551639331552953081651)
      ·
        refine ⟨947327327458997329429622477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631551551639331552953081651 947327327458997329429622477)
        ·
          refine ⟨355247747797123998536108429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947327327458997329429622477 355247747797123998536108429)
          ·
            refine ⟨133217905423921499451040661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355247747797123998536108429 133217905423921499451040661)
            ·
              refine ⟨6244589316746320286767531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 133217905423921499451040661 6244589316746320286767531)
              ·
                refine ⟨9366883975119480430151297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244589316746320286767531 9366883975119480430151297)
                ·
                  refine ⟨7025162981339610322613473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9366883975119480430151297 7025162981339610322613473)
                  ·
                    refine ⟨5268872236004707741960105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025162981339610322613473 5268872236004707741960105)
                    ·
                      refine ⟨3951654177003530806470079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268872236004707741960105 3951654177003530806470079)
                      ·
                        rfl

theorem cell23_7695819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 2, 2, 2].length) (baseStart_7695819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695819 prefixEnd_7695819 := by exact prefixLift 7695819
  have htrace : WordTrace (prefixWord ++ tailWord_7695819) baseStart_7695819 baseEnd_7695819 := by
    simpa [prefixWord, tailWord_7695819, baseEnd_7695819] using wordTrace_append hprefix tailTrace_7695819
  have hstable : (prefixWord ++ tailWord_7695819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695819).length < 2 ^ (prefixWord ++ tailWord_7695819).sum := by decide
  have hdescent : baseEnd_7695819 < baseStart_7695819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695848 : List Nat := [2, 1, 4, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7695848 : Nat := 118140960795 + 7695848 * 2 ^ 59
def prefixEnd_7695848 : Nat := 4983230072969 + 3 ^ 40 * 7695848 * 2
def baseEnd_7695848 : Nat := 3951669067942511193007445

theorem tailTrace_7695848 : CollatzResearch.WordTrace tailWord_7695848 prefixEnd_7695848 3951669067942511193007445 := by
  unfold tailWord_7695848
  simp only [CollatzResearch.WordTrace]
  refine ⟨140345318111632258521532099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187127090815509678028709465 140345318111632258521532099)
  ·
    refine ⟨210517977167448387782298149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140345318111632258521532099 210517977167448387782298149)
    ·
      refine ⟨39472120718896572709180903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210517977167448387782298149 39472120718896572709180903)
      ·
        refine ⟨59208181078344859063771355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39472120718896572709180903 59208181078344859063771355)
        ·
          refine ⟨88812271617517288595657033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59208181078344859063771355 88812271617517288595657033)
          ·
            refine ⟨66609203713137966446742775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88812271617517288595657033 66609203713137966446742775)
            ·
              refine ⟨99913805569706949670114163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66609203713137966446742775 99913805569706949670114163)
              ·
                refine ⟨149870708354560424505171245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99913805569706949670114163 149870708354560424505171245)
                ·
                  refine ⟨56201515632960159189439217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149870708354560424505171245 56201515632960159189439217)
                  ·
                    refine ⟨42151136724720119392079413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56201515632960159189439217 42151136724720119392079413)
                    ·
                      refine ⟨3951669067942511193007445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42151136724720119392079413 3951669067942511193007445)
                      ·
                        rfl

theorem cell23_7695848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7695848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695848 prefixEnd_7695848 := by exact prefixLift 7695848
  have htrace : WordTrace (prefixWord ++ tailWord_7695848) baseStart_7695848 baseEnd_7695848 := by
    simpa [prefixWord, tailWord_7695848, baseEnd_7695848] using wordTrace_append hprefix tailTrace_7695848
  have hstable : (prefixWord ++ tailWord_7695848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695848).length < 2 ^ (prefixWord ++ tailWord_7695848).sum := by decide
  have hdescent : baseEnd_7695848 < baseStart_7695848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695862 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_7695862 : Nat := 118140960795 + 7695862 * 2 ^ 59
def prefixEnd_7695862 : Nat := 4983230072969 + 3 ^ 40 * 7695862 * 2
def baseEnd_7695862 : Nat := 3951676256671674138232381

theorem tailTrace_7695862 : CollatzResearch.WordTrace tailWord_7695862 prefixEnd_7695862 3951676256671674138232381 := by
  unfold tailWord_7695862
  simp only [CollatzResearch.WordTrace]
  refine ⟨17543196677825862339629615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187127431230142531622715893 17543196677825862339629615)
  ·
    refine ⟨26314795016738793509444423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17543196677825862339629615 26314795016738793509444423)
    ·
      refine ⟨39472192525108190264166635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26314795016738793509444423 39472192525108190264166635)
      ·
        refine ⟨59208288787662285396249953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39472192525108190264166635 59208288787662285396249953)
        ·
          refine ⟨44406216590746714047187465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59208288787662285396249953 44406216590746714047187465)
          ·
            refine ⟨33304662443060035535390599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44406216590746714047187465 33304662443060035535390599)
            ·
              refine ⟨49956993664590053303085899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33304662443060035535390599 49956993664590053303085899)
              ·
                refine ⟨74935490496885079954628849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49956993664590053303085899 74935490496885079954628849)
                ·
                  refine ⟨56201617872663809965971637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74935490496885079954628849 56201617872663809965971637)
                  ·
                    refine ⟨5268901675562232184309841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56201617872663809965971637 5268901675562232184309841)
                    ·
                      refine ⟨3951676256671674138232381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268901675562232184309841 3951676256671674138232381)
                      ·
                        rfl

theorem cell23_7695862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_7695862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695862 prefixEnd_7695862 := by exact prefixLift 7695862
  have htrace : WordTrace (prefixWord ++ tailWord_7695862) baseStart_7695862 baseEnd_7695862 := by
    simpa [prefixWord, tailWord_7695862, baseEnd_7695862] using wordTrace_append hprefix tailTrace_7695862
  have hstable : (prefixWord ++ tailWord_7695862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695862).length < 2 ^ (prefixWord ++ tailWord_7695862).sum := by decide
  have hdescent : baseEnd_7695862 < baseStart_7695862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695898 : List Nat := [3, 1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_7695898 : Nat := 118140960795 + 7695898 * 2 ^ 59
def prefixEnd_7695898 : Nat := 4983230072969 + 3 ^ 40 * 7695898 * 2
def baseEnd_7695898 : Nat := 439077193552803999709135

theorem tailTrace_7695898 : CollatzResearch.WordTrace tailWord_7695898 prefixEnd_7695898 439077193552803999709135 := by
  unfold tailWord_7695898
  simp only [CollatzResearch.WordTrace]
  refine ⟨70173114968270843895596087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187128306582055583721589565 70173114968270843895596087)
  ·
    refine ⟨105259672452406265843394131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70173114968270843895596087 105259672452406265843394131)
    ·
      refine ⟨157889508678609398765091197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105259672452406265843394131 157889508678609398765091197)
      ·
        refine ⟨59208565754478524536909199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157889508678609398765091197 59208565754478524536909199)
        ·
          refine ⟨88812848631717786805363799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59208565754478524536909199 88812848631717786805363799)
          ·
            refine ⟨133219272947576680208045699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88812848631717786805363799 133219272947576680208045699)
            ·
              refine ⟨199828909421365020312068549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133219272947576680208045699 199828909421365020312068549)
              ·
                refine ⟨37467920516505941308512853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199828909421365020312068549 37467920516505941308512853)
                ·
                  refine ⟨439077193552803999709135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37467920516505941308512853 439077193552803999709135)
                  ·
                    rfl

theorem cell23_7695898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_7695898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695898 prefixEnd_7695898 := by exact prefixLift 7695898
  have htrace : WordTrace (prefixWord ++ tailWord_7695898) baseStart_7695898 baseEnd_7695898 := by
    simpa [prefixWord, tailWord_7695898, baseEnd_7695898] using wordTrace_append hprefix tailTrace_7695898
  have hstable : (prefixWord ++ tailWord_7695898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695898).length < 2 ^ (prefixWord ++ tailWord_7695898).sum := by decide
  have hdescent : baseEnd_7695898 < baseStart_7695898 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695952 : List Nat := [2, 1, 1, 1, 1, 3, 4, 3, 2, 3, 2]
def baseStart_7695952 : Nat := 118140960795 + 7695952 * 2 ^ 59
def prefixEnd_7695952 : Nat := 4983230072969 + 3 ^ 40 * 7695952 * 2
def baseEnd_7695952 : Nat := 3951722469930578786106967

theorem tailTrace_7695952 : CollatzResearch.WordTrace tailWord_7695952 prefixEnd_7695952 3951722469930578786106967 := by
  unfold tailWord_7695952
  simp only [CollatzResearch.WordTrace]
  refine ⟨140347214707443871402425055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187129619609925161869900073 140347214707443871402425055)
  ·
    refine ⟨210520822061165807103637583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140347214707443871402425055 210520822061165807103637583)
    ·
      refine ⟨315781233091748710655456375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210520822061165807103637583 315781233091748710655456375)
      ·
        refine ⟨473671849637623065983184563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315781233091748710655456375 473671849637623065983184563)
        ·
          refine ⟨710507774456434598974776845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473671849637623065983184563 710507774456434598974776845)
          ·
            refine ⟨266440415421162974615541317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 710507774456434598974776845 266440415421162974615541317)
            ·
              refine ⟨49957577891468057740413997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266440415421162974615541317 49957577891468057740413997)
              ·
                refine ⟨18734091709300521652655249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49957577891468057740413997 18734091709300521652655249)
                ·
                  refine ⟨14050568781975391239491437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18734091709300521652655249 14050568781975391239491437)
                  ·
                    refine ⟨5268963293240771714809289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14050568781975391239491437 5268963293240771714809289)
                    ·
                      refine ⟨3951722469930578786106967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5268963293240771714809289 3951722469930578786106967)
                      ·
                        rfl

theorem cell23_7695952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 3, 2, 3, 2].length) (baseStart_7695952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695952 prefixEnd_7695952 := by exact prefixLift 7695952
  have htrace : WordTrace (prefixWord ++ tailWord_7695952) baseStart_7695952 baseEnd_7695952 := by
    simpa [prefixWord, tailWord_7695952, baseEnd_7695952] using wordTrace_append hprefix tailTrace_7695952
  have hstable : (prefixWord ++ tailWord_7695952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695952).length < 2 ^ (prefixWord ++ tailWord_7695952).sum := by decide
  have hdescent : baseEnd_7695952 < baseStart_7695952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695976 : List Nat := [2, 1, 4, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_7695976 : Nat := 118140960795 + 7695976 * 2 ^ 59
def prefixEnd_7695976 : Nat := 4983230072969 + 3 ^ 40 * 7695976 * 2
def baseEnd_7695976 : Nat := 3951734793466286692206857

theorem tailTrace_7695976 : CollatzResearch.WordTrace tailWord_7695976 prefixEnd_7695976 3951734793466286692206857 := by
  unfold tailWord_7695976
  simp only [CollatzResearch.WordTrace]
  refine ⟨140347652383400397451861891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187130203177867196602482521 140347652383400397451861891)
  ·
    refine ⟨210521478575100596177792837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140347652383400397451861891 210521478575100596177792837)
    ·
      refine ⟨39472777232831361783336157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210521478575100596177792837 39472777232831361783336157)
      ·
        refine ⟨14802291462311760668751059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39472777232831361783336157 14802291462311760668751059)
        ·
          refine ⟨22203437193467641003126589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14802291462311760668751059 22203437193467641003126589)
          ·
            refine ⟨8326288947550365376172471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22203437193467641003126589 8326288947550365376172471)
            ·
              refine ⟨12489433421325548064258707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326288947550365376172471 12489433421325548064258707)
              ·
                refine ⟨18734150131988322096388061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489433421325548064258707 18734150131988322096388061)
                ·
                  refine ⟨7025306299495620786145523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18734150131988322096388061 7025306299495620786145523)
                  ·
                    refine ⟨10537959449243431179218285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7025306299495620786145523 10537959449243431179218285)
                    ·
                      refine ⟨3951734793466286692206857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10537959449243431179218285 3951734793466286692206857)
                      ·
                        rfl

theorem cell23_7695976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_7695976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695976 prefixEnd_7695976 := by exact prefixLift 7695976
  have htrace : WordTrace (prefixWord ++ tailWord_7695976) baseStart_7695976 baseEnd_7695976 := by
    simpa [prefixWord, tailWord_7695976, baseEnd_7695976] using wordTrace_append hprefix tailTrace_7695976
  have hstable : (prefixWord ++ tailWord_7695976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695976).length < 2 ^ (prefixWord ++ tailWord_7695976).sum := by decide
  have hdescent : baseEnd_7695976 < baseStart_7695976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7695995 : List Nat := [1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4]
def baseStart_7695995 : Nat := 118140960795 + 7695995 * 2 ^ 59
def prefixEnd_7695995 : Nat := 4983230072969 + 3 ^ 40 * 7695995 * 2
def baseEnd_7695995 : Nat := 3951744549598722117869269

theorem tailTrace_7695995 : CollatzResearch.WordTrace tailWord_7695995 prefixEnd_7695995 3951744549598722117869269 := by
  unfold tailWord_7695995
  simp only [CollatzResearch.WordTrace]
  refine ⟨280695997753731961148665439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187130665169154640765776959 280695997753731961148665439)
  ·
    refine ⟨421043996630597941722998159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280695997753731961148665439 421043996630597941722998159)
    ·
      refine ⟨631565994945896912584497239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421043996630597941722998159 631565994945896912584497239)
      ·
        refine ⟨947348992418845368876745859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631565994945896912584497239 947348992418845368876745859)
        ·
          refine ⟨1421023488628268053315118789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947348992418845368876745859 1421023488628268053315118789)
          ·
            refine ⟨266441904117800259996584773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1421023488628268053315118789 266441904117800259996584773)
            ·
              refine ⟨49957857022087548749359645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266441904117800259996584773 49957857022087548749359645)
              ·
                refine ⟨18734196383282830781009867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49957857022087548749359645 18734196383282830781009867)
                ·
                  refine ⟨28101294574924246171514801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18734196383282830781009867 28101294574924246171514801)
                  ·
                    refine ⟨21075970931193184628636101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28101294574924246171514801 21075970931193184628636101)
                    ·
                      refine ⟨3951744549598722117869269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21075970931193184628636101 3951744549598722117869269)
                      ·
                        rfl

theorem cell23_7695995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 1, 2, 4].length) (baseStart_7695995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7695995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7695995 prefixEnd_7695995 := by exact prefixLift 7695995
  have htrace : WordTrace (prefixWord ++ tailWord_7695995) baseStart_7695995 baseEnd_7695995 := by
    simpa [prefixWord, tailWord_7695995, baseEnd_7695995] using wordTrace_append hprefix tailTrace_7695995
  have hstable : (prefixWord ++ tailWord_7695995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7695995).length < 2 ^ (prefixWord ++ tailWord_7695995).sum := by decide
  have hdescent : baseEnd_7695995 < baseStart_7695995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7695995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696033 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 1, 2, 2]
def baseStart_7696033 : Nat := 118140960795 + 7696033 * 2 ^ 59
def prefixEnd_7696033 : Nat := 4983230072969 + 3 ^ 40 * 7696033 * 2
def baseEnd_7696033 : Nat := 3951764061863592969194095

theorem tailTrace_7696033 : CollatzResearch.WordTrace tailWord_7696033 prefixEnd_7696033 3951764061863592969194095 := by
  unfold tailWord_7696033
  simp only [CollatzResearch.WordTrace]
  refine ⟨280697383727594293638548753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187131589151729529092365835 280697383727594293638548753)
  ·
    refine ⟨210523037795695720228911565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280697383727594293638548753 210523037795695720228911565)
    ·
      refine ⟨78946139173385895085841837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210523037795695720228911565 78946139173385895085841837)
      ·
        refine ⟨29604802190019710657190689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78946139173385895085841837 29604802190019710657190689)
        ·
          refine ⟨22203601642514782992893017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29604802190019710657190689 22203601642514782992893017)
          ·
            refine ⟨16652701231886087244669763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22203601642514782992893017 16652701231886087244669763)
            ·
              refine ⟨24979051847829130867004645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16652701231886087244669763 24979051847829130867004645)
              ·
                refine ⟨4683572221467962037563371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24979051847829130867004645 4683572221467962037563371)
                ·
                  refine ⟨7025358332201943056345057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4683572221467962037563371 7025358332201943056345057)
                  ·
                    refine ⟨5269018749151457292258793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025358332201943056345057 5269018749151457292258793)
                    ·
                      refine ⟨3951764061863592969194095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269018749151457292258793 3951764061863592969194095)
                      ·
                        rfl

theorem cell23_7696033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_7696033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696033 prefixEnd_7696033 := by exact prefixLift 7696033
  have htrace : WordTrace (prefixWord ++ tailWord_7696033) baseStart_7696033 baseEnd_7696033 := by
    simpa [prefixWord, tailWord_7696033, baseEnd_7696033] using wordTrace_append hprefix tailTrace_7696033
  have hstable : (prefixWord ++ tailWord_7696033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696033).length < 2 ^ (prefixWord ++ tailWord_7696033).sum := by decide
  have hdescent : baseEnd_7696033 < baseStart_7696033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696046 : List Nat := [4, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_7696046 : Nat := 118140960795 + 7696046 * 2 ^ 59
def prefixEnd_7696046 : Nat := 4983230072969 + 3 ^ 40 * 7696046 * 2
def baseEnd_7696046 : Nat := 3951770737112101418331535

theorem tailTrace_7696046 : CollatzResearch.WordTrace tailWord_7696046 prefixEnd_7696046 3951770737112101418331535 := by
  unfold tailWord_7696046
  simp only [CollatzResearch.WordTrace]
  refine ⟨35087232234568399607346499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187131905251031464572514661 35087232234568399607346499)
  ·
    refine ⟨52630848351852599411019749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35087232234568399607346499 52630848351852599411019749)
    ·
      refine ⟨9868284065972362389566203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52630848351852599411019749 9868284065972362389566203)
      ·
        refine ⟨14802426098958543584349305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9868284065972362389566203 14802426098958543584349305)
        ·
          refine ⟨11101819574218907688261979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14802426098958543584349305 11101819574218907688261979)
          ·
            refine ⟨16652729361328361532392969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11101819574218907688261979 16652729361328361532392969)
            ·
              refine ⟨12489547020996271149294727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16652729361328361532392969 12489547020996271149294727)
              ·
                refine ⟨18734320531494406723942091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489547020996271149294727 18734320531494406723942091)
                ·
                  refine ⟨28101480797241610085913137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18734320531494406723942091 28101480797241610085913137)
                  ·
                    refine ⟨21076110597931207564434853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28101480797241610085913137 21076110597931207564434853)
                    ·
                      refine ⟨3951770737112101418331535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21076110597931207564434853 3951770737112101418331535)
                      ·
                        rfl

theorem cell23_7696046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_7696046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696046 prefixEnd_7696046 := by exact prefixLift 7696046
  have htrace : WordTrace (prefixWord ++ tailWord_7696046) baseStart_7696046 baseEnd_7696046 := by
    simpa [prefixWord, tailWord_7696046, baseEnd_7696046] using wordTrace_append hprefix tailTrace_7696046
  have hstable : (prefixWord ++ tailWord_7696046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696046).length < 2 ^ (prefixWord ++ tailWord_7696046).sum := by decide
  have hdescent : baseEnd_7696046 < baseStart_7696046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696070 : List Nat := [6, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_7696070 : Nat := 118140960795 + 7696070 * 2 ^ 59
def prefixEnd_7696070 : Nat := 4983230072969 + 3 ^ 40 * 7696070 * 2
def baseEnd_7696070 : Nat := 3951783060647809324431425

theorem tailTrace_7696070 : CollatzResearch.WordTrace tailWord_7696070 prefixEnd_7696070 3951783060647809324431425 := by
  unfold tailWord_7696070
  simp only [CollatzResearch.WordTrace]
  refine ⟨8771835413389382779926427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187132488818973499305097109 8771835413389382779926427)
  ·
    refine ⟨13157753120084074169889641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8771835413389382779926427 13157753120084074169889641)
    ·
      refine ⟨9868314840063055627417231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13157753120084074169889641 9868314840063055627417231)
      ·
        refine ⟨14802472260094583441125847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9868314840063055627417231 14802472260094583441125847)
        ·
          refine ⟨22203708390141875161688771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14802472260094583441125847 22203708390141875161688771)
          ·
            refine ⟨33305562585212812742533157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22203708390141875161688771 33305562585212812742533157)
            ·
              refine ⟨6244792984727402389224967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33305562585212812742533157 6244792984727402389224967)
              ·
                refine ⟨9367189477091103583837451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6244792984727402389224967 9367189477091103583837451)
                ·
                  refine ⟨14050784215636655375756177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9367189477091103583837451 14050784215636655375756177)
                  ·
                    refine ⟨10538088161727491531817133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14050784215636655375756177 10538088161727491531817133)
                    ·
                      refine ⟨3951783060647809324431425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538088161727491531817133 3951783060647809324431425)
                      ·
                        rfl

theorem cell23_7696070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_7696070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696070 prefixEnd_7696070 := by exact prefixLift 7696070
  have htrace : WordTrace (prefixWord ++ tailWord_7696070) baseStart_7696070 baseEnd_7696070 := by
    simpa [prefixWord, tailWord_7696070, baseEnd_7696070] using wordTrace_append hprefix tailTrace_7696070
  have hstable : (prefixWord ++ tailWord_7696070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696070).length < 2 ^ (prefixWord ++ tailWord_7696070).sum := by decide
  have hdescent : baseEnd_7696070 < baseStart_7696070 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696075 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5]
def baseStart_7696075 : Nat := 118140960795 + 7696075 * 2 ^ 59
def prefixEnd_7696075 : Nat := 4983230072969 + 3 ^ 40 * 7696075 * 2
def baseEnd_7696075 : Nat := 3951785628051081804868901

theorem tailTrace_7696075 : CollatzResearch.WordTrace tailWord_7696075 prefixEnd_7696075 3951785628051081804868901 := by
  unfold tailWord_7696075
  simp only [CollatzResearch.WordTrace]
  refine ⟨280698915593442134811577679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187132610395628089874385119 280698915593442134811577679)
  ·
    refine ⟨421048373390163202217366519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280698915593442134811577679 421048373390163202217366519)
    ·
      refine ⟨631572560085244803326049779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421048373390163202217366519 631572560085244803326049779)
      ·
        refine ⟨947358840127867204989074669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631572560085244803326049779 947358840127867204989074669)
        ·
          refine ⟨355259565047950201870903001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947358840127867204989074669 355259565047950201870903001)
          ·
            refine ⟨266444673785962651403177251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355259565047950201870903001 266444673785962651403177251)
            ·
              refine ⟨399667010678943977104765877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266444673785962651403177251 399667010678943977104765877)
              ·
                refine ⟨37468782251150997853571801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 399667010678943977104765877 37468782251150997853571801)
                ·
                  refine ⟨28101586688363248390178851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37468782251150997853571801 28101586688363248390178851)
                  ·
                    refine ⟨42152380032544872585268277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28101586688363248390178851 42152380032544872585268277)
                    ·
                      refine ⟨3951785628051081804868901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42152380032544872585268277 3951785628051081804868901)
                      ·
                        rfl

theorem cell23_7696075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 5].length) (baseStart_7696075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696075 prefixEnd_7696075 := by exact prefixLift 7696075
  have htrace : WordTrace (prefixWord ++ tailWord_7696075) baseStart_7696075 baseEnd_7696075 := by
    simpa [prefixWord, tailWord_7696075, baseEnd_7696075] using wordTrace_append hprefix tailTrace_7696075
  have hstable : (prefixWord ++ tailWord_7696075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696075).length < 2 ^ (prefixWord ++ tailWord_7696075).sum := by decide
  have hdescent : baseEnd_7696075 < baseStart_7696075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696082 : List Nat := [3, 2, 2, 2, 2, 1, 1, 2, 2, 6]
def baseStart_7696082 : Nat := 118140960795 + 7696082 * 2 ^ 59
def prefixEnd_7696082 : Nat := 4983230072969 + 3 ^ 40 * 7696082 * 2
def baseEnd_7696082 : Nat := 1317263074138554425827123

theorem tailTrace_7696082 : CollatzResearch.WordTrace tailWord_7696082 prefixEnd_7696082 1317263074138554425827123 := by
  unfold tailWord_7696082
  simp only [CollatzResearch.WordTrace]
  refine ⟨70174792726104193751770625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187132780602944516671388333 70174792726104193751770625)
  ·
    refine ⟨52631094544578145313827969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70174792726104193751770625 52631094544578145313827969)
    ·
      refine ⟨39473320908433608985370977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52631094544578145313827969 39473320908433608985370977)
      ·
        refine ⟨29604990681325206739028233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39473320908433608985370977 29604990681325206739028233)
        ·
          refine ⟨22203743010993905054271175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29604990681325206739028233 22203743010993905054271175)
          ·
            refine ⟨33305614516490857581406763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22203743010993905054271175 33305614516490857581406763)
            ·
              refine ⟨49958421774736286372110145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33305614516490857581406763 49958421774736286372110145)
              ·
                refine ⟨37468816331052214779082609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49958421774736286372110145 37468816331052214779082609)
                ·
                  refine ⟨28101612248289161084311957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37468816331052214779082609 28101612248289161084311957)
                  ·
                    refine ⟨1317263074138554425827123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28101612248289161084311957 1317263074138554425827123)
                    ·
                      rfl

theorem cell23_7696082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_7696082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696082 prefixEnd_7696082 := by exact prefixLift 7696082
  have htrace : WordTrace (prefixWord ++ tailWord_7696082) baseStart_7696082 baseEnd_7696082 := by
    simpa [prefixWord, tailWord_7696082, baseEnd_7696082] using wordTrace_append hprefix tailTrace_7696082
  have hstable : (prefixWord ++ tailWord_7696082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696082).length < 2 ^ (prefixWord ++ tailWord_7696082).sum := by decide
  have hdescent : baseEnd_7696082 < baseStart_7696082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696106 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_7696106 : Nat := 118140960795 + 7696106 * 2 ^ 59
def prefixEnd_7696106 : Nat := 4983230072969 + 3 ^ 40 * 7696106 * 2
def baseEnd_7696106 : Nat := 3951801545951371183581259

theorem tailTrace_7696106 : CollatzResearch.WordTrace tailWord_7696106 prefixEnd_7696106 3951801545951371183581259 := by
  unfold tailWord_7696106
  simp only [CollatzResearch.WordTrace]
  refine ⟨70175011564082456776489043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187133364170886551403970781 70175011564082456776489043)
  ·
    refine ⟨105262517346123685164733565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70175011564082456776489043 105262517346123685164733565)
    ·
      refine ⟨39473444004796381936775087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105262517346123685164733565 39473444004796381936775087)
      ·
        refine ⟨59210166007194572905162631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39473444004796381936775087 59210166007194572905162631)
        ·
          refine ⟨88815249010791859357743947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59210166007194572905162631 88815249010791859357743947)
          ·
            refine ⟨133222873516187789036615921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88815249010791859357743947 133222873516187789036615921)
            ·
              refine ⟨99917155137140841777461941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133222873516187789036615921 99917155137140841777461941)
              ·
                refine ⟨9367233294106953916637057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99917155137140841777461941 9367233294106953916637057)
                ·
                  refine ⟨7025424970580215437477793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9367233294106953916637057 7025424970580215437477793)
                  ·
                    refine ⟨5269068727935161578108345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7025424970580215437477793 5269068727935161578108345)
                    ·
                      refine ⟨3951801545951371183581259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269068727935161578108345 3951801545951371183581259)
                      ·
                        rfl

theorem cell23_7696106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_7696106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696106 prefixEnd_7696106 := by exact prefixLift 7696106
  have htrace : WordTrace (prefixWord ++ tailWord_7696106) baseStart_7696106 baseEnd_7696106 := by
    simpa [prefixWord, tailWord_7696106, baseEnd_7696106] using wordTrace_append hprefix tailTrace_7696106
  have hstable : (prefixWord ++ tailWord_7696106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696106).length < 2 ^ (prefixWord ++ tailWord_7696106).sum := by decide
  have hdescent : baseEnd_7696106 < baseStart_7696106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696129 : List Nat := [1, 2, 4, 1, 1, 1, 5, 3, 5]
def baseStart_7696129 : Nat := 118140960795 + 7696129 * 2 ^ 59
def prefixEnd_7696129 : Nat := 4983230072969 + 3 ^ 40 * 7696129 * 2
def baseEnd_7696129 : Nat := 439090372889602732621517

theorem tailTrace_7696129 : CollatzResearch.WordTrace tailWord_7696129 prefixEnd_7696129 439090372889602732621517 := by
  unfold tailWord_7696129
  simp only [CollatzResearch.WordTrace]
  refine ⟨280700885135246502034043441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187133923423497668022695627 280700885135246502034043441)
  ·
    refine ⟨210525663851434876525532581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280700885135246502034043441 210525663851434876525532581)
    ·
      refine ⟨39473561972144039348537359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210525663851434876525532581 39473561972144039348537359)
      ·
        refine ⟨59210342958216059022806039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39473561972144039348537359 59210342958216059022806039)
        ·
          refine ⟨88815514437324088534209059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59210342958216059022806039 88815514437324088534209059)
          ·
            refine ⟨133223271655986132801313589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88815514437324088534209059 133223271655986132801313589)
            ·
              refine ⟨12489681717748699950123149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133223271655986132801313589 12489681717748699950123149)
              ·
                refine ⟨4683630644155762481296181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12489681717748699950123149 4683630644155762481296181)
                ·
                  refine ⟨439090372889602732621517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4683630644155762481296181 439090372889602732621517)
                  ·
                    rfl

theorem cell23_7696129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 3, 5].length) (baseStart_7696129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696129 prefixEnd_7696129 := by exact prefixLift 7696129
  have htrace : WordTrace (prefixWord ++ tailWord_7696129) baseStart_7696129 baseEnd_7696129 := by
    simpa [prefixWord, tailWord_7696129, baseEnd_7696129] using wordTrace_append hprefix tailTrace_7696129
  have hstable : (prefixWord ++ tailWord_7696129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696129).length < 2 ^ (prefixWord ++ tailWord_7696129).sum := by decide
  have hdescent : baseEnd_7696129 < baseStart_7696129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696142 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 4, 5]
def baseStart_7696142 : Nat := 118140960795 + 7696142 * 2 ^ 59
def prefixEnd_7696142 : Nat := 4983230072969 + 3 ^ 40 * 7696142 * 2
def baseEnd_7696142 : Nat := 1317273343751644347577031

theorem tailTrace_7696142 : CollatzResearch.WordTrace tailWord_7696142 prefixEnd_7696142 1317273343751644347577031 := by
  unfold tailWord_7696142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35087669910524925656783335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187134239522799603502844453 35087669910524925656783335)
  ·
    refine ⟨52631504865787388485175003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35087669910524925656783335 52631504865787388485175003)
    ·
      refine ⟨78947257298681082727762505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52631504865787388485175003 78947257298681082727762505)
      ·
        refine ⟨59210442974010812045821879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78947257298681082727762505 59210442974010812045821879)
        ·
          refine ⟨88815664461016218068732819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59210442974010812045821879 88815664461016218068732819)
          ·
            refine ⟨133223496691524327103099229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88815664461016218068732819 133223496691524327103099229)
            ·
              refine ⟨49958811259321622663662211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133223496691524327103099229 49958811259321622663662211)
              ·
                refine ⟨74938216888982433995493317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49958811259321622663662211 74938216888982433995493317)
                ·
                  refine ⟨14050915666684206374154997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74938216888982433995493317 14050915666684206374154997)
                  ·
                    refine ⟨1317273343751644347577031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14050915666684206374154997 1317273343751644347577031)
                    ·
                      rfl

theorem cell23_7696142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_7696142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696142 prefixEnd_7696142 := by exact prefixLift 7696142
  have htrace : WordTrace (prefixWord ++ tailWord_7696142) baseStart_7696142 baseEnd_7696142 := by
    simpa [prefixWord, tailWord_7696142, baseEnd_7696142] using wordTrace_append hprefix tailTrace_7696142
  have hstable : (prefixWord ++ tailWord_7696142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696142).length < 2 ^ (prefixWord ++ tailWord_7696142).sum := by decide
  have hdescent : baseEnd_7696142 < baseStart_7696142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696146 : List Nat := [3, 2, 4, 1, 1, 3, 1, 1, 7]
def baseStart_7696146 : Nat := 118140960795 + 7696146 * 2 ^ 59
def prefixEnd_7696146 : Nat := 4983230072969 + 3 ^ 40 * 7696146 * 2
def baseEnd_7696146 : Nat := 439091342797505669675675

theorem tailTrace_7696146 : CollatzResearch.WordTrace tailWord_7696146 prefixEnd_7696146 439091342797505669675675 := by
  unfold tailWord_7696146
  simp only [CollatzResearch.WordTrace]
  refine ⟨70175376294046228484353073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187134336784123275958274861 70175376294046228484353073)
  ·
    refine ⟨52631532220534671363264805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70175376294046228484353073 52631532220534671363264805)
    ·
      refine ⟨9868412291350250880612151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52631532220534671363264805 9868412291350250880612151)
      ·
        refine ⟨14802618437025376320918227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9868412291350250880612151 14802618437025376320918227)
        ·
          refine ⟨22203927655538064481377341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14802618437025376320918227 22203927655538064481377341)
          ·
            refine ⟨8326472870826774180516503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22203927655538064481377341 8326472870826774180516503)
            ·
              refine ⟨12489709306240161270774755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8326472870826774180516503 12489709306240161270774755)
              ·
                refine ⟨18734563959360241906162133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489709306240161270774755 18734563959360241906162133)
                ·
                  refine ⟨439091342797505669675675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18734563959360241906162133 439091342797505669675675)
                  ·
                    rfl

theorem cell23_7696146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 7].length) (baseStart_7696146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696146 prefixEnd_7696146 := by exact prefixLift 7696146
  have htrace : WordTrace (prefixWord ++ tailWord_7696146) baseStart_7696146 baseEnd_7696146 := by
    simpa [prefixWord, tailWord_7696146, baseEnd_7696146] using wordTrace_append hprefix tailTrace_7696146
  have hstable : (prefixWord ++ tailWord_7696146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696146).length < 2 ^ (prefixWord ++ tailWord_7696146).sum := by decide
  have hdescent : baseEnd_7696146 < baseStart_7696146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696199 : List Nat := [1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 3]
def baseStart_7696199 : Nat := 118140960795 + 7696199 * 2 ^ 59
def prefixEnd_7696199 : Nat := 4983230072969 + 3 ^ 40 * 7696199 * 2
def baseEnd_7696199 : Nat := 3951849299652239319718331

theorem tailTrace_7696199 : CollatzResearch.WordTrace tailWord_7696199 prefixEnd_7696199 3951849299652239319718331 := by
  unfold tailWord_7696199
  simp only [CollatzResearch.WordTrace]
  refine ⟨280703438244992903989091651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187135625496661935992727767 280703438244992903989091651)
  ·
    refine ⟨421055157367489355983637477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280703438244992903989091651 421055157367489355983637477)
    ·
      refine ⟨78947842006404254246932027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421055157367489355983637477 78947842006404254246932027)
      ·
        refine ⟨118421763009606381370398041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78947842006404254246932027 118421763009606381370398041)
        ·
          refine ⟨88816322257204786027798531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118421763009606381370398041 88816322257204786027798531)
          ·
            refine ⟨133224483385807179041697797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88816322257204786027798531 133224483385807179041697797)
            ·
              refine ⟨24979590634838846070318337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133224483385807179041697797 24979590634838846070318337)
              ·
                refine ⟨18734692976129134552738753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24979590634838846070318337 18734692976129134552738753)
                ·
                  refine ⟨14051019732096850914554065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18734692976129134552738753 14051019732096850914554065)
                  ·
                    refine ⟨10538264799072638185915549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14051019732096850914554065 10538264799072638185915549)
                    ·
                      refine ⟨3951849299652239319718331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538264799072638185915549 3951849299652239319718331)
                      ·
                        rfl

theorem cell23_7696199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 2, 2, 2, 3].length) (baseStart_7696199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696199 prefixEnd_7696199 := by exact prefixLift 7696199
  have htrace : WordTrace (prefixWord ++ tailWord_7696199) baseStart_7696199 baseEnd_7696199 := by
    simpa [prefixWord, tailWord_7696199, baseEnd_7696199] using wordTrace_append hprefix tailTrace_7696199
  have hstable : (prefixWord ++ tailWord_7696199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696199).length < 2 ^ (prefixWord ++ tailWord_7696199).sum := by decide
  have hdescent : baseEnd_7696199 < baseStart_7696199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696242 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_7696242 : Nat := 118140960795 + 7696242 * 2 ^ 59
def prefixEnd_7696242 : Nat := 4983230072969 + 3 ^ 40 * 7696242 * 2
def baseEnd_7696242 : Nat := 3951871379320382651480633

theorem tailTrace_7696242 : CollatzResearch.WordTrace tailWord_7696242 prefixEnd_7696242 3951871379320382651480633 := by
  unfold tailWord_7696242
  simp only [CollatzResearch.WordTrace]
  refine ⟨70176251645959280583226745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187136671055891414888604653 70176251645959280583226745)
  ·
    refine ⟨52632188734469460437420059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70176251645959280583226745 52632188734469460437420059)
    ·
      refine ⟨78948283101704190656130089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52632188734469460437420059 78948283101704190656130089)
      ·
        refine ⟨59211212326278142992097567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78948283101704190656130089 59211212326278142992097567)
        ·
          refine ⟨88816818489417214488146351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59211212326278142992097567 88816818489417214488146351)
          ·
            refine ⟨133225227734125821732219527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88816818489417214488146351 133225227734125821732219527)
            ·
              refine ⟨199837841601188732598329291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133225227734125821732219527 199837841601188732598329291)
              ·
                refine ⟨299756762401783098897493937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199837841601188732598329291 299756762401783098897493937)
                ·
                  refine ⟨224817571801337324173120453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299756762401783098897493937 224817571801337324173120453)
                  ·
                    refine ⟨42153294712750748282460085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 224817571801337324173120453 42153294712750748282460085)
                    ·
                      refine ⟨3951871379320382651480633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42153294712750748282460085 3951871379320382651480633)
                      ·
                        rfl

theorem cell23_7696242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_7696242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696242 prefixEnd_7696242 := by exact prefixLift 7696242
  have htrace : WordTrace (prefixWord ++ tailWord_7696242) baseStart_7696242 baseEnd_7696242 := by
    simpa [prefixWord, tailWord_7696242, baseEnd_7696242] using wordTrace_append hprefix tailTrace_7696242
  have hstable : (prefixWord ++ tailWord_7696242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696242).length < 2 ^ (prefixWord ++ tailWord_7696242).sum := by decide
  have hdescent : baseEnd_7696242 < baseStart_7696242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696249 : List Nat := [1, 2, 1, 3, 2, 2, 3, 3, 1, 5]
def baseStart_7696249 : Nat := 118140960795 + 7696249 * 2 ^ 59
def prefixEnd_7696249 : Nat := 4983230072969 + 3 ^ 40 * 7696249 * 2
def baseEnd_7696249 : Nat := 1317291657894988041364367

theorem tailTrace_7696249 : CollatzResearch.WordTrace tailWord_7696249 prefixEnd_7696249 1317291657894988041364367 := by
  unfold tailWord_7696249
  simp only [CollatzResearch.WordTrace]
  refine ⟨280705261894811762528411801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187136841263207841685607867 280705261894811762528411801)
  ·
    refine ⟨210528946421108821896308851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280705261894811762528411801 210528946421108821896308851)
    ·
      refine ⟨315793419631663232844463277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210528946421108821896308851 315793419631663232844463277)
      ·
        refine ⟨118422532361873712316673729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315793419631663232844463277 118422532361873712316673729)
        ·
          refine ⟨88816899271405284237505297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118422532361873712316673729 88816899271405284237505297)
          ·
            refine ⟨66612674453553963178128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88816899271405284237505297 66612674453553963178128973)
            ·
              refine ⟨24979752920082736191798365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66612674453553963178128973 24979752920082736191798365)
              ·
                refine ⟨9367407345031026071924387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24979752920082736191798365 9367407345031026071924387)
                ·
                  refine ⟨14051111017546539107886581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9367407345031026071924387 14051111017546539107886581)
                  ·
                    refine ⟨1317291657894988041364367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14051111017546539107886581 1317291657894988041364367)
                    ·
                      rfl

theorem cell23_7696249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_7696249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696249 prefixEnd_7696249 := by exact prefixLift 7696249
  have htrace : WordTrace (prefixWord ++ tailWord_7696249) baseStart_7696249 baseEnd_7696249 := by
    simpa [prefixWord, tailWord_7696249, baseEnd_7696249] using wordTrace_append hprefix tailTrace_7696249
  have hstable : (prefixWord ++ tailWord_7696249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696249).length < 2 ^ (prefixWord ++ tailWord_7696249).sum := by decide
  have hdescent : baseEnd_7696249 < baseStart_7696249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696263 : List Nat := [1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 3]
def baseStart_7696263 : Nat := 118140960795 + 7696263 * 2 ^ 59
def prefixEnd_7696263 : Nat := 4983230072969 + 3 ^ 40 * 7696263 * 2
def baseEnd_7696263 : Nat := 3951882162414127069318037

theorem tailTrace_7696263 : CollatzResearch.WordTrace tailWord_7696263 prefixEnd_7696263 3951882162414127069318037 := by
  unfold tailWord_7696263
  simp only [CollatzResearch.WordTrace]
  refine ⟨280705772516761042919421443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187137181677840695279614295 280705772516761042919421443)
  ·
    refine ⟨421058658775141564379132165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280705772516761042919421443 421058658775141564379132165)
    ·
      refine ⟨78948498520339043321087281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421058658775141564379132165 78948498520339043321087281)
      ·
        refine ⟨59211373890254282490815461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78948498520339043321087281 59211373890254282490815461)
        ·
          refine ⟨11102132604422677967027899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59211373890254282490815461 11102132604422677967027899)
          ·
            refine ⟨16653198906634016950541849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102132604422677967027899 16653198906634016950541849)
            ·
              refine ⟨12489899179975512712906387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16653198906634016950541849 12489899179975512712906387)
              ·
                refine ⟨18734848769963269069359581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489899179975512712906387 18734848769963269069359581)
                ·
                  refine ⟨7025568288736225901009843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18734848769963269069359581 7025568288736225901009843)
                  ·
                    refine ⟨10538352433104338851514765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7025568288736225901009843 10538352433104338851514765)
                    ·
                      refine ⟨3951882162414127069318037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538352433104338851514765 3951882162414127069318037)
                      ·
                        rfl

theorem cell23_7696263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_7696263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696263 prefixEnd_7696263 := by exact prefixLift 7696263
  have htrace : WordTrace (prefixWord ++ tailWord_7696263) baseStart_7696263 baseEnd_7696263 := by
    simpa [prefixWord, tailWord_7696263, baseEnd_7696263] using wordTrace_append hprefix tailTrace_7696263
  have hstable : (prefixWord ++ tailWord_7696263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696263).length < 2 ^ (prefixWord ++ tailWord_7696263).sum := by decide
  have hdescent : baseEnd_7696263 < baseStart_7696263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696272 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_7696272 : Nat := 118140960795 + 7696272 * 2 ^ 59
def prefixEnd_7696272 : Nat := 4983230072969 + 3 ^ 40 * 7696272 * 2
def baseEnd_7696272 : Nat := 3951886783740017534105495

theorem tailTrace_7696272 : CollatzResearch.WordTrace tailWord_7696272 prefixEnd_7696272 3951886783740017534105495 := by
  unfold tailWord_7696272
  simp only [CollatzResearch.WordTrace]
  refine ⟨140353050386864218728249535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187137400515818958304332713 140353050386864218728249535)
  ·
    refine ⟨210529575580296328092374303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140353050386864218728249535 210529575580296328092374303)
    ·
      refine ⟨315794363370444492138561455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210529575580296328092374303 315794363370444492138561455)
      ·
        refine ⟨473691545055666738207842183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315794363370444492138561455 473691545055666738207842183)
        ·
          refine ⟨710537317583500107311763275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473691545055666738207842183 710537317583500107311763275)
          ·
            refine ⟨1065805976375250160967644913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710537317583500107311763275 1065805976375250160967644913)
            ·
              refine ⟨799354482281437620725733685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1065805976375250160967644913 799354482281437620725733685)
              ·
                refine ⟨74939482713884776943037533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 799354482281437620725733685 74939482713884776943037533)
                ·
                  refine ⟨28102306017706791353639075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74939482713884776943037533 28102306017706791353639075)
                  ·
                    refine ⟨42153459026560187030458613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28102306017706791353639075 42153459026560187030458613)
                    ·
                      refine ⟨3951886783740017534105495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42153459026560187030458613 3951886783740017534105495)
                      ·
                        rfl

theorem cell23_7696272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_7696272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696272 prefixEnd_7696272 := by exact prefixLift 7696272
  have htrace : WordTrace (prefixWord ++ tailWord_7696272) baseStart_7696272 baseEnd_7696272 := by
    simpa [prefixWord, tailWord_7696272, baseEnd_7696272] using wordTrace_append hprefix tailTrace_7696272
  have hstable : (prefixWord ++ tailWord_7696272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696272).length < 2 ^ (prefixWord ++ tailWord_7696272).sum := by decide
  have hdescent : baseEnd_7696272 < baseStart_7696272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696279 : List Nat := [1, 1, 3, 3, 1, 3, 3, 1, 1, 6]
def baseStart_7696279 : Nat := 118140960795 + 7696279 * 2 ^ 59
def prefixEnd_7696279 : Nat := 4983230072969 + 3 ^ 40 * 7696279 * 2
def baseEnd_7696279 : Nat := 1317296792701533002239321

theorem tailTrace_7696279 : CollatzResearch.WordTrace tailWord_7696279 prefixEnd_7696279 1317296792701533002239321 := by
  unfold tailWord_7696279
  simp only [CollatzResearch.WordTrace]
  refine ⟨280706356084703077652003891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187137570723135385101335927 280706356084703077652003891)
  ·
    refine ⟨421059534127054616478005837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280706356084703077652003891 421059534127054616478005837)
    ·
      refine ⟨157897325297645481179252189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421059534127054616478005837 157897325297645481179252189)
      ·
        refine ⟨59211496986617055442219571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157897325297645481179252189 59211496986617055442219571)
        ·
          refine ⟨88817245479925583163329357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59211496986617055442219571 88817245479925583163329357)
          ·
            refine ⟨33306467054972093686248509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88817245479925583163329357 33306467054972093686248509)
            ·
              refine ⟨12489925145614535132343191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33306467054972093686248509 12489925145614535132343191)
              ·
                refine ⟨18734887718421802698514787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12489925145614535132343191 18734887718421802698514787)
                ·
                  refine ⟨28102331577632704047772181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18734887718421802698514787 28102331577632704047772181)
                  ·
                    refine ⟨1317296792701533002239321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28102331577632704047772181 1317296792701533002239321)
                    ·
                      rfl

theorem cell23_7696279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_7696279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696279 prefixEnd_7696279 := by exact prefixLift 7696279
  have htrace : WordTrace (prefixWord ++ tailWord_7696279) baseStart_7696279 baseEnd_7696279 := by
    simpa [prefixWord, tailWord_7696279, baseEnd_7696279] using wordTrace_append hprefix tailTrace_7696279
  have hstable : (prefixWord ++ tailWord_7696279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696279).length < 2 ^ (prefixWord ++ tailWord_7696279).sum := by decide
  have hdescent : baseEnd_7696279 < baseStart_7696279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696309 : List Nat := [1, 3, 3, 2, 1, 4, 9]
def baseStart_7696309 : Nat := 118140960795 + 7696309 * 2 ^ 59
def prefixEnd_7696309 : Nat := 4983230072969 + 3 ^ 40 * 7696309 * 2
def baseEnd_7696309 : Nat := 48788960278076961596825

theorem tailTrace_7696309 : CollatzResearch.WordTrace tailWord_7696309 prefixEnd_7696309 48788960278076961596825 := by
  unfold tailWord_7696309
  simp only [CollatzResearch.WordTrace]
  refine ⟨280707450274594392775595981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187138300183062928517063987 280707450274594392775595981)
  ·
    refine ⟨105265293852972897290848493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280707450274594392775595981 105265293852972897290848493)
    ·
      refine ⟨39474485194864836484068185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105265293852972897290848493 39474485194864836484068185)
      ·
        refine ⟨29605863896148627363051139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39474485194864836484068185 29605863896148627363051139)
        ·
          refine ⟨44408795844222941044576709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29605863896148627363051139 44408795844222941044576709)
          ·
            refine ⟨8326649220791801445858133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44408795844222941044576709 8326649220791801445858133)
            ·
              refine ⟨48788960278076961596825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8326649220791801445858133 48788960278076961596825)
              ·
                rfl

theorem cell23_7696309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 9].length) (baseStart_7696309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696309 prefixEnd_7696309 := by exact prefixLift 7696309
  have htrace : WordTrace (prefixWord ++ tailWord_7696309) baseStart_7696309 baseEnd_7696309 := by
    simpa [prefixWord, tailWord_7696309, baseEnd_7696309] using wordTrace_append hprefix tailTrace_7696309
  have hstable : (prefixWord ++ tailWord_7696309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696309).length < 2 ^ (prefixWord ++ tailWord_7696309).sum := by decide
  have hdescent : baseEnd_7696309 < baseStart_7696309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696379 : List Nat := [1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 3]
def baseStart_7696379 : Nat := 118140960795 + 7696379 * 2 ^ 59
def prefixEnd_7696379 : Nat := 4983230072969 + 3 ^ 40 * 7696379 * 2
def baseEnd_7696379 : Nat := 3951941726170048615467503

theorem tailTrace_7696379 : CollatzResearch.WordTrace tailWord_7696379 prefixEnd_7696379 3951941726170048615467503 := by
  unfold tailWord_7696379
  simp only [CollatzResearch.WordTrace]
  refine ⟨280710003384340794730644191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187140002256227196487096127 280710003384340794730644191)
  ·
    refine ⟨421065005076511192095966287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280710003384340794730644191 421065005076511192095966287)
    ·
      refine ⟨631597507614766788143949431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421065005076511192095966287 631597507614766788143949431)
      ·
        refine ⟨947396261422150182215924147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631597507614766788143949431 947396261422150182215924147)
        ·
          refine ⟨1421094392133225273323886221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947396261422150182215924147 1421094392133225273323886221)
          ·
            refine ⟨532910397049959477496457333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1421094392133225273323886221 532910397049959477496457333)
            ·
              refine ⟨49960349723433701015292875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 532910397049959477496457333 49960349723433701015292875)
              ·
                refine ⟨74940524585150551522939313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49960349723433701015292875 74940524585150551522939313)
                ·
                  refine ⟨56205393438862913642204485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74940524585150551522939313 56205393438862913642204485)
                  ·
                    refine ⟨10538511269786796307913341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56205393438862913642204485 10538511269786796307913341)
                    ·
                      refine ⟨3951941726170048615467503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538511269786796307913341 3951941726170048615467503)
                      ·
                        rfl

theorem cell23_7696379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 4, 3].length) (baseStart_7696379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696379 prefixEnd_7696379 := by exact prefixLift 7696379
  have htrace : WordTrace (prefixWord ++ tailWord_7696379) baseStart_7696379 baseEnd_7696379 := by
    simpa [prefixWord, tailWord_7696379, baseEnd_7696379] using wordTrace_append hprefix tailTrace_7696379
  have hstable : (prefixWord ++ tailWord_7696379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696379).length < 2 ^ (prefixWord ++ tailWord_7696379).sum := by decide
  have hdescent : baseEnd_7696379 < baseStart_7696379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696389 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_7696389 : Nat := 118140960795 + 7696389 * 2 ^ 59
def prefixEnd_7696389 : Nat := 4983230072969 + 3 ^ 40 * 7696389 * 2
def baseEnd_7696389 : Nat := 3951946860976593576342457

theorem tailTrace_7696389 : CollatzResearch.WordTrace tailWord_7696389 prefixEnd_7696389 3951946860976593576342457 := by
  unfold tailWord_7696389
  simp only [CollatzResearch.WordTrace]
  refine ⟨280710368114304566438508221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187140245409536377625672147 280710368114304566438508221)
  ·
    refine ⟨105266388042864212414440583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280710368114304566438508221 105266388042864212414440583)
    ·
      refine ⟨157899582064296318621660875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105266388042864212414440583 157899582064296318621660875)
      ·
        refine ⟨236849373096444477932491313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157899582064296318621660875 236849373096444477932491313)
        ·
          refine ⟨177637029822333358449368485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236849373096444477932491313 177637029822333358449368485)
          ·
            refine ⟨33306943091687504709256591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177637029822333358449368485 33306943091687504709256591)
            ·
              refine ⟨49960414637531257063884887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33306943091687504709256591 49960414637531257063884887)
              ·
                refine ⟨74940621956296885595827331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49960414637531257063884887 74940621956296885595827331)
                ·
                  refine ⟨112410932934445328393740997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74940621956296885595827331 112410932934445328393740997)
                  ·
                    refine ⟨21077049925208499073826437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112410932934445328393740997 21077049925208499073826437)
                    ·
                      refine ⟨3951946860976593576342457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21077049925208499073826437 3951946860976593576342457)
                      ·
                        rfl

theorem cell23_7696389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_7696389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696389 prefixEnd_7696389 := by exact prefixLift 7696389
  have htrace : WordTrace (prefixWord ++ tailWord_7696389) baseStart_7696389 baseEnd_7696389 := by
    simpa [prefixWord, tailWord_7696389, baseEnd_7696389] using wordTrace_append hprefix tailTrace_7696389
  have hstable : (prefixWord ++ tailWord_7696389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696389).length < 2 ^ (prefixWord ++ tailWord_7696389).sum := by decide
  have hdescent : baseEnd_7696389 < baseStart_7696389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696409 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_7696409 : Nat := 118140960795 + 7696409 * 2 ^ 59
def prefixEnd_7696409 : Nat := 4983230072969 + 3 ^ 40 * 7696409 * 2
def baseEnd_7696409 : Nat := 3951957130589683498092365

theorem tailTrace_7696409 : CollatzResearch.WordTrace tailWord_7696409 prefixEnd_7696409 3951957130589683498092365 := by
  unfold tailWord_7696409
  simp only [CollatzResearch.WordTrace]
  refine ⟨280711097574232109854236281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187140731716154739902824187 280711097574232109854236281)
  ·
    refine ⟨210533323180674082390677211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280711097574232109854236281 210533323180674082390677211)
    ·
      refine ⟨315799984771011123586015817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210533323180674082390677211 315799984771011123586015817)
      ·
        refine ⟨236849988578258342689511863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315799984771011123586015817 236849988578258342689511863)
        ·
          refine ⟨355274982867387514034267795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236849988578258342689511863 355274982867387514034267795)
          ·
            refine ⟨532912474301081271051401693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355274982867387514034267795 532912474301081271051401693)
            ·
              refine ⟨199842177862905476644275635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 532912474301081271051401693 199842177862905476644275635)
              ·
                refine ⟨299763266794358214966413453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199842177862905476644275635 299763266794358214966413453)
                ·
                  refine ⟨112411225047884330612405045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299763266794358214966413453 112411225047884330612405045)
                  ·
                    refine ⟨10538552348239155994912973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112411225047884330612405045 10538552348239155994912973)
                    ·
                      refine ⟨3951957130589683498092365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538552348239155994912973 3951957130589683498092365)
                      ·
                        rfl

theorem cell23_7696409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_7696409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696409 prefixEnd_7696409 := by exact prefixLift 7696409
  have htrace : WordTrace (prefixWord ++ tailWord_7696409) baseStart_7696409 baseEnd_7696409 := by
    simpa [prefixWord, tailWord_7696409, baseEnd_7696409] using wordTrace_append hprefix tailTrace_7696409
  have hstable : (prefixWord ++ tailWord_7696409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696409).length < 2 ^ (prefixWord ++ tailWord_7696409).sum := by decide
  have hdescent : baseEnd_7696409 < baseStart_7696409 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696439 : List Nat := [1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_7696439 : Nat := 118140960795 + 7696439 * 2 ^ 59
def prefixEnd_7696439 : Nat := 4983230072969 + 3 ^ 40 * 7696439 * 2
def baseEnd_7696439 : Nat := 3951972535009318380717227

theorem tailTrace_7696439 : CollatzResearch.WordTrace tailWord_7696439 prefixEnd_7696439 3951972535009318380717227 := by
  unfold tailWord_7696439
  simp only [CollatzResearch.WordTrace]
  refine ⟨280712191764123424977828371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187141461176082283318552247 280712191764123424977828371)
  ·
    refine ⟨421068287646185137466742557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280712191764123424977828371 421068287646185137466742557)
    ·
      refine ⟨157900607867319426550028459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421068287646185137466742557 157900607867319426550028459)
      ·
        refine ⟨236850911800979139825042689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157900607867319426550028459 236850911800979139825042689)
        ·
          refine ⟨177638183850734354868782017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236850911800979139825042689 177638183850734354868782017)
          ·
            refine ⟨133228637888050766151586513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177638183850734354868782017 133228637888050766151586513)
            ·
              refine ⟨99921478416038074613689885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133228637888050766151586513 99921478416038074613689885)
              ·
                refine ⟨37470554406014277980133707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99921478416038074613689885 37470554406014277980133707)
                ·
                  refine ⟨56205831609021416970200561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37470554406014277980133707 56205831609021416970200561)
                  ·
                    refine ⟨42154373706766062727650421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56205831609021416970200561 42154373706766062727650421)
                    ·
                      refine ⟨3951972535009318380717227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42154373706766062727650421 3951972535009318380717227)
                      ·
                        rfl

theorem cell23_7696439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_7696439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696439 prefixEnd_7696439 := by exact prefixLift 7696439
  have htrace : WordTrace (prefixWord ++ tailWord_7696439) baseStart_7696439 baseEnd_7696439 := by
    simpa [prefixWord, tailWord_7696439, baseEnd_7696439] using wordTrace_append hprefix tailTrace_7696439
  have hstable : (prefixWord ++ tailWord_7696439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696439).length < 2 ^ (prefixWord ++ tailWord_7696439).sum := by decide
  have hdescent : baseEnd_7696439 < baseStart_7696439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696479 : List Nat := [1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_7696479 : Nat := 118140960795 + 7696479 * 2 ^ 59
def prefixEnd_7696479 : Nat := 4983230072969 + 3 ^ 40 * 7696479 * 2
def baseEnd_7696479 : Nat := 3951993074235498224217043

theorem tailTrace_7696479 : CollatzResearch.WordTrace tailWord_7696479 prefixEnd_7696479 3951993074235498224217043 := by
  unfold tailWord_7696479
  simp only [CollatzResearch.WordTrace]
  refine ⟨280713650683978511809284491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187142433789319007872856327 280713650683978511809284491)
  ·
    refine ⟨421070476025967767713926737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280713650683978511809284491 421070476025967767713926737)
    ·
      refine ⟨315802857019475825785445053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421070476025967767713926737 315802857019475825785445053)
      ·
        refine ⟨118426071382303434669541895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315802857019475825785445053 118426071382303434669541895)
        ·
          refine ⟨177639107073455152004312843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118426071382303434669541895 177639107073455152004312843)
          ·
            refine ⟨266458660610182728006469265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177639107073455152004312843 266458660610182728006469265)
            ·
              refine ⟨199843995457637046004851949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266458660610182728006469265 199843995457637046004851949)
              ·
                refine ⟨74941498296613892251819481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199843995457637046004851949 74941498296613892251819481)
                ·
                  refine ⟨56206123722460419188864611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74941498296613892251819481 56206123722460419188864611)
                  ·
                    refine ⟨84309185583690628783296917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56206123722460419188864611 84309185583690628783296917)
                    ·
                      refine ⟨3951993074235498224217043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84309185583690628783296917 3951993074235498224217043)
                      ·
                        rfl

theorem cell23_7696479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_7696479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696479 prefixEnd_7696479 := by exact prefixLift 7696479
  have htrace : WordTrace (prefixWord ++ tailWord_7696479) baseStart_7696479 baseEnd_7696479 := by
    simpa [prefixWord, tailWord_7696479, baseEnd_7696479] using wordTrace_append hprefix tailTrace_7696479
  have hstable : (prefixWord ++ tailWord_7696479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696479).length < 2 ^ (prefixWord ++ tailWord_7696479).sum := by decide
  have hdescent : baseEnd_7696479 < baseStart_7696479 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696489 : List Nat := [1, 2, 1, 1, 1, 5, 1, 3, 8]
def baseStart_7696489 : Nat := 118140960795 + 7696489 * 2 ^ 59
def prefixEnd_7696489 : Nat := 4983230072969 + 3 ^ 40 * 7696489 * 2
def baseEnd_7696489 : Nat := 439110912115782576121333

theorem tailTrace_7696489 : CollatzResearch.WordTrace tailWord_7696489 prefixEnd_7696489 439110912115782576121333 := by
  unfold tailWord_7696489
  simp only [CollatzResearch.WordTrace]
  refine ⟨280714015413942283517148521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187142676942628189011432347 280714015413942283517148521)
  ·
    refine ⟨210535511560456712637861391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280714015413942283517148521 210535511560456712637861391)
    ·
      refine ⟨315803267340685068956792087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210535511560456712637861391 315803267340685068956792087)
      ·
        refine ⟨473704901011027603435188131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315803267340685068956792087 473704901011027603435188131)
        ·
          refine ⟨710557351516541405152782197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473704901011027603435188131 710557351516541405152782197)
          ·
            refine ⟨66614751704675756733073331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 710557351516541405152782197 66614751704675756733073331)
            ·
              refine ⟨99922127557013635099609997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66614751704675756733073331 99922127557013635099609997)
              ·
                refine ⟨37470797833880113162353749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99922127557013635099609997 37470797833880113162353749)
                ·
                  refine ⟨439110912115782576121333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37470797833880113162353749 439110912115782576121333)
                  ·
                    rfl

theorem cell23_7696489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 3, 8].length) (baseStart_7696489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696489 prefixEnd_7696489 := by exact prefixLift 7696489
  have htrace : WordTrace (prefixWord ++ tailWord_7696489) baseStart_7696489 baseEnd_7696489 := by
    simpa [prefixWord, tailWord_7696489, baseEnd_7696489] using wordTrace_append hprefix tailTrace_7696489
  have hstable : (prefixWord ++ tailWord_7696489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696489).length < 2 ^ (prefixWord ++ tailWord_7696489).sum := by decide
  have hdescent : baseEnd_7696489 < baseStart_7696489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696520 : List Nat := [2, 1, 3, 4, 1, 2, 2, 1, 2, 2, 3]
def baseStart_7696520 : Nat := 118140960795 + 7696520 * 2 ^ 59
def prefixEnd_7696520 : Nat := 4983230072969 + 3 ^ 40 * 7696520 * 2
def baseEnd_7696520 : Nat := 3952014126942332563804355

theorem tailTrace_7696520 : CollatzResearch.WordTrace tailWord_7696520 prefixEnd_7696520 3952014126942332563804355 := by
  unfold tailWord_7696520
  simp only [CollatzResearch.WordTrace]
  refine ⟨140357573038414987905763507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187143430717886650541018009 140357573038414987905763507)
  ·
    refine ⟨210536359557622481858645261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140357573038414987905763507 210536359557622481858645261)
    ·
      refine ⟨78951134834108430696991973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210536359557622481858645261 78951134834108430696991973)
      ·
        refine ⟨14803337781395330755685995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78951134834108430696991973 14803337781395330755685995)
        ·
          refine ⟨22205006672092996133528993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14803337781395330755685995 22205006672092996133528993)
          ·
            refine ⟨16653755004069747100146745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22205006672092996133528993 16653755004069747100146745)
            ·
              refine ⟨12490316253052310325110059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16653755004069747100146745 12490316253052310325110059)
              ·
                refine ⟨18735474379578465487665089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12490316253052310325110059 18735474379578465487665089)
                ·
                  refine ⟨14051605784683849115748817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18735474379578465487665089 14051605784683849115748817)
                  ·
                    refine ⟨10538704338512886836811613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14051605784683849115748817 10538704338512886836811613)
                    ·
                      refine ⟨3952014126942332563804355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538704338512886836811613 3952014126942332563804355)
                      ·
                        rfl

theorem cell23_7696520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_7696520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696520 prefixEnd_7696520 := by exact prefixLift 7696520
  have htrace : WordTrace (prefixWord ++ tailWord_7696520) baseStart_7696520 baseEnd_7696520 := by
    simpa [prefixWord, tailWord_7696520, baseEnd_7696520] using wordTrace_append hprefix tailTrace_7696520
  have hstable : (prefixWord ++ tailWord_7696520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696520).length < 2 ^ (prefixWord ++ tailWord_7696520).sum := by decide
  have hdescent : baseEnd_7696520 < baseStart_7696520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696529 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_7696529 : Nat := 118140960795 + 7696529 * 2 ^ 59
def prefixEnd_7696529 : Nat := 4983230072969 + 3 ^ 40 * 7696529 * 2
def baseEnd_7696529 : Nat := 3952018748268223028591813

theorem tailTrace_7696529 : CollatzResearch.WordTrace tailWord_7696529 prefixEnd_7696529 3952018748268223028591813 := by
  unfold tailWord_7696529
  simp only [CollatzResearch.WordTrace]
  refine ⟨280715474333797370348604641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187143649555864913565736427 280715474333797370348604641)
  ·
    refine ⟨210536605750348027761453481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280715474333797370348604641 210536605750348027761453481)
    ·
      refine ⟨157902454312761020821090111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210536605750348027761453481 157902454312761020821090111)
      ·
        refine ⟨236853681469141531231635167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157902454312761020821090111 236853681469141531231635167)
        ·
          refine ⟨355280522203712296847452751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236853681469141531231635167 355280522203712296847452751)
          ·
            refine ⟨532920783305568445271179127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355280522203712296847452751 532920783305568445271179127)
            ·
              refine ⟨799381174958352667906768691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532920783305568445271179127 799381174958352667906768691)
              ·
                refine ⟨1199071762437529001860153037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 799381174958352667906768691 1199071762437529001860153037)
                ·
                  refine ⟨449651910914073375697557389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1199071762437529001860153037 449651910914073375697557389)
                  ·
                    refine ⟨168619466592777515886584021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 449651910914073375697557389 168619466592777515886584021)
                    ·
                      refine ⟨3952018748268223028591813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168619466592777515886584021 3952018748268223028591813)
                      ·
                        rfl

theorem cell23_7696529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_7696529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696529 prefixEnd_7696529 := by exact prefixLift 7696529
  have htrace : WordTrace (prefixWord ++ tailWord_7696529) baseStart_7696529 baseEnd_7696529 := by
    simpa [prefixWord, tailWord_7696529, baseEnd_7696529] using wordTrace_append hprefix tailTrace_7696529
  have hstable : (prefixWord ++ tailWord_7696529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696529).length < 2 ^ (prefixWord ++ tailWord_7696529).sum := by decide
  have hdescent : baseEnd_7696529 < baseStart_7696529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696573 : List Nat := [1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_7696573 : Nat := 118140960795 + 7696573 * 2 ^ 59
def prefixEnd_7696573 : Nat := 4983230072969 + 3 ^ 40 * 7696573 * 2
def baseEnd_7696573 : Nat := 3952041341417020856441611

theorem tailTrace_7696573 : CollatzResearch.WordTrace tailWord_7696573 prefixEnd_7696573 3952041341417020856441611 := by
  unfold tailWord_7696573
  simp only [CollatzResearch.WordTrace]
  refine ⟨280717079145637965863206373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187144719430425310575470915 280717079145637965863206373)
  ·
    refine ⟨52634452339807118599351195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280717079145637965863206373 52634452339807118599351195)
    ·
      refine ⟨78951678509710677899026793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52634452339807118599351195 78951678509710677899026793)
      ·
        refine ⟨59213758882283008424270095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78951678509710677899026793 59213758882283008424270095)
        ·
          refine ⟨88820638323424512636405143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59213758882283008424270095 88820638323424512636405143)
          ·
            refine ⟨133230957485136768954607715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88820638323424512636405143 133230957485136768954607715)
            ·
              refine ⟨199846436227705153431911573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133230957485136768954607715 199846436227705153431911573)
              ·
                refine ⟨9367801698173679067120855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199846436227705153431911573 9367801698173679067120855)
                ·
                  refine ⟨14051702547260518600681283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9367801698173679067120855 14051702547260518600681283)
                  ·
                    refine ⟨21077553820890777901021925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14051702547260518600681283 21077553820890777901021925)
                    ·
                      refine ⟨3952041341417020856441611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21077553820890777901021925 3952041341417020856441611)
                      ·
                        rfl

theorem cell23_7696573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_7696573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696573 prefixEnd_7696573 := by exact prefixLift 7696573
  have htrace : WordTrace (prefixWord ++ tailWord_7696573) baseStart_7696573 baseEnd_7696573 := by
    simpa [prefixWord, tailWord_7696573, baseEnd_7696573] using wordTrace_append hprefix tailTrace_7696573
  have hstable : (prefixWord ++ tailWord_7696573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696573).length < 2 ^ (prefixWord ++ tailWord_7696573).sum := by decide
  have hdescent : baseEnd_7696573 < baseStart_7696573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696577 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_7696577 : Nat := 118140960795 + 7696577 * 2 ^ 59
def prefixEnd_7696577 : Nat := 4983230072969 + 3 ^ 40 * 7696577 * 2
def baseEnd_7696577 : Nat := 3952043395339638840791593

theorem tailTrace_7696577 : CollatzResearch.WordTrace tailWord_7696577 prefixEnd_7696577 3952043395339638840791593 := by
  unfold tailWord_7696577
  simp only [CollatzResearch.WordTrace]
  refine ⟨280717225037623474546351985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187144816691748983030901323 280717225037623474546351985)
  ·
    refine ⟨210537918778217605909763989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280717225037623474546351985 210537918778217605909763989)
    ·
      refine ⟨9868964942728950277020187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210537918778217605909763989 9868964942728950277020187)
      ·
        refine ⟨14803447414093425415530281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9868964942728950277020187 14803447414093425415530281)
        ·
          refine ⟨11102585560570069061647711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14803447414093425415530281 11102585560570069061647711)
          ·
            refine ⟨16653878340855103592471567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11102585560570069061647711 16653878340855103592471567)
            ·
              refine ⟨24980817511282655388707351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16653878340855103592471567 24980817511282655388707351)
              ·
                refine ⟨37471226266923983083061027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24980817511282655388707351 37471226266923983083061027)
                ·
                  refine ⟨56206839400385974624591541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37471226266923983083061027 56206839400385974624591541)
                  ·
                    refine ⟨5269391193786185121055457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56206839400385974624591541 5269391193786185121055457)
                    ·
                      refine ⟨3952043395339638840791593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269391193786185121055457 3952043395339638840791593)
                      ·
                        rfl

theorem cell23_7696577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_7696577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696577 prefixEnd_7696577 := by exact prefixLift 7696577
  have htrace : WordTrace (prefixWord ++ tailWord_7696577) baseStart_7696577 baseEnd_7696577 := by
    simpa [prefixWord, tailWord_7696577, baseEnd_7696577] using wordTrace_append hprefix tailTrace_7696577
  have hstable : (prefixWord ++ tailWord_7696577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696577).length < 2 ^ (prefixWord ++ tailWord_7696577).sum := by decide
  have hdescent : baseEnd_7696577 < baseStart_7696577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696590 : List Nat := [4, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_7696590 : Nat := 118140960795 + 7696590 * 2 ^ 59
def prefixEnd_7696590 : Nat := 4983230072969 + 3 ^ 40 * 7696590 * 2
def baseEnd_7696590 : Nat := 3952050070588147289929033

theorem tailTrace_7696590 : CollatzResearch.WordTrace tailWord_7696590 prefixEnd_7696590 3952050070588147289929033 := by
  unfold tailWord_7696590
  simp only [CollatzResearch.WordTrace]
  refine ⟨35089712398322047220821903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187145132791050918511050149 35089712398322047220821903)
  ·
    refine ⟨52634568597483070831232855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35089712398322047220821903 52634568597483070831232855)
    ·
      refine ⟨78951852896224606246849283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52634568597483070831232855 78951852896224606246849283)
      ·
        refine ⟨118427779344336909370273925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78951852896224606246849283 118427779344336909370273925)
        ·
          refine ⟨22205208627063170506926361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118427779344336909370273925 22205208627063170506926361)
          ·
            refine ⟨16653906470297377880194771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22205208627063170506926361 16653906470297377880194771)
            ·
              refine ⟨24980859705446066820292157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16653906470297377880194771 24980859705446066820292157)
              ·
                refine ⟨9367822389542275057609559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24980859705446066820292157 9367822389542275057609559)
                ·
                  refine ⟨14051733584313412586414339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9367822389542275057609559 14051733584313412586414339)
                  ·
                    refine ⟨21077600376470118879621509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14051733584313412586414339 21077600376470118879621509)
                    ·
                      refine ⟨3952050070588147289929033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21077600376470118879621509 3952050070588147289929033)
                      ·
                        rfl

theorem cell23_7696590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_7696590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696590 prefixEnd_7696590 := by exact prefixLift 7696590
  have htrace : WordTrace (prefixWord ++ tailWord_7696590) baseStart_7696590 baseEnd_7696590 := by
    simpa [prefixWord, tailWord_7696590, baseEnd_7696590] using wordTrace_append hprefix tailTrace_7696590
  have hstable : (prefixWord ++ tailWord_7696590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696590).length < 2 ^ (prefixWord ++ tailWord_7696590).sum := by decide
  have hdescent : baseEnd_7696590 < baseStart_7696590 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696600 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 2, 4]
def baseStart_7696600 : Nat := 118140960795 + 7696600 * 2 ^ 59
def prefixEnd_7696600 : Nat := 4983230072969 + 3 ^ 40 * 7696600 * 2
def baseEnd_7696600 : Nat := 1317351735131564083601329

theorem tailTrace_7696600 : CollatzResearch.WordTrace tailWord_7696600 prefixEnd_7696600 1317351735131564083601329 := by
  unfold tailWord_7696600
  simp only [CollatzResearch.WordTrace]
  refine ⟨140359031958270074737219627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187145375944360099649626169 140359031958270074737219627)
  ·
    refine ⟨210538547937405112105829441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140359031958270074737219627 210538547937405112105829441)
    ·
      refine ⟨157903910953053834079372081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210538547937405112105829441 157903910953053834079372081)
      ·
        refine ⟨118427933214790375559529061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157903910953053834079372081 118427933214790375559529061)
        ·
          refine ⟨22205237477773195417411699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118427933214790375559529061 22205237477773195417411699)
          ·
            refine ⟨33307856216659793126117549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22205237477773195417411699 33307856216659793126117549)
            ·
              refine ⟨12490446081247422422294081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33307856216659793126117549 12490446081247422422294081)
              ·
                refine ⟨9367834560935566816720561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12490446081247422422294081 9367834560935566816720561)
                ·
                  refine ⟨7025875920701675112540421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9367834560935566816720561 7025875920701675112540421)
                  ·
                    refine ⟨1317351735131564083601329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7025875920701675112540421 1317351735131564083601329)
                    ·
                      rfl

theorem cell23_7696600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 2, 4].length) (baseStart_7696600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696600 prefixEnd_7696600 := by exact prefixLift 7696600
  have htrace : WordTrace (prefixWord ++ tailWord_7696600) baseStart_7696600 baseEnd_7696600 := by
    simpa [prefixWord, tailWord_7696600, baseEnd_7696600] using wordTrace_append hprefix tailTrace_7696600
  have hstable : (prefixWord ++ tailWord_7696600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696600).length < 2 ^ (prefixWord ++ tailWord_7696600).sum := by decide
  have hdescent : baseEnd_7696600 < baseStart_7696600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696674 : List Nat := [3, 3, 1, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_7696674 : Nat := 118140960795 + 7696674 * 2 ^ 59
def prefixEnd_7696674 : Nat := 4983230072969 + 3 ^ 40 * 7696674 * 2
def baseEnd_7696674 : Nat := 3952093202963124961278647

theorem tailTrace_7696674 : CollatzResearch.WordTrace tailWord_7696674 prefixEnd_7696674 3952093202963124961278647 := by
  unfold tailWord_7696674
  simp only [CollatzResearch.WordTrace]
  refine ⟨70180190729568015028158269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187147175278848040075088717 70180190729568015028158269)
  ·
    refine ⟨26317571523588005635559351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70180190729568015028158269 26317571523588005635559351)
    ·
      refine ⟨39476357285382008453339027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26317571523588005635559351 39476357285382008453339027)
      ·
        refine ⟨59214535928073012680008541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39476357285382008453339027 59214535928073012680008541)
        ·
          refine ⟨22205450973027379755003203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59214535928073012680008541 22205450973027379755003203)
          ·
            refine ⟨33308176459541069632504805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22205450973027379755003203 33308176459541069632504805)
            ·
              refine ⟨6245283086163950556094651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33308176459541069632504805 6245283086163950556094651)
              ·
                refine ⟨9367924629245925834141977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245283086163950556094651 9367924629245925834141977)
                ·
                  refine ⟨7025943471934444375606483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9367924629245925834141977 7025943471934444375606483)
                  ·
                    refine ⟨10538915207901666563409725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7025943471934444375606483 10538915207901666563409725)
                    ·
                      refine ⟨3952093202963124961278647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538915207901666563409725 3952093202963124961278647)
                      ·
                        rfl

theorem cell23_7696674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_7696674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696674 prefixEnd_7696674 := by exact prefixLift 7696674
  have htrace : WordTrace (prefixWord ++ tailWord_7696674) baseStart_7696674 baseEnd_7696674 := by
    simpa [prefixWord, tailWord_7696674, baseEnd_7696674] using wordTrace_append hprefix tailTrace_7696674
  have hstable : (prefixWord ++ tailWord_7696674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696674).length < 2 ^ (prefixWord ++ tailWord_7696674).sum := by decide
  have hdescent : baseEnd_7696674 < baseStart_7696674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696697 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 1, 4, 2]
def baseStart_7696697 : Nat := 118140960795 + 7696697 * 2 ^ 59
def prefixEnd_7696697 : Nat := 4983230072969 + 3 ^ 40 * 7696697 * 2
def baseEnd_7696697 : Nat := 3952105013018178371291041

theorem tailTrace_7696697 : CollatzResearch.WordTrace tailWord_7696697 prefixEnd_7696697 3952105013018178371291041 := by
  unfold tailWord_7696697
  simp only [CollatzResearch.WordTrace]
  refine ⟨280721601797188735040720345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187147734531459156693813563 280721601797188735040720345)
  ·
    refine ⟨210541201347891551280540259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280721601797188735040720345 210541201347891551280540259)
    ·
      refine ⟨315811802021837326920810389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210541201347891551280540259 315811802021837326920810389)
      ·
        refine ⟨14803678219773624699412987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 315811802021837326920810389 14803678219773624699412987)
        ·
          refine ⟨22205517329660437049119481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14803678219773624699412987 22205517329660437049119481)
          ·
            refine ⟨16654137997245327786839611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22205517329660437049119481 16654137997245327786839611)
            ·
              refine ⟨24981206995867991680259417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16654137997245327786839611 24981206995867991680259417)
              ·
                refine ⟨18735905246900993760194563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24981206995867991680259417 18735905246900993760194563)
                ·
                  refine ⟨28103857870351490640291845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18735905246900993760194563 28103857870351490640291845)
                  ·
                    refine ⟨5269473350690904495054721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28103857870351490640291845 5269473350690904495054721)
                    ·
                      refine ⟨3952105013018178371291041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269473350690904495054721 3952105013018178371291041)
                      ·
                        rfl

theorem cell23_7696697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_7696697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696697 prefixEnd_7696697 := by exact prefixLift 7696697
  have htrace : WordTrace (prefixWord ++ tailWord_7696697) baseStart_7696697 baseEnd_7696697 := by
    simpa [prefixWord, tailWord_7696697, baseEnd_7696697] using wordTrace_append hprefix tailTrace_7696697
  have hstable : (prefixWord ++ tailWord_7696697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696697).length < 2 ^ (prefixWord ++ tailWord_7696697).sum := by decide
  have hdescent : baseEnd_7696697 < baseStart_7696697 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696713 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_7696713 : Nat := 118140960795 + 7696713 * 2 ^ 59
def prefixEnd_7696713 : Nat := 4983230072969 + 3 ^ 40 * 7696713 * 2
def baseEnd_7696713 : Nat := 3952113228708650308690967

theorem tailTrace_7696713 : CollatzResearch.WordTrace tailWord_7696713 prefixEnd_7696713 3952113228708650308690967 := by
  unfold tailWord_7696713
  simp only [CollatzResearch.WordTrace]
  refine ⟨280722185365130769773302793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187148123576753846515535195 280722185365130769773302793)
  ·
    refine ⟨210541639023848077329977095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280722185365130769773302793 210541639023848077329977095)
    ·
      refine ⟨315812458535772115994965643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210541639023848077329977095 315812458535772115994965643)
      ·
        refine ⟨473718687803658173992448465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315812458535772115994965643 473718687803658173992448465)
        ·
          refine ⟨355289015852743630494336349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473718687803658173992448465 355289015852743630494336349)
          ·
            refine ⟨133233380944778861435376131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355289015852743630494336349 133233380944778861435376131)
            ·
              refine ⟨199850071417168292153064197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133233380944778861435376131 199850071417168292153064197)
              ·
                refine ⟨37471888390719054778699537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199850071417168292153064197 37471888390719054778699537)
                ·
                  refine ⟨28103916293039291084024653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37471888390719054778699537 28103916293039291084024653)
                  ·
                    refine ⟨10538968609889734156509245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28103916293039291084024653 10538968609889734156509245)
                    ·
                      refine ⟨3952113228708650308690967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10538968609889734156509245 3952113228708650308690967)
                      ·
                        rfl

theorem cell23_7696713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_7696713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696713 prefixEnd_7696713 := by exact prefixLift 7696713
  have htrace : WordTrace (prefixWord ++ tailWord_7696713) baseStart_7696713 baseEnd_7696713 := by
    simpa [prefixWord, tailWord_7696713, baseEnd_7696713] using wordTrace_append hprefix tailTrace_7696713
  have hstable : (prefixWord ++ tailWord_7696713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696713).length < 2 ^ (prefixWord ++ tailWord_7696713).sum := by decide
  have hdescent : baseEnd_7696713 < baseStart_7696713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696720 : List Nat := [2, 1, 1, 1, 1, 7, 1, 4, 5]
def baseStart_7696720 : Nat := 118140960795 + 7696720 * 2 ^ 59
def prefixEnd_7696720 : Nat := 4983230072969 + 3 ^ 40 * 7696720 * 2
def baseEnd_7696720 : Nat := 439124091452581309033715

theorem tailTrace_7696720 : CollatzResearch.WordTrace tailWord_7696720 prefixEnd_7696720 439124091452581309033715 := by
  unfold tailWord_7696720
  simp only [CollatzResearch.WordTrace]
  refine ⟨140361220338052704984403807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187148293784070273312538409 140361220338052704984403807)
  ·
    refine ⟨210541830507079057476605711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140361220338052704984403807 210541830507079057476605711)
    ·
      refine ⟨315812745760618586214908567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210541830507079057476605711 315812745760618586214908567)
      ·
        refine ⟨473719118640927879322362851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315812745760618586214908567 473719118640927879322362851)
        ·
          refine ⟨710578677961391818983544277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473719118640927879322362851 710578677961391818983544277)
          ·
            refine ⟨16654187764720120757426819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 710578677961391818983544277 16654187764720120757426819)
            ·
              refine ⟨24981281647080181136140229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16654187764720120757426819 24981281647080181136140229)
              ·
                refine ⟨4683990308827533963026293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24981281647080181136140229 4683990308827533963026293)
                ·
                  refine ⟨439124091452581309033715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4683990308827533963026293 439124091452581309033715)
                  ·
                    rfl

theorem cell23_7696720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 4, 5].length) (baseStart_7696720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696720 prefixEnd_7696720 := by exact prefixLift 7696720
  have htrace : WordTrace (prefixWord ++ tailWord_7696720) baseStart_7696720 baseEnd_7696720 := by
    simpa [prefixWord, tailWord_7696720, baseEnd_7696720] using wordTrace_append hprefix tailTrace_7696720
  have hstable : (prefixWord ++ tailWord_7696720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696720).length < 2 ^ (prefixWord ++ tailWord_7696720).sum := by decide
  have hdescent : baseEnd_7696720 < baseStart_7696720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696740 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 2, 5, 2]
def baseStart_7696740 : Nat := 118140960795 + 7696740 * 2 ^ 59
def prefixEnd_7696740 : Nat := 4983230072969 + 3 ^ 40 * 7696740 * 2
def baseEnd_7696740 : Nat := 3952127092686321703053343

theorem tailTrace_7696740 : CollatzResearch.WordTrace tailWord_7696740 prefixEnd_7696740 3952127092686321703053343 := by
  unfold tailWord_7696740
  simp only [CollatzResearch.WordTrace]
  refine ⟨140361585068016476692267837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187148780090688635589690449 140361585068016476692267837)
  ·
    refine ⟨52635594400506178759600439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140361585068016476692267837 52635594400506178759600439)
    ·
      refine ⟨78953391600759268139400659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52635594400506178759600439 78953391600759268139400659)
      ·
        refine ⟨118430087401138902209100989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78953391600759268139400659 118430087401138902209100989)
        ·
          refine ⟨44411282775427088328412871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118430087401138902209100989 44411282775427088328412871)
          ·
            refine ⟨66616924163140632492619307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44411282775427088328412871 66616924163140632492619307)
            ·
              refine ⟨99925386244710948738928961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66616924163140632492619307 99925386244710948738928961)
              ·
                refine ⟨74944039683533211554196721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99925386244710948738928961 74944039683533211554196721)
                ·
                  refine ⟨56208029762649908665647541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74944039683533211554196721 56208029762649908665647541)
                  ·
                    refine ⟨5269502790248428937404457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56208029762649908665647541 5269502790248428937404457)
                    ·
                      refine ⟨3952127092686321703053343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269502790248428937404457 3952127092686321703053343)
                      ·
                        rfl

theorem cell23_7696740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_7696740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696740 prefixEnd_7696740 := by exact prefixLift 7696740
  have htrace : WordTrace (prefixWord ++ tailWord_7696740) baseStart_7696740 baseEnd_7696740 := by
    simpa [prefixWord, tailWord_7696740, baseEnd_7696740] using wordTrace_append hprefix tailTrace_7696740
  have hstable : (prefixWord ++ tailWord_7696740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696740).length < 2 ^ (prefixWord ++ tailWord_7696740).sum := by decide
  have hdescent : baseEnd_7696740 < baseStart_7696740 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696780 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 3, 4]
def baseStart_7696780 : Nat := 118140960795 + 7696780 * 2 ^ 59
def prefixEnd_7696780 : Nat := 4983230072969 + 3 ^ 40 * 7696780 * 2
def baseEnd_7696780 : Nat := 1317382543970833848851053

theorem tailTrace_7696780 : CollatzResearch.WordTrace tailWord_7696780 prefixEnd_7696780 1317382543970833848851053 := by
  unfold tailWord_7696780
  simp only [CollatzResearch.WordTrace]
  refine ⟨140362314527944020107995897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187149752703925360143994529 140362314527944020107995897)
  ·
    refine ⟨105271735895958015080996923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140362314527944020107995897 105271735895958015080996923)
    ·
      refine ⟨157907603843937022621495385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105271735895958015080996923 157907603843937022621495385)
      ·
        refine ⟨118430702882952766966121539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157907603843937022621495385 118430702882952766966121539)
        ·
          refine ⟨177646054324429150449182309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118430702882952766966121539 177646054324429150449182309)
          ·
            refine ⟨33308635185830465709221683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177646054324429150449182309 33308635185830465709221683)
            ·
              refine ⟨49962952778745698563832525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33308635185830465709221683 49962952778745698563832525)
              ·
                refine ⟨18736107292029636961437197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49962952778745698563832525 18736107292029636961437197)
                ·
                  refine ⟨7026040234511113860538949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18736107292029636961437197 7026040234511113860538949)
                  ·
                    refine ⟨1317382543970833848851053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026040234511113860538949 1317382543970833848851053)
                    ·
                      rfl

theorem cell23_7696780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 3, 4].length) (baseStart_7696780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696780 prefixEnd_7696780 := by exact prefixLift 7696780
  have htrace : WordTrace (prefixWord ++ tailWord_7696780) baseStart_7696780 baseEnd_7696780 := by
    simpa [prefixWord, tailWord_7696780, baseEnd_7696780] using wordTrace_append hprefix tailTrace_7696780
  have hstable : (prefixWord ++ tailWord_7696780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696780).length < 2 ^ (prefixWord ++ tailWord_7696780).sum := by decide
  have hdescent : baseEnd_7696780 < baseStart_7696780 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696843 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4]
def baseStart_7696843 : Nat := 118140960795 + 7696843 * 2 ^ 59
def prefixEnd_7696843 : Nat := 4983230072969 + 3 ^ 40 * 7696843 * 2
def baseEnd_7696843 : Nat := 3952179981193734800065369

theorem tailTrace_7696843 : CollatzResearch.WordTrace tailWord_7696843 prefixEnd_7696843 3952179981193734800065369 := by
  unfold tailWord_7696843
  simp only [CollatzResearch.WordTrace]
  refine ⟨280726926854659801975535183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187151284569773201317023455 280726926854659801975535183)
  ·
    refine ⟨421090390281989702963302775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280726926854659801975535183 421090390281989702963302775)
    ·
      refine ⟨631635585422984554444954163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421090390281989702963302775 631635585422984554444954163)
      ·
        refine ⟨947453378134476831667431245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631635585422984554444954163 947453378134476831667431245)
        ·
          refine ⟨355295016800428811875286717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947453378134476831667431245 355295016800428811875286717)
          ·
            refine ⟨133235631300160804453232519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355295016800428811875286717 133235631300160804453232519)
            ·
              refine ⟨199853446950241206679848779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133235631300160804453232519 199853446950241206679848779)
              ·
                refine ⟨299780170425361810019773169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199853446950241206679848779 299780170425361810019773169)
                ·
                  refine ⟨224835127819021357514829877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299780170425361810019773169 224835127819021357514829877)
                  ·
                    refine ⟨21078293233033252267015301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224835127819021357514829877 21078293233033252267015301)
                    ·
                      refine ⟨3952179981193734800065369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21078293233033252267015301 3952179981193734800065369)
                      ·
                        rfl

theorem cell23_7696843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_7696843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696843 prefixEnd_7696843 := by exact prefixLift 7696843
  have htrace : WordTrace (prefixWord ++ tailWord_7696843) baseStart_7696843 baseEnd_7696843 := by
    simpa [prefixWord, tailWord_7696843, baseEnd_7696843] using wordTrace_append hprefix tailTrace_7696843
  have hstable : (prefixWord ++ tailWord_7696843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696843).length < 2 ^ (prefixWord ++ tailWord_7696843).sum := by decide
  have hdescent : baseEnd_7696843 < baseStart_7696843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696844 : List Nat := [2, 2, 1, 4, 3, 2, 2, 1, 6]
def baseStart_7696844 : Nat := 118140960795 + 7696844 * 2 ^ 59
def prefixEnd_7696844 : Nat := 4983230072969 + 3 ^ 40 * 7696844 * 2
def baseEnd_7696844 : Nat := 439131166074932144016985

theorem tailTrace_7696844 : CollatzResearch.WordTrace tailWord_7696844 prefixEnd_7696844 439131166074932144016985 := by
  unfold tailWord_7696844
  simp only [CollatzResearch.WordTrace]
  refine ⟨140363481663828089573160793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187151308885104119430881057 140363481663828089573160793)
  ·
    refine ⟨105272611247871067179870595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140363481663828089573160793 105272611247871067179870595)
    ·
      refine ⟨157908916871806600769805893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105272611247871067179870595 157908916871806600769805893)
      ·
        refine ⟨29607921913463737644338605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157908916871806600769805893 29607921913463737644338605)
        ·
          refine ⟨11102970717548901616626977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29607921913463737644338605 11102970717548901616626977)
          ·
            refine ⟨8327228038161676212470233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11102970717548901616626977 8327228038161676212470233)
            ·
              refine ⟨6245421028621257159352675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327228038161676212470233 6245421028621257159352675)
              ·
                refine ⟨9368131542931885739029013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245421028621257159352675 9368131542931885739029013)
                ·
                  refine ⟨439131166074932144016985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9368131542931885739029013 439131166074932144016985)
                  ·
                    rfl

theorem cell23_7696844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 2, 1, 6].length) (baseStart_7696844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696844 prefixEnd_7696844 := by exact prefixLift 7696844
  have htrace : WordTrace (prefixWord ++ tailWord_7696844) baseStart_7696844 baseEnd_7696844 := by
    simpa [prefixWord, tailWord_7696844, baseEnd_7696844] using wordTrace_append hprefix tailTrace_7696844
  have hstable : (prefixWord ++ tailWord_7696844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696844).length < 2 ^ (prefixWord ++ tailWord_7696844).sum := by decide
  have hdescent : baseEnd_7696844 < baseStart_7696844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696854 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3]
def baseStart_7696854 : Nat := 118140960795 + 7696854 * 2 ^ 59
def prefixEnd_7696854 : Nat := 4983230072969 + 3 ^ 40 * 7696854 * 2
def baseEnd_7696854 : Nat := 3952185629480934257027819

theorem tailTrace_7696854 : CollatzResearch.WordTrace tailWord_7696854 prefixEnd_7696854 3952185629480934257027819 := by
  unfold tailWord_7696854
  simp only [CollatzResearch.WordTrace]
  refine ⟨17545458003601246928386601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187151552038413300569457077 17545458003601246928386601)
  ·
    refine ⟨13159093502700935196289951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17545458003601246928386601 13159093502700935196289951)
    ·
      refine ⟨19738640254051402794434927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13159093502700935196289951 19738640254051402794434927)
      ·
        refine ⟨29607960381077104191652391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19738640254051402794434927 29607960381077104191652391)
        ·
          refine ⟨44411940571615656287478587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29607960381077104191652391 44411940571615656287478587)
          ·
            refine ⟨66617910857423484431217881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44411940571615656287478587 66617910857423484431217881)
            ·
              refine ⟨49963433143067613323413411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66617910857423484431217881 49963433143067613323413411)
              ·
                refine ⟨74945149714601419985120117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49963433143067613323413411 74945149714601419985120117)
                ·
                  refine ⟨7026107785743883123605011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74945149714601419985120117 7026107785743883123605011)
                  ·
                    refine ⟨10539161678615824685407517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026107785743883123605011 10539161678615824685407517)
                    ·
                      refine ⟨3952185629480934257027819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539161678615824685407517 3952185629480934257027819)
                      ·
                        rfl

theorem cell23_7696854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_7696854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696854 prefixEnd_7696854 := by exact prefixLift 7696854
  have htrace : WordTrace (prefixWord ++ tailWord_7696854) baseStart_7696854 baseEnd_7696854 := by
    simpa [prefixWord, tailWord_7696854, baseEnd_7696854] using wordTrace_append hprefix tailTrace_7696854
  have hstable : (prefixWord ++ tailWord_7696854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696854).length < 2 ^ (prefixWord ++ tailWord_7696854).sum := by decide
  have hdescent : baseEnd_7696854 < baseStart_7696854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696873 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_7696873 : Nat := 118140960795 + 7696873 * 2 ^ 59
def prefixEnd_7696873 : Nat := 4983230072969 + 3 ^ 40 * 7696873 * 2
def baseEnd_7696873 : Nat := 3952195385613369682690231

theorem tailTrace_7696873 : CollatzResearch.WordTrace tailWord_7696873 prefixEnd_7696873 3952195385613369682690231 := by
  unfold tailWord_7696873
  simp only [CollatzResearch.WordTrace]
  refine ⟨280728021044551117099127273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187152014029700744732751515 280728021044551117099127273)
  ·
    refine ⟨210546015783413337824345455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280728021044551117099127273 210546015783413337824345455)
    ·
      refine ⟨315819023675120006736518183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210546015783413337824345455 315819023675120006736518183)
      ·
        refine ⟨473728535512680010104777275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315819023675120006736518183 473728535512680010104777275)
        ·
          refine ⟨710592803269020015157165913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473728535512680010104777275 710592803269020015157165913)
          ·
            refine ⟨532944602451765011367874435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710592803269020015157165913 532944602451765011367874435)
            ·
              refine ⟨799416903677647517051811653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532944602451765011367874435 799416903677647517051811653)
              ·
                refine ⟨149890669439558909447214685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 799416903677647517051811653 149890669439558909447214685)
                ·
                  refine ⟨56209001039834591042705507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149890669439558909447214685 56209001039834591042705507)
                  ·
                    refine ⟨84313501559751886564058261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56209001039834591042705507 84313501559751886564058261)
                    ·
                      refine ⟨3952195385613369682690231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84313501559751886564058261 3952195385613369682690231)
                      ·
                        rfl

theorem cell23_7696873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_7696873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696873 prefixEnd_7696873 := by exact prefixLift 7696873
  have htrace : WordTrace (prefixWord ++ tailWord_7696873) baseStart_7696873 baseEnd_7696873 := by
    simpa [prefixWord, tailWord_7696873, baseEnd_7696873] using wordTrace_append hprefix tailTrace_7696873
  have hstable : (prefixWord ++ tailWord_7696873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696873).length < 2 ^ (prefixWord ++ tailWord_7696873).sum := by decide
  have hdescent : baseEnd_7696873 < baseStart_7696873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696874 : List Nat := [3, 1, 3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_7696874 : Nat := 118140960795 + 7696874 * 2 ^ 59
def prefixEnd_7696874 : Nat := 4983230072969 + 3 ^ 40 * 7696874 * 2
def baseEnd_7696874 : Nat := 1317398633031341392925909

theorem tailTrace_7696874 : CollatzResearch.WordTrace tailWord_7696874 prefixEnd_7696874 1317398633031341392925909 := by
  unfold tailWord_7696874
  simp only [CollatzResearch.WordTrace]
  refine ⟨70182014379386873567478419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187152038345031662846609117 70182014379386873567478419)
  ·
    refine ⟨105273021569080310351217629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70182014379386873567478419 105273021569080310351217629)
    ·
      refine ⟨39477383088405116381706611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105273021569080310351217629 39477383088405116381706611)
      ·
        refine ⟨59216074632607674572559917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39477383088405116381706611 59216074632607674572559917)
        ·
          refine ⟨22206027987227877964709969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59216074632607674572559917 22206027987227877964709969)
          ·
            refine ⟨16654520990420908473532477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22206027987227877964709969 16654520990420908473532477)
            ·
              refine ⟨6245445371407840677574679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16654520990420908473532477 6245445371407840677574679)
              ·
                refine ⟨9368168057111761016362019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245445371407840677574679 9368168057111761016362019)
                ·
                  refine ⟨14052252085667641524543029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368168057111761016362019 14052252085667641524543029)
                  ·
                    refine ⟨1317398633031341392925909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14052252085667641524543029 1317398633031341392925909)
                    ·
                      rfl

theorem cell23_7696874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_7696874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696874 prefixEnd_7696874 := by exact prefixLift 7696874
  have htrace : WordTrace (prefixWord ++ tailWord_7696874) baseStart_7696874 baseEnd_7696874 := by
    simpa [prefixWord, tailWord_7696874, baseEnd_7696874] using wordTrace_append hprefix tailTrace_7696874
  have hstable : (prefixWord ++ tailWord_7696874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696874).length < 2 ^ (prefixWord ++ tailWord_7696874).sum := by decide
  have hdescent : baseEnd_7696874 < baseStart_7696874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696897 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_7696897 : Nat := 118140960795 + 7696897 * 2 ^ 59
def prefixEnd_7696897 : Nat := 4983230072969 + 3 ^ 40 * 7696897 * 2
def baseEnd_7696897 : Nat := 3952207709149077588790121

theorem tailTrace_7696897 : CollatzResearch.WordTrace tailWord_7696897 prefixEnd_7696897 3952207709149077588790121 := by
  unfold tailWord_7696897
  simp only [CollatzResearch.WordTrace]
  refine ⟨280728896396464169198000945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187152597597642779465333963 280728896396464169198000945)
  ·
    refine ⟨210546672297348126898500709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280728896396464169198000945 210546672297348126898500709)
    ·
      refine ⟨39477501055752773793468883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210546672297348126898500709 39477501055752773793468883)
      ·
        refine ⟨59216251583629160690203325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39477501055752773793468883 59216251583629160690203325)
        ·
          refine ⟨22206094343860935258826247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59216251583629160690203325 22206094343860935258826247)
          ·
            refine ⟨33309141515791402888239371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22206094343860935258826247 33309141515791402888239371)
            ·
              refine ⟨49963712273687104332359057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33309141515791402888239371 49963712273687104332359057)
              ·
                refine ⟨37472784205265328249269293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49963712273687104332359057 37472784205265328249269293)
                ·
                  refine ⟨14052294076974498093475985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37472784205265328249269293 14052294076974498093475985)
                  ·
                    refine ⟨10539220557730873570106989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14052294076974498093475985 10539220557730873570106989)
                    ·
                      refine ⟨3952207709149077588790121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539220557730873570106989 3952207709149077588790121)
                      ·
                        rfl

theorem cell23_7696897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_7696897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696897 prefixEnd_7696897 := by exact prefixLift 7696897
  have htrace : WordTrace (prefixWord ++ tailWord_7696897) baseStart_7696897 baseEnd_7696897 := by
    simpa [prefixWord, tailWord_7696897, baseEnd_7696897] using wordTrace_append hprefix tailTrace_7696897
  have hstable : (prefixWord ++ tailWord_7696897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696897).length < 2 ^ (prefixWord ++ tailWord_7696897).sum := by decide
  have hdescent : baseEnd_7696897 < baseStart_7696897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696907 : List Nat := [1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 4]
def baseStart_7696907 : Nat := 118140960795 + 7696907 * 2 ^ 59
def prefixEnd_7696907 : Nat := 4983230072969 + 3 ^ 40 * 7696907 * 2
def baseEnd_7696907 : Nat := 3952212843955622549665075

theorem tailTrace_7696907 : CollatzResearch.WordTrace tailWord_7696907 prefixEnd_7696907 3952212843955622549665075 := by
  unfold tailWord_7696907
  simp only [CollatzResearch.WordTrace]
  refine ⟨280729261126427940905864975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187152840750951960603909983 280729261126427940905864975)
  ·
    refine ⟨421093891689641911358797463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280729261126427940905864975 421093891689641911358797463)
    ·
      refine ⟨631640837534462867038196195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421093891689641911358797463 631640837534462867038196195)
      ·
        refine ⟨947461256301694300557294293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631640837534462867038196195 947461256301694300557294293)
        ·
          refine ⟨22206123194570960169311585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 947461256301694300557294293 22206123194570960169311585)
          ·
            refine ⟨16654592395928220126983689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22206123194570960169311585 16654592395928220126983689)
            ·
              refine ⟨12490944296946165095237767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16654592395928220126983689 12490944296946165095237767)
              ·
                refine ⟨18736416445419247642856651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12490944296946165095237767 18736416445419247642856651)
                ·
                  refine ⟨28104624668128871464284977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18736416445419247642856651 28104624668128871464284977)
                  ·
                    refine ⟨21078468501096653598213733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28104624668128871464284977 21078468501096653598213733)
                    ·
                      refine ⟨3952212843955622549665075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21078468501096653598213733 3952212843955622549665075)
                      ·
                        rfl

theorem cell23_7696907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 2, 4].length) (baseStart_7696907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696907 prefixEnd_7696907 := by exact prefixLift 7696907
  have htrace : WordTrace (prefixWord ++ tailWord_7696907) baseStart_7696907 baseEnd_7696907 := by
    simpa [prefixWord, tailWord_7696907, baseEnd_7696907] using wordTrace_append hprefix tailTrace_7696907
  have hstable : (prefixWord ++ tailWord_7696907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696907).length < 2 ^ (prefixWord ++ tailWord_7696907).sum := by decide
  have hdescent : baseEnd_7696907 < baseStart_7696907 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696927 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 3]
def baseStart_7696927 : Nat := 118140960795 + 7696927 * 2 ^ 59
def prefixEnd_7696927 : Nat := 4983230072969 + 3 ^ 40 * 7696927 * 2
def baseEnd_7696927 : Nat := 3952223113568712471414983

theorem tailTrace_7696927 : CollatzResearch.WordTrace tailWord_7696927 prefixEnd_7696927 3952223113568712471414983 := by
  unfold tailWord_7696927
  simp only [CollatzResearch.WordTrace]
  refine ⟨280729990586355484321593035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187153327057570322881062023 280729990586355484321593035)
  ·
    refine ⟨421094985879533226482389553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280729990586355484321593035 421094985879533226482389553)
    ·
      refine ⟨315821239409649919861792165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421094985879533226482389553 315821239409649919861792165)
      ·
        refine ⟨59216482389309359974086031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315821239409649919861792165 59216482389309359974086031)
        ·
          refine ⟨88824723583964039961129047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59216482389309359974086031 88824723583964039961129047)
          ·
            refine ⟨133237085375946059941693571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88824723583964039961129047 133237085375946059941693571)
            ·
              refine ⟨199855628063919089912540357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133237085375946059941693571 199855628063919089912540357)
              ·
                refine ⟨37472930261984829358601317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199855628063919089912540357 37472930261984829358601317)
                ·
                  refine ⟨7026174424122155504737747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37472930261984829358601317 7026174424122155504737747)
                  ·
                    refine ⟨10539261636183233257106621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026174424122155504737747 10539261636183233257106621)
                    ·
                      refine ⟨3952223113568712471414983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539261636183233257106621 3952223113568712471414983)
                      ·
                        rfl

theorem cell23_7696927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_7696927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696927 prefixEnd_7696927 := by exact prefixLift 7696927
  have htrace : WordTrace (prefixWord ++ tailWord_7696927) baseStart_7696927 baseEnd_7696927 := by
    simpa [prefixWord, tailWord_7696927, baseEnd_7696927] using wordTrace_append hprefix tailTrace_7696927
  have hstable : (prefixWord ++ tailWord_7696927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696927).length < 2 ^ (prefixWord ++ tailWord_7696927).sum := by decide
  have hdescent : baseEnd_7696927 < baseStart_7696927 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696928 : List Nat := [2, 1, 1, 6, 3, 1, 2, 1, 1, 1, 4]
def baseStart_7696928 : Nat := 118140960795 + 7696928 * 2 ^ 59
def prefixEnd_7696928 : Nat := 4983230072969 + 3 ^ 40 * 7696928 * 2
def baseEnd_7696928 : Nat := 3952223627049366967502479

theorem tailTrace_7696928 : CollatzResearch.WordTrace tailWord_7696928 prefixEnd_7696928 3952223627049366967502479 := by
  unfold tailWord_7696928
  simp only [CollatzResearch.WordTrace]
  refine ⟨140365013529675930746189719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187153351372901240994919625 140365013529675930746189719)
  ·
    refine ⟨210547520294513896119284579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140365013529675930746189719 210547520294513896119284579)
    ·
      refine ⟨315821280441770844178926869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210547520294513896119284579 315821280441770844178926869)
      ·
        refine ⟨14804122520708008320887197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 315821280441770844178926869 14804122520708008320887197)
        ·
          refine ⟨5551545945265503120332699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14804122520708008320887197 5551545945265503120332699)
          ·
            refine ⟨8327318917898254680499049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551545945265503120332699 8327318917898254680499049)
            ·
              refine ⟨6245489188423691010374287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327318917898254680499049 6245489188423691010374287)
              ·
                refine ⟨9368233782635536515561431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245489188423691010374287 9368233782635536515561431)
                ·
                  refine ⟨14052350673953304773342147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368233782635536515561431 14052350673953304773342147)
                  ·
                    refine ⟨21078526010929957160013221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14052350673953304773342147 21078526010929957160013221)
                    ·
                      refine ⟨3952223627049366967502479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21078526010929957160013221 3952223627049366967502479)
                      ·
                        rfl

theorem cell23_7696928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_7696928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696928 prefixEnd_7696928 := by exact prefixLift 7696928
  have htrace : WordTrace (prefixWord ++ tailWord_7696928) baseStart_7696928 baseEnd_7696928 := by
    simpa [prefixWord, tailWord_7696928, baseEnd_7696928] using wordTrace_append hprefix tailTrace_7696928
  have hstable : (prefixWord ++ tailWord_7696928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696928).length < 2 ^ (prefixWord ++ tailWord_7696928).sum := by decide
  have hdescent : baseEnd_7696928 < baseStart_7696928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696931 : List Nat := [1, 1, 1, 4, 4, 3, 2, 1, 1, 2, 3]
def baseStart_7696931 : Nat := 118140960795 + 7696931 * 2 ^ 59
def prefixEnd_7696931 : Nat := 4983230072969 + 3 ^ 40 * 7696931 * 2
def baseEnd_7696931 : Nat := 3952225167491330455764965

theorem tailTrace_7696931 : CollatzResearch.WordTrace tailWord_7696931 prefixEnd_7696931 3952225167491330455764965 := by
  unfold tailWord_7696931
  simp only [CollatzResearch.WordTrace]
  refine ⟨280730136478340993004738647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187153424318893995336492431 280730136478340993004738647)
  ·
    refine ⟨421095204717511489507107971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280730136478340993004738647 421095204717511489507107971)
    ·
      refine ⟨631642807076267234260661957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421095204717511489507107971 631642807076267234260661957)
      ·
        refine ⟨118433026326800106423874117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 631642807076267234260661957 118433026326800106423874117)
        ·
          refine ⟨22206192436275019954476397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118433026326800106423874117 22206192436275019954476397)
          ·
            refine ⟨8327322163603132482928649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22206192436275019954476397 8327322163603132482928649)
            ·
              refine ⟨6245491622702349362196487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327322163603132482928649 6245491622702349362196487)
              ·
                refine ⟨9368237434053524043294731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245491622702349362196487 9368237434053524043294731)
                ·
                  refine ⟨14052356151080286064942097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368237434053524043294731 14052356151080286064942097)
                  ·
                    refine ⟨10539267113310214548706573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14052356151080286064942097 10539267113310214548706573)
                    ·
                      refine ⟨3952225167491330455764965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539267113310214548706573 3952225167491330455764965)
                      ·
                        rfl

theorem cell23_7696931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 2, 1, 1, 2, 3].length) (baseStart_7696931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696931 prefixEnd_7696931 := by exact prefixLift 7696931
  have htrace : WordTrace (prefixWord ++ tailWord_7696931) baseStart_7696931 baseEnd_7696931 := by
    simpa [prefixWord, tailWord_7696931, baseEnd_7696931] using wordTrace_append hprefix tailTrace_7696931
  have hstable : (prefixWord ++ tailWord_7696931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696931).length < 2 ^ (prefixWord ++ tailWord_7696931).sum := by decide
  have hdescent : baseEnd_7696931 < baseStart_7696931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696944 : List Nat := [2, 1, 1, 1, 2, 3, 5, 2, 2, 1, 3]
def baseStart_7696944 : Nat := 118140960795 + 7696944 * 2 ^ 59
def prefixEnd_7696944 : Nat := 4983230072969 + 3 ^ 40 * 7696944 * 2
def baseEnd_7696944 : Nat := 3952231842739838904902405

theorem tailTrace_7696944 : CollatzResearch.WordTrace tailWord_7696944 prefixEnd_7696944 3952231842739838904902405 := by
  unfold tailWord_7696944
  simp only [CollatzResearch.WordTrace]
  refine ⟨140365305313646948112480943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187153740418195930816641257 140365305313646948112480943)
  ·
    refine ⟨210547957970470422168721415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140365305313646948112480943 210547957970470422168721415)
    ·
      refine ⟨315821936955705633253082123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210547957970470422168721415 315821936955705633253082123)
      ·
        refine ⟨473732905433558449879623185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315821936955705633253082123 473732905433558449879623185)
        ·
          refine ⟨355299679075168837409717389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473732905433558449879623185 355299679075168837409717389)
          ·
            refine ⟨133237379653188314028644021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 355299679075168837409717389 133237379653188314028644021)
            ·
              refine ⟨12491004342486404440185377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133237379653188314028644021 12491004342486404440185377)
              ·
                refine ⟨9368253256864803330139033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12491004342486404440185377 9368253256864803330139033)
                ·
                  refine ⟨7026189942648602497604275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9368253256864803330139033 7026189942648602497604275)
                  ·
                    refine ⟨10539284913972903746406413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026189942648602497604275 10539284913972903746406413)
                    ·
                      refine ⟨3952231842739838904902405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539284913972903746406413 3952231842739838904902405)
                      ·
                        rfl

theorem cell23_7696944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 2, 2, 1, 3].length) (baseStart_7696944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696944 prefixEnd_7696944 := by exact prefixLift 7696944
  have htrace : WordTrace (prefixWord ++ tailWord_7696944) baseStart_7696944 baseEnd_7696944 := by
    simpa [prefixWord, tailWord_7696944, baseEnd_7696944] using wordTrace_append hprefix tailTrace_7696944
  have hstable : (prefixWord ++ tailWord_7696944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696944).length < 2 ^ (prefixWord ++ tailWord_7696944).sum := by decide
  have hdescent : baseEnd_7696944 < baseStart_7696944 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696958 : List Nat := [4, 2, 1, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_7696958 : Nat := 118140960795 + 7696958 * 2 ^ 59
def prefixEnd_7696958 : Nat := 4983230072969 + 3 ^ 40 * 7696958 * 2
def baseEnd_7696958 : Nat := 3952239031469001850127341

theorem tailTrace_7696958 : CollatzResearch.WordTrace tailWord_7696958 prefixEnd_7696958 3952239031469001850127341 := by
  unfold tailWord_7696958
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091390156155397076996441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187154080832828784410647685 35091390156155397076996441)
  ·
    refine ⟨26318542617116547807747331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35091390156155397076996441 26318542617116547807747331)
    ·
      refine ⟨39477813925674821711620997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26318542617116547807747331 39477813925674821711620997)
      ·
        refine ⟨7402090111064029070928937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39477813925674821711620997 7402090111064029070928937)
        ·
          refine ⟨5551567583298021803196703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7402090111064029070928937 5551567583298021803196703)
          ·
            refine ⟨8327351374947032704795055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551567583298021803196703 8327351374947032704795055)
            ·
              refine ⟨12491027062420549057192583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8327351374947032704795055 12491027062420549057192583)
              ·
                refine ⟨18736540593630823585788875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12491027062420549057192583 18736540593630823585788875)
                ·
                  refine ⟨28104810890446235378683313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18736540593630823585788875 28104810890446235378683313)
                  ·
                    refine ⟨21078608167834676534012485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28104810890446235378683313 21078608167834676534012485)
                    ·
                      refine ⟨3952239031469001850127341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21078608167834676534012485 3952239031469001850127341)
                      ·
                        rfl

theorem cell23_7696958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_7696958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696958 prefixEnd_7696958 := by exact prefixLift 7696958
  have htrace : WordTrace (prefixWord ++ tailWord_7696958) baseStart_7696958 baseEnd_7696958 := by
    simpa [prefixWord, tailWord_7696958, baseEnd_7696958] using wordTrace_append hprefix tailTrace_7696958
  have hstable : (prefixWord ++ tailWord_7696958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696958).length < 2 ^ (prefixWord ++ tailWord_7696958).sum := by decide
  have hdescent : baseEnd_7696958 < baseStart_7696958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696960 : List Nat := [2, 1, 1, 2, 2, 2, 4, 1, 2, 6]
def baseStart_7696960 : Nat := 118140960795 + 7696960 * 2 ^ 59
def prefixEnd_7696960 : Nat := 4983230072969 + 3 ^ 40 * 7696960 * 2
def baseEnd_7696960 : Nat := 1317413352810103614100777

theorem tailTrace_7696960 : CollatzResearch.WordTrace tailWord_7696960 prefixEnd_7696960 1317413352810103614100777 := by
  unfold tailWord_7696960
  simp only [CollatzResearch.WordTrace]
  refine ⟨140365597097617965478772167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187154129463490620638362889 140365597097617965478772167)
  ·
    refine ⟨210548395646426948218158251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140365597097617965478772167 210548395646426948218158251)
    ·
      refine ⟨315822593469640422327237377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210548395646426948218158251 315822593469640422327237377)
      ·
        refine ⟨236866945102230316745428033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315822593469640422327237377 236866945102230316745428033)
        ·
          refine ⟨177650208826672737559071025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236866945102230316745428033 177650208826672737559071025)
          ·
            refine ⟨133237656620004553169303269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177650208826672737559071025 133237656620004553169303269)
            ·
              refine ⟨24982060616250853719244363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133237656620004553169303269 24982060616250853719244363)
              ·
                refine ⟨37473090924376280578866545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24982060616250853719244363 37473090924376280578866545)
                ·
                  refine ⟨28104818193282210434149909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37473090924376280578866545 28104818193282210434149909)
                  ·
                    refine ⟨1317413352810103614100777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28104818193282210434149909 1317413352810103614100777)
                    ·
                      rfl

theorem cell23_7696960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 1, 2, 6].length) (baseStart_7696960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696960 prefixEnd_7696960 := by exact prefixLift 7696960
  have htrace : WordTrace (prefixWord ++ tailWord_7696960) baseStart_7696960 baseEnd_7696960 := by
    simpa [prefixWord, tailWord_7696960, baseEnd_7696960] using wordTrace_append hprefix tailTrace_7696960
  have hstable : (prefixWord ++ tailWord_7696960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696960).length < 2 ^ (prefixWord ++ tailWord_7696960).sum := by decide
  have hdescent : baseEnd_7696960 < baseStart_7696960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7696984 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 4, 2, 2]
def baseStart_7696984 : Nat := 118140960795 + 7696984 * 2 ^ 59
def prefixEnd_7696984 : Nat := 4983230072969 + 3 ^ 40 * 7696984 * 2
def baseEnd_7696984 : Nat := 3952252381966018748402221

theorem tailTrace_7696984 : CollatzResearch.WordTrace tailWord_7696984 prefixEnd_7696984 3952252381966018748402221 := by
  unfold tailWord_7696984
  simp only [CollatzResearch.WordTrace]
  refine ⟨140366034773574491528209003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187154713031432655370945337 140366034773574491528209003)
  ·
    refine ⟨210549052160361737292313505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140366034773574491528209003 210549052160361737292313505)
    ·
      refine ⟨157911789120271302969235129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210549052160361737292313505 157911789120271302969235129)
      ·
        refine ⟨118433841840203477226926347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157911789120271302969235129 118433841840203477226926347)
        ·
          refine ⟨177650762760305215840389521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118433841840203477226926347 177650762760305215840389521)
          ·
            refine ⟨133238072070228911880292141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177650762760305215840389521 133238072070228911880292141)
            ·
              refine ⟨49964277026335841955109553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 133238072070228911880292141 49964277026335841955109553)
              ·
                refine ⟨37473207769751881466332165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49964277026335841955109553 37473207769751881466332165)
                ·
                  refine ⟨7026226456828477774937281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37473207769751881466332165 7026226456828477774937281)
                  ·
                    refine ⟨5269669842621358331202961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7026226456828477774937281 5269669842621358331202961)
                    ·
                      refine ⟨3952252381966018748402221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269669842621358331202961 3952252381966018748402221)
                      ·
                        rfl

theorem cell23_7696984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 4, 2, 2].length) (baseStart_7696984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7696984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7696984 prefixEnd_7696984 := by exact prefixLift 7696984
  have htrace : WordTrace (prefixWord ++ tailWord_7696984) baseStart_7696984 baseEnd_7696984 := by
    simpa [prefixWord, tailWord_7696984, baseEnd_7696984] using wordTrace_append hprefix tailTrace_7696984
  have hstable : (prefixWord ++ tailWord_7696984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7696984).length < 2 ^ (prefixWord ++ tailWord_7696984).sum := by decide
  have hdescent : baseEnd_7696984 < baseStart_7696984 := by decide
  rcases family_descends (prefixWord ++ tailWord_7696984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697007 : List Nat := [1, 1, 2, 1, 3, 2, 2, 6, 5]
def baseStart_7697007 : Nat := 118140960795 + 7697007 * 2 ^ 59
def prefixEnd_7697007 : Nat := 4983230072969 + 3 ^ 40 * 7697007 * 2
def baseEnd_7697007 : Nat := 439140465780119128712735

theorem tailTrace_7697007 : CollatzResearch.WordTrace tailWord_7697007 prefixEnd_7697007 439140465780119128712735 := by
  unfold tailWord_7697007
  simp only [CollatzResearch.WordTrace]
  refine ⟨280732908426065657984505275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187155272284043771989670183 280732908426065657984505275)
  ·
    refine ⟨421099362639098486976757913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280732908426065657984505275 421099362639098486976757913)
    ·
      refine ⟨315824521979323865232568435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421099362639098486976757913 315824521979323865232568435)
      ·
        refine ⟨473736782968985797848852653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315824521979323865232568435 473736782968985797848852653)
        ·
          refine ⟨177651293613369674193319745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473736782968985797848852653 177651293613369674193319745)
          ·
            refine ⟨133238470210027255644989809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177651293613369674193319745 133238470210027255644989809)
            ·
              refine ⟨99928852657520441733742357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133238470210027255644989809 99928852657520441733742357)
              ·
                refine ⟨4684164968321270706269173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99928852657520441733742357 4684164968321270706269173)
                ·
                  refine ⟨439140465780119128712735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4684164968321270706269173 439140465780119128712735)
                  ·
                    rfl

theorem cell23_7697007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 5].length) (baseStart_7697007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697007 prefixEnd_7697007 := by exact prefixLift 7697007
  have htrace : WordTrace (prefixWord ++ tailWord_7697007) baseStart_7697007 baseEnd_7697007 := by
    simpa [prefixWord, tailWord_7697007, baseEnd_7697007] using wordTrace_append hprefix tailTrace_7697007
  have hstable : (prefixWord ++ tailWord_7697007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697007).length < 2 ^ (prefixWord ++ tailWord_7697007).sum := by decide
  have hdescent : baseEnd_7697007 < baseStart_7697007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697020 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 3, 7]
def baseStart_7697020 : Nat := 118140960795 + 7697020 * 2 ^ 59
def prefixEnd_7697020 : Nat := 4983230072969 + 3 ^ 40 * 7697020 * 2
def baseEnd_7697020 : Nat := 1317423622423193535850685

theorem tailTrace_7697020 : CollatzResearch.WordTrace tailWord_7697020 prefixEnd_7697020 1317423622423193535850685 := by
  unfold tailWord_7697020
  simp only [CollatzResearch.WordTrace]
  refine ⟨140366691287509280602364257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187155588383345707469819009 140366691287509280602364257)
  ·
    refine ⟨105275018465631960451773193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140366691287509280602364257 105275018465631960451773193)
    ·
      refine ⟨78956263849223970338829895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105275018465631960451773193 78956263849223970338829895)
      ·
        refine ⟨118434395773835955508244843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78956263849223970338829895 118434395773835955508244843)
        ·
          refine ⟨177651593660753933262367265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118434395773835955508244843 177651593660753933262367265)
          ·
            refine ⟨133238695245565449946775449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177651593660753933262367265 133238695245565449946775449)
            ·
              refine ⟨99929021434174087460081587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133238695245565449946775449 99929021434174087460081587)
              ·
                refine ⟨149893532151261131190122381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99929021434174087460081587 149893532151261131190122381)
                ·
                  refine ⟨56210074556722924196295893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149893532151261131190122381 56210074556722924196295893)
                  ·
                    refine ⟨1317423622423193535850685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56210074556722924196295893 1317423622423193535850685)
                    ·
                      rfl

theorem cell23_7697020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_7697020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697020 prefixEnd_7697020 := by exact prefixLift 7697020
  have htrace : WordTrace (prefixWord ++ tailWord_7697020) baseStart_7697020 baseEnd_7697020 := by
    simpa [prefixWord, tailWord_7697020, baseEnd_7697020] using wordTrace_append hprefix tailTrace_7697020
  have hstable : (prefixWord ++ tailWord_7697020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697020).length < 2 ^ (prefixWord ++ tailWord_7697020).sum := by decide
  have hdescent : baseEnd_7697020 < baseStart_7697020 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697054 : List Nat := [4, 3, 1, 1, 1, 1, 1, 4, 2, 5]
def baseStart_7697054 : Nat := 118140960795 + 7697054 * 2 ^ 59
def prefixEnd_7697054 : Nat := 4983230072969 + 3 ^ 40 * 7697054 * 2
def baseEnd_7697054 : Nat := 1317429441870611158175633

theorem tailTrace_7697054 : CollatzResearch.WordTrace tailWord_7697054 prefixEnd_7697054 1317429441870611158175633 := by
  unfold tailWord_7697054
  simp only [CollatzResearch.WordTrace]
  refine ⟨35091827832111923126433277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187156415104596923340977477 35091827832111923126433277)
  ·
    refine ⟨13159435437041971172412479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35091827832111923126433277 13159435437041971172412479)
    ·
      refine ⟨19739153155562956758618719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13159435437041971172412479 19739153155562956758618719)
      ·
        refine ⟨29608729733344435137928079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19739153155562956758618719 29608729733344435137928079)
        ·
          refine ⟨44413094600016652706892119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29608729733344435137928079 44413094600016652706892119)
          ·
            refine ⟨66619641900024979060338179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44413094600016652706892119 66619641900024979060338179)
            ·
              refine ⟨99929462850037468590507269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66619641900024979060338179 99929462850037468590507269)
              ·
                refine ⟨18736774284382025360720113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99929462850037468590507269 18736774284382025360720113)
                ·
                  refine ⟨14052580713286519020540085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18736774284382025360720113 14052580713286519020540085)
                  ·
                    refine ⟨1317429441870611158175633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14052580713286519020540085 1317429441870611158175633)
                    ·
                      rfl

theorem cell23_7697054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_7697054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697054 prefixEnd_7697054 := by exact prefixLift 7697054
  have htrace : WordTrace (prefixWord ++ tailWord_7697054) baseStart_7697054 baseEnd_7697054 := by
    simpa [prefixWord, tailWord_7697054, baseEnd_7697054] using wordTrace_append hprefix tailTrace_7697054
  have hstable : (prefixWord ++ tailWord_7697054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697054).length < 2 ^ (prefixWord ++ tailWord_7697054).sum := by decide
  have hdescent : baseEnd_7697054 < baseStart_7697054 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697080 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 12]
def baseStart_7697080 : Nat := 118140960795 + 7697080 * 2 ^ 59
def prefixEnd_7697080 : Nat := 4983230072969 + 3 ^ 40 * 7697080 * 2
def baseEnd_7697080 : Nat := 439144630678761152533531

theorem tailTrace_7697080 : CollatzResearch.WordTrace tailWord_7697080 prefixEnd_7697080 439144630678761152533531 := by
  unfold tailWord_7697080
  simp only [CollatzResearch.WordTrace]
  refine ⟨140367785477400595725956347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187157047303200794301275129 140367785477400595725956347)
  ·
    refine ⟨210551678216100893588934521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140367785477400595725956347 210551678216100893588934521)
    ·
      refine ⟨157913758662075670191700891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210551678216100893588934521 157913758662075670191700891)
      ·
        refine ⟨236870637993113505287551337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157913758662075670191700891 236870637993113505287551337)
        ·
          refine ⟨177652978494835128965663503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236870637993113505287551337 177652978494835128965663503)
          ·
            refine ⟨266479467742252693448495255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177652978494835128965663503 266479467742252693448495255)
            ·
              refine ⟨399719201613379040172742883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266479467742252693448495255 399719201613379040172742883)
              ·
                refine ⟨599578802420068560259114325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399719201613379040172742883 599578802420068560259114325)
                ·
                  refine ⟨439144630678761152533531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 599578802420068560259114325 439144630678761152533531)
                  ·
                    rfl

theorem cell23_7697080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 12].length) (baseStart_7697080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697080 prefixEnd_7697080 := by exact prefixLift 7697080
  have htrace : WordTrace (prefixWord ++ tailWord_7697080) baseStart_7697080 baseEnd_7697080 := by
    simpa [prefixWord, tailWord_7697080, baseEnd_7697080] using wordTrace_append hprefix tailTrace_7697080
  have hstable : (prefixWord ++ tailWord_7697080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697080).length < 2 ^ (prefixWord ++ tailWord_7697080).sum := by decide
  have hdescent : baseEnd_7697080 < baseStart_7697080 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697084 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 3, 4]
def baseStart_7697084 : Nat := 118140960795 + 7697084 * 2 ^ 59
def prefixEnd_7697084 : Nat := 4983230072969 + 3 ^ 40 * 7697084 * 2
def baseEnd_7697084 : Nat := 1317434576677156119050587

theorem tailTrace_7697084 : CollatzResearch.WordTrace tailWord_7697084 prefixEnd_7697084 1317434576677156119050587 := by
  unfold tailWord_7697084
  simp only [CollatzResearch.WordTrace]
  refine ⟨140367858423393350067529153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187157144564524466756705537 140367858423393350067529153)
  ·
    refine ⟨105275893817545012550646865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140367858423393350067529153 105275893817545012550646865)
    ·
      refine ⟨78956920363158759412985149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105275893817545012550646865 78956920363158759412985149)
      ·
        refine ⟨29608845136184534779869431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78956920363158759412985149 29608845136184534779869431)
        ·
          refine ⟨44413267704276802169804147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29608845136184534779869431 44413267704276802169804147)
          ·
            refine ⟨66619901556415203254706221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44413267704276802169804147 66619901556415203254706221)
            ·
              refine ⟨24982463083655701220514833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66619901556415203254706221 24982463083655701220514833)
              ·
                refine ⟨18736847312741775915386125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24982463083655701220514833 18736847312741775915386125)
                ·
                  refine ⟨7026317742278165968269797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18736847312741775915386125 7026317742278165968269797)
                  ·
                    refine ⟨1317434576677156119050587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026317742278165968269797 1317434576677156119050587)
                    ·
                      rfl

theorem cell23_7697084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_7697084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697084 prefixEnd_7697084 := by exact prefixLift 7697084
  have htrace : WordTrace (prefixWord ++ tailWord_7697084) baseStart_7697084 baseEnd_7697084 := by
    simpa [prefixWord, tailWord_7697084, baseEnd_7697084] using wordTrace_append hprefix tailTrace_7697084
  have hstable : (prefixWord ++ tailWord_7697084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697084).length < 2 ^ (prefixWord ++ tailWord_7697084).sum := by decide
  have hdescent : baseEnd_7697084 < baseStart_7697084 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697144 : List Nat := [2, 1, 2, 1, 1, 2, 6, 2, 1, 5]
def baseStart_7697144 : Nat := 118140960795 + 7697144 * 2 ^ 59
def prefixEnd_7697144 : Nat := 4983230072969 + 3 ^ 40 * 7697144 * 2
def baseEnd_7697144 : Nat := 1317444846290246040800495

theorem tailTrace_7697144 : CollatzResearch.WordTrace tailWord_7697144 prefixEnd_7697144 1317444846290246040800495 := by
  unfold tailWord_7697144
  simp only [CollatzResearch.WordTrace]
  refine ⟨140368952613284665191121243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187158603484379553588161657 140368952613284665191121243)
  ·
    refine ⟨210553428919926997786681865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140368952613284665191121243 210553428919926997786681865)
    ·
      refine ⟨157915071689945248340011399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210553428919926997786681865 157915071689945248340011399)
      ·
        refine ⟨236872607534917872510017099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157915071689945248340011399 236872607534917872510017099)
        ·
          refine ⟨355308911302376808765025649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236872607534917872510017099 355308911302376808765025649)
          ·
            refine ⟨266481683476782606573769237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355308911302376808765025649 266481683476782606573769237)
            ·
              refine ⟨12491328912974184683145433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 266481683476782606573769237 12491328912974184683145433)
              ·
                refine ⟨9368496684730638512359075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12491328912974184683145433 9368496684730638512359075)
                ·
                  refine ⟨14052745027095957768538613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368496684730638512359075 14052745027095957768538613)
                  ·
                    refine ⟨1317444846290246040800495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14052745027095957768538613 1317444846290246040800495)
                    ·
                      rfl

theorem cell23_7697144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 2, 1, 5].length) (baseStart_7697144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697144 prefixEnd_7697144 := by exact prefixLift 7697144
  have htrace : WordTrace (prefixWord ++ tailWord_7697144) baseStart_7697144 baseEnd_7697144 := by
    simpa [prefixWord, tailWord_7697144, baseEnd_7697144] using wordTrace_append hprefix tailTrace_7697144
  have hstable : (prefixWord ++ tailWord_7697144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697144).length < 2 ^ (prefixWord ++ tailWord_7697144).sum := by decide
  have hdescent : baseEnd_7697144 < baseStart_7697144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697147 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 4]
def baseStart_7697147 : Nat := 118140960795 + 7697147 * 2 ^ 59
def prefixEnd_7697147 : Nat := 4983230072969 + 3 ^ 40 * 7697147 * 2
def baseEnd_7697147 : Nat := 3952336079312701610663971

theorem tailTrace_7697147 : CollatzResearch.WordTrace tailWord_7697147 prefixEnd_7697147 3952336079312701610663971 := by
  unfold tailWord_7697147
  simp only [CollatzResearch.WordTrace]
  refine ⟨280738014645558461894601695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187158676430372307929734463 280738014645558461894601695)
  ·
    refine ⟨421107021968337692841902543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280738014645558461894601695 421107021968337692841902543)
    ·
      refine ⟨631660532952506539262853815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421107021968337692841902543 631660532952506539262853815)
      ·
        refine ⟨947490799428759808894280723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631660532952506539262853815 947490799428759808894280723)
        ·
          refine ⟨1421236199143139713341421085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947490799428759808894280723 1421236199143139713341421085)
          ·
            refine ⟨532963574678677392503032907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1421236199143139713341421085 532963574678677392503032907)
            ·
              refine ⟨799445362018016088754549361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532963574678677392503032907 799445362018016088754549361)
              ·
                refine ⟨599584021513512066565912021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 799445362018016088754549361 599584021513512066565912021)
                ·
                  refine ⟨14052750504222939060138563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 599584021513512066565912021 14052750504222939060138563)
                  ·
                    refine ⟨21079125756334408590207845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14052750504222939060138563 21079125756334408590207845)
                    ·
                      refine ⟨3952336079312701610663971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21079125756334408590207845 3952336079312701610663971)
                      ·
                        rfl

theorem cell23_7697147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 7, 1, 4].length) (baseStart_7697147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697147 prefixEnd_7697147 := by exact prefixLift 7697147
  have htrace : WordTrace (prefixWord ++ tailWord_7697147) baseStart_7697147 baseEnd_7697147 := by
    simpa [prefixWord, tailWord_7697147, baseEnd_7697147] using wordTrace_append hprefix tailTrace_7697147
  have hstable : (prefixWord ++ tailWord_7697147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697147).length < 2 ^ (prefixWord ++ tailWord_7697147).sum := by decide
  have hdescent : baseEnd_7697147 < baseStart_7697147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697157 : List Nat := [1, 3, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_7697157 : Nat := 118140960795 + 7697157 * 2 ^ 59
def prefixEnd_7697157 : Nat := 4983230072969 + 3 ^ 40 * 7697157 * 2
def baseEnd_7697157 : Nat := 1317447071373082190512975

theorem tailTrace_7697157 : CollatzResearch.WordTrace tailWord_7697157 prefixEnd_7697157 1317447071373082190512975 := by
  unfold tailWord_7697157
  simp only [CollatzResearch.WordTrace]
  refine ⟨280738379375522233602465725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187158919583681489068310483 280738379375522233602465725)
  ·
    refine ⟨105276892265820837600924647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280738379375522233602465725 105276892265820837600924647)
    ·
      refine ⟨157915338398731256401386971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105276892265820837600924647 157915338398731256401386971)
      ·
        refine ⟨236873007598096884602080457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157915338398731256401386971 236873007598096884602080457)
        ·
          refine ⟨177654755698572663451560343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236873007598096884602080457 177654755698572663451560343)
          ·
            refine ⟨266482133547858995177340515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177654755698572663451560343 266482133547858995177340515)
            ·
              refine ⟨399723200321788492766010773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266482133547858995177340515 399723200321788492766010773)
              ·
                refine ⟨18737025015083835598406755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 399723200321788492766010773 18737025015083835598406755)
                ·
                  refine ⟨28105537522625753397610133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18737025015083835598406755 28105537522625753397610133)
                  ·
                    refine ⟨1317447071373082190512975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28105537522625753397610133 1317447071373082190512975)
                    ·
                      rfl

theorem cell23_7697157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_7697157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697157 prefixEnd_7697157 := by exact prefixLift 7697157
  have htrace : WordTrace (prefixWord ++ tailWord_7697157) baseStart_7697157 baseEnd_7697157 := by
    simpa [prefixWord, tailWord_7697157, baseEnd_7697157] using wordTrace_append hprefix tailTrace_7697157
  have hstable : (prefixWord ++ tailWord_7697157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697157).length < 2 ^ (prefixWord ++ tailWord_7697157).sum := by decide
  have hdescent : baseEnd_7697157 < baseStart_7697157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697175 : List Nat := [1, 1, 3, 4, 4, 1, 1, 1, 3, 1, 3]
def baseStart_7697175 : Nat := 118140960795 + 7697175 * 2 ^ 59
def prefixEnd_7697175 : Nat := 4983230072969 + 3 ^ 40 * 7697175 * 2
def baseEnd_7697175 : Nat := 3952350456771027501113843

theorem tailTrace_7697175 : CollatzResearch.WordTrace tailWord_7697175 prefixEnd_7697175 3952350456771027501113843 := by
  unfold tailWord_7697175
  simp only [CollatzResearch.WordTrace]
  refine ⟨280739035889457022676620979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187159357259638015117747319 280739035889457022676620979)
  ·
    refine ⟨421108553834185534014931469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280739035889457022676620979 421108553834185534014931469)
    ·
      refine ⟨157915707687819575255599301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421108553834185534014931469 157915707687819575255599301)
      ·
        refine ⟨29609195191466170360424869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157915707687819575255599301 29609195191466170360424869)
        ·
          refine ⟨5551724098399906942579663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29609195191466170360424869 5551724098399906942579663)
          ·
            refine ⟨8327586147599860413869495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551724098399906942579663 8327586147599860413869495)
            ·
              refine ⟨12491379221399790620804243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8327586147599860413869495 12491379221399790620804243)
              ·
                refine ⟨18737068832099685931206365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12491379221399790620804243 18737068832099685931206365)
                ·
                  refine ⟨7026400812037382224202387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18737068832099685931206365 7026400812037382224202387)
                  ·
                    refine ⟨10539601218056073336303581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026400812037382224202387 10539601218056073336303581)
                    ·
                      refine ⟨3952350456771027501113843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539601218056073336303581 3952350456771027501113843)
                      ·
                        rfl

theorem cell23_7697175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_7697175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697175 prefixEnd_7697175 := by exact prefixLift 7697175
  have htrace : WordTrace (prefixWord ++ tailWord_7697175) baseStart_7697175 baseEnd_7697175 := by
    simpa [prefixWord, tailWord_7697175, baseEnd_7697175] using wordTrace_append hprefix tailTrace_7697175
  have hstable : (prefixWord ++ tailWord_7697175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697175).length < 2 ^ (prefixWord ++ tailWord_7697175).sum := by decide
  have hdescent : baseEnd_7697175 < baseStart_7697175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697177 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_7697177 : Nat := 118140960795 + 7697177 * 2 ^ 59
def prefixEnd_7697177 : Nat := 4983230072969 + 3 ^ 40 * 7697177 * 2
def baseEnd_7697177 : Nat := 3952351483732336493288833

theorem tailTrace_7697177 : CollatzResearch.WordTrace tailWord_7697177 prefixEnd_7697177 3952351483732336493288833 := by
  unfold tailWord_7697177
  simp only [CollatzResearch.WordTrace]
  refine ⟨280739108835449777018193785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187159405890299851345462523 280739108835449777018193785)
  ·
    refine ⟨210554331626587332763645339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280739108835449777018193785 210554331626587332763645339)
    ·
      refine ⟨315831497439880999145468009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210554331626587332763645339 315831497439880999145468009)
      ·
        refine ⟨236873623079910749359101007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315831497439880999145468009 236873623079910749359101007)
        ·
          refine ⟨355310434619866124038651511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236873623079910749359101007 355310434619866124038651511)
          ·
            refine ⟨532965651929799186057977267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355310434619866124038651511 532965651929799186057977267)
            ·
              refine ⟨799448477894698779086965901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 532965651929799186057977267 799448477894698779086965901)
              ·
                refine ⟨299793179210512042157612213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799448477894698779086965901 299793179210512042157612213)
                ·
                  refine ⟨28105610550985503952276145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 299793179210512042157612213 28105610550985503952276145)
                  ·
                    refine ⟨21079207913239127964207109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28105610550985503952276145 21079207913239127964207109)
                    ·
                      refine ⟨3952351483732336493288833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21079207913239127964207109 3952351483732336493288833)
                      ·
                        rfl

theorem cell23_7697177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_7697177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697177 prefixEnd_7697177 := by exact prefixLift 7697177
  have htrace : WordTrace (prefixWord ++ tailWord_7697177) baseStart_7697177 baseEnd_7697177 := by
    simpa [prefixWord, tailWord_7697177, baseEnd_7697177] using wordTrace_append hprefix tailTrace_7697177
  have hstable : (prefixWord ++ tailWord_7697177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697177).length < 2 ^ (prefixWord ++ tailWord_7697177).sum := by decide
  have hdescent : baseEnd_7697177 < baseStart_7697177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697184 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5]
def baseStart_7697184 : Nat := 118140960795 + 7697184 * 2 ^ 59
def prefixEnd_7697184 : Nat := 4983230072969 + 3 ^ 40 * 7697184 * 2
def baseEnd_7697184 : Nat := 3952355078096917965901301

theorem tailTrace_7697184 : CollatzResearch.WordTrace tailWord_7697184 prefixEnd_7697184 3952355078096917965901301 := by
  unfold tailWord_7697184
  simp only [CollatzResearch.WordTrace]
  refine ⟨140369682073212208606849303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187159576097616278142465737 140369682073212208606849303)
  ·
    refine ⟨210554523109818312910273955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140369682073212208606849303 210554523109818312910273955)
    ·
      refine ⟨315831784664727469365410933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210554523109818312910273955 315831784664727469365410933)
      ·
        refine ⟨29609229812318200253007275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315831784664727469365410933 29609229812318200253007275)
        ·
          refine ⟨44413844718477300379510913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29609229812318200253007275 44413844718477300379510913)
          ·
            refine ⟨33310383538857975284633185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44413844718477300379510913 33310383538857975284633185)
            ·
              refine ⟨24982787654143481463474889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33310383538857975284633185 24982787654143481463474889)
              ·
                refine ⟨18737090740607611097606167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24982787654143481463474889 18737090740607611097606167)
                ·
                  refine ⟨28105636110911416646409251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18737090740607611097606167 28105636110911416646409251)
                  ·
                    refine ⟨42158454166367124969613877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28105636110911416646409251 42158454166367124969613877)
                    ·
                      refine ⟨3952355078096917965901301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42158454166367124969613877 3952355078096917965901301)
                      ·
                        rfl

theorem cell23_7697184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_7697184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697184 prefixEnd_7697184 := by exact prefixLift 7697184
  have htrace : WordTrace (prefixWord ++ tailWord_7697184) baseStart_7697184 baseEnd_7697184 := by
    simpa [prefixWord, tailWord_7697184, baseEnd_7697184] using wordTrace_append hprefix tailTrace_7697184
  have hstable : (prefixWord ++ tailWord_7697184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697184).length < 2 ^ (prefixWord ++ tailWord_7697184).sum := by decide
  have hdescent : baseEnd_7697184 < baseStart_7697184 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697198 : List Nat := [4, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_7697198 : Nat := 118140960795 + 7697198 * 2 ^ 59
def prefixEnd_7697198 : Nat := 4983230072969 + 3 ^ 40 * 7697198 * 2
def baseEnd_7697198 : Nat := 3952362266826080911126237

theorem tailTrace_7697198 : CollatzResearch.WordTrace tailWord_7697198 prefixEnd_7697198 3952362266826080911126237 := by
  unfold tailWord_7697198
  simp only [CollatzResearch.WordTrace]
  refine ⟨35092484346046712200588531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187159916512249131736472165 35092484346046712200588531)
  ·
    refine ⟨52638726519070068300882797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35092484346046712200588531 52638726519070068300882797)
    ·
      refine ⟨19739522444651275612831049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52638726519070068300882797 19739522444651275612831049)
      ·
        refine ⟨14804641833488456709623287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19739522444651275612831049 14804641833488456709623287)
        ·
          refine ⟨22206962750232685064434931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14804641833488456709623287 22206962750232685064434931)
          ·
            refine ⟨33310444125349027596652397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22206962750232685064434931 33310444125349027596652397)
            ·
              refine ⟨12491416547005885348744649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33310444125349027596652397 12491416547005885348744649)
              ·
                refine ⟨9368562410254414011558487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12491416547005885348744649 9368562410254414011558487)
                ·
                  refine ⟨14052843615381621017337731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368562410254414011558487 14052843615381621017337731)
                  ·
                    refine ⟨21079265423072431526006597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14052843615381621017337731 21079265423072431526006597)
                    ·
                      refine ⟨3952362266826080911126237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21079265423072431526006597 3952362266826080911126237)
                      ·
                        rfl

theorem cell23_7697198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_7697198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697198 prefixEnd_7697198 := by exact prefixLift 7697198
  have htrace : WordTrace (prefixWord ++ tailWord_7697198) baseStart_7697198 baseEnd_7697198 := by
    simpa [prefixWord, tailWord_7697198, baseEnd_7697198] using wordTrace_append hprefix tailTrace_7697198
  have hstable : (prefixWord ++ tailWord_7697198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697198).length < 2 ^ (prefixWord ++ tailWord_7697198).sum := by decide
  have hdescent : baseEnd_7697198 < baseStart_7697198 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697241 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 3, 3, 2]
def baseStart_7697241 : Nat := 118140960795 + 7697241 * 2 ^ 59
def prefixEnd_7697241 : Nat := 4983230072969 + 3 ^ 40 * 7697241 * 2
def baseEnd_7697241 : Nat := 3952384346494224242888539

theorem tailTrace_7697241 : CollatzResearch.WordTrace tailWord_7697241 prefixEnd_7697241 3952384346494224242888539 := by
  unfold tailWord_7697241
  simp only [CollatzResearch.WordTrace]
  refine ⟨280741443107217915948523577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187160962071478610632349051 280741443107217915948523577)
  ·
    refine ⟨210556082330413436961392683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280741443107217915948523577 210556082330413436961392683)
    ·
      refine ⟨315834123495620155442089025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210556082330413436961392683 315834123495620155442089025)
      ·
        refine ⟨236875592621715116581566769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315834123495620155442089025 236875592621715116581566769)
        ·
          refine ⟨177656694466286337436175077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236875592621715116581566769 177656694466286337436175077)
          ·
            refine ⟨33310630212428688269282827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177656694466286337436175077 33310630212428688269282827)
            ·
              refine ⟨49965945318643032403924241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33310630212428688269282827 49965945318643032403924241)
              ·
                refine ⟨37474458988982274302943181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49965945318643032403924241 37474458988982274302943181)
                ·
                  refine ⟨14052922120868352863603693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37474458988982274302943181 14052922120868352863603693)
                  ·
                    refine ⟨5269845795325632323851385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14052922120868352863603693 5269845795325632323851385)
                    ·
                      refine ⟨3952384346494224242888539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269845795325632323851385 3952384346494224242888539)
                      ·
                        rfl

theorem cell23_7697241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_7697241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697241 prefixEnd_7697241 := by exact prefixLift 7697241
  have htrace : WordTrace (prefixWord ++ tailWord_7697241) baseStart_7697241 baseEnd_7697241 := by
    simpa [prefixWord, tailWord_7697241, baseEnd_7697241] using wordTrace_append hprefix tailTrace_7697241
  have hstable : (prefixWord ++ tailWord_7697241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697241).length < 2 ^ (prefixWord ++ tailWord_7697241).sum := by decide
  have hdescent : baseEnd_7697241 < baseStart_7697241 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697282 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 4, 1, 3]
def baseStart_7697282 : Nat := 118140960795 + 7697282 * 2 ^ 59
def prefixEnd_7697282 : Nat := 4983230072969 + 3 ^ 40 * 7697282 * 2
def baseEnd_7697282 : Nat := 3952405399201058582475851

theorem tailTrace_7697282 : CollatzResearch.WordTrace tailWord_7697282 prefixEnd_7697282 3952405399201058582475851 := by
  unfold tailWord_7697282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70185734625017344987691525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187161959000046253300510733 70185734625017344987691525)
  ·
    refine ⟨13159825242190752185192161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70185734625017344987691525 13159825242190752185192161)
    ·
      refine ⟨9869868931643064138894121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13159825242190752185192161 9869868931643064138894121)
      ·
        refine ⟨7402401698732298104170591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9869868931643064138894121 7402401698732298104170591)
        ·
          refine ⟨11103602548098447156255887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402401698732298104170591 11103602548098447156255887)
          ·
            refine ⟨16655403822147670734383831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11103602548098447156255887 16655403822147670734383831)
            ·
              refine ⟨24983105733221506101575747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16655403822147670734383831 24983105733221506101575747)
              ·
                refine ⟨37474658599832259152363621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24983105733221506101575747 37474658599832259152363621)
                ·
                  refine ⟨7026498487468548591068179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37474658599832259152363621 7026498487468548591068179)
                  ·
                    refine ⟨10539747731202822886602269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026498487468548591068179 10539747731202822886602269)
                    ·
                      refine ⟨3952405399201058582475851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539747731202822886602269 3952405399201058582475851)
                      ·
                        rfl

theorem cell23_7697282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_7697282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697282 prefixEnd_7697282 := by exact prefixLift 7697282
  have htrace : WordTrace (prefixWord ++ tailWord_7697282) baseStart_7697282 baseEnd_7697282 := by
    simpa [prefixWord, tailWord_7697282, baseEnd_7697282] using wordTrace_append hprefix tailTrace_7697282
  have hstable : (prefixWord ++ tailWord_7697282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697282).length < 2 ^ (prefixWord ++ tailWord_7697282).sum := by decide
  have hdescent : baseEnd_7697282 < baseStart_7697282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697350 : List Nat := [6, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_7697350 : Nat := 118140960795 + 7697350 * 2 ^ 59
def prefixEnd_7697350 : Nat := 4983230072969 + 3 ^ 40 * 7697350 * 2
def baseEnd_7697350 : Nat := 3952440315885564316425539

theorem tailTrace_7697350 : CollatzResearch.WordTrace tailWord_7697350 prefixEnd_7697350 3952440315885564316425539 := by
  unfold tailWord_7697350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8773294333244469611382547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 187163612442548685042827669 8773294333244469611382547)
  ·
    refine ⟨13159941499866704417073821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8773294333244469611382547 13159941499866704417073821)
    ·
      refine ⟨4934978062450014156402683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13159941499866704417073821 4934978062450014156402683)
      ·
        refine ⟨7402467093675021234604025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4934978062450014156402683 7402467093675021234604025)
        ·
          refine ⟨5551850320256265925953019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7402467093675021234604025 5551850320256265925953019)
          ·
            refine ⟨8327775480384398888929529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551850320256265925953019 8327775480384398888929529)
            ·
              refine ⟨6245831610288299166697147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327775480384398888929529 6245831610288299166697147)
              ·
                refine ⟨9368747415432448750045721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245831610288299166697147 9368747415432448750045721)
                ·
                  refine ⟨7026560561574336562534291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9368747415432448750045721 7026560561574336562534291)
                  ·
                    refine ⟨10539840842361504843801437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026560561574336562534291 10539840842361504843801437)
                    ·
                      refine ⟨3952440315885564316425539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539840842361504843801437 3952440315885564316425539)
                      ·
                        rfl

theorem cell23_7697350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_7697350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697350 prefixEnd_7697350 := by exact prefixLift 7697350
  have htrace : WordTrace (prefixWord ++ tailWord_7697350) baseStart_7697350 baseEnd_7697350 := by
    simpa [prefixWord, tailWord_7697350, baseEnd_7697350] using wordTrace_append hprefix tailTrace_7697350
  have hstable : (prefixWord ++ tailWord_7697350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697350).length < 2 ^ (prefixWord ++ tailWord_7697350).sum := by decide
  have hdescent : baseEnd_7697350 < baseStart_7697350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697361 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 6, 2]
def baseStart_7697361 : Nat := 118140960795 + 7697361 * 2 ^ 59
def prefixEnd_7697361 : Nat := 4983230072969 + 3 ^ 40 * 7697361 * 2
def baseEnd_7697361 : Nat := 3952445964172763773387987

theorem tailTrace_7697361 : CollatzResearch.WordTrace tailWord_7697361 prefixEnd_7697361 3952445964172763773387987 := by
  unfold tailWord_7697361
  simp only [CollatzResearch.WordTrace]
  refine ⟨280745819866783176442891937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187163879911188784295261291 280745819866783176442891937)
  ·
    refine ⟨210559364900087382332168953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280745819866783176442891937 210559364900087382332168953)
    ·
      refine ⟨157919523675065536749126715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210559364900087382332168953 157919523675065536749126715)
      ·
        refine ⟨236879285512598305123690073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157919523675065536749126715 236879285512598305123690073)
        ·
          refine ⟨177659464134448728842767555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236879285512598305123690073 177659464134448728842767555)
          ·
            refine ⟨266489196201673093264151333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177659464134448728842767555 266489196201673093264151333)
            ·
              refine ⟨49966724287813704987028375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 266489196201673093264151333 49966724287813704987028375)
              ·
                refine ⟨74950086431720557480542563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49966724287813704987028375 74950086431720557480542563)
                ·
                  refine ⟨112425129647580836220813845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74950086431720557480542563 112425129647580836220813845)
                  ·
                    refine ⟨5269927952230351697850649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112425129647580836220813845 5269927952230351697850649)
                    ·
                      refine ⟨3952445964172763773387987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5269927952230351697850649 3952445964172763773387987)
                      ·
                        rfl

theorem cell23_7697361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_7697361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697361 prefixEnd_7697361 := by exact prefixLift 7697361
  have htrace : WordTrace (prefixWord ++ tailWord_7697361) baseStart_7697361 baseEnd_7697361 := by
    simpa [prefixWord, tailWord_7697361, baseEnd_7697361] using wordTrace_append hprefix tailTrace_7697361
  have hstable : (prefixWord ++ tailWord_7697361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697361).length < 2 ^ (prefixWord ++ tailWord_7697361).sum := by decide
  have hdescent : baseEnd_7697361 < baseStart_7697361 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697384 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 10]
def baseStart_7697384 : Nat := 118140960795 + 7697384 * 2 ^ 59
def prefixEnd_7697384 : Nat := 4983230072969 + 3 ^ 40 * 7697384 * 2
def baseEnd_7697384 : Nat := 439161974914201909266709

theorem tailTrace_7697384 : CollatzResearch.WordTrace tailWord_7697384 prefixEnd_7697384 439161974914201909266709 := by
  unfold tailWord_7697384
  simp only [CollatzResearch.WordTrace]
  refine ⟨140373329372849925685489603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187164439163799900913986137 140373329372849925685489603)
  ·
    refine ⟨210559994059274888528234405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140373329372849925685489603 210559994059274888528234405)
    ·
      refine ⟨39479998886114041599043951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210559994059274888528234405 39479998886114041599043951)
      ·
        refine ⟨59219998329171062398565927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39479998886114041599043951 59219998329171062398565927)
        ·
          refine ⟨88829997493756593597848891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59219998329171062398565927 88829997493756593597848891)
          ·
            refine ⟨133244996240634890396773337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88829997493756593597848891 133244996240634890396773337)
            ·
              refine ⟨99933747180476167797580003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133244996240634890396773337 99933747180476167797580003)
              ·
                refine ⟨149900620770714251696370005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99933747180476167797580003 149900620770714251696370005)
                ·
                  refine ⟨439161974914201909266709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149900620770714251696370005 439161974914201909266709)
                  ·
                    rfl

theorem cell23_7697384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 10].length) (baseStart_7697384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697384 prefixEnd_7697384 := by exact prefixLift 7697384
  have htrace : WordTrace (prefixWord ++ tailWord_7697384) baseStart_7697384 baseEnd_7697384 := by
    simpa [prefixWord, tailWord_7697384, baseEnd_7697384] using wordTrace_append hprefix tailTrace_7697384
  have hstable : (prefixWord ++ tailWord_7697384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697384).length < 2 ^ (prefixWord ++ tailWord_7697384).sum := by decide
  have hdescent : baseEnd_7697384 < baseStart_7697384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697401 : List Nat := [1, 2, 1, 3, 1, 3, 4, 2, 6]
def baseStart_7697401 : Nat := 118140960795 + 7697401 * 2 ^ 59
def prefixEnd_7697401 : Nat := 4983230072969 + 3 ^ 40 * 7697401 * 2
def baseEnd_7697401 : Nat := 439162944822104846320867

theorem tailTrace_7697401 : CollatzResearch.WordTrace tailWord_7697401 prefixEnd_7697401 439162944822104846320867 := by
  unfold tailWord_7697401
  simp only [CollatzResearch.WordTrace]
  refine ⟨280747278786638263274348057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187164852524425508849565371 280747278786638263274348057)
  ·
    refine ⟨210560459089978697455761043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280747278786638263274348057 210560459089978697455761043)
    ·
      refine ⟨315840688634968046183641565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210560459089978697455761043 315840688634968046183641565)
      ·
        refine ⟨118440258238113017318865587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315840688634968046183641565 118440258238113017318865587)
        ·
          refine ⟨177660387357169525978298381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118440258238113017318865587 177660387357169525978298381)
          ·
            refine ⟨66622645258938572241861893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177660387357169525978298381 66622645258938572241861893)
            ·
              refine ⟨12491745986050982295349105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66622645258938572241861893 12491745986050982295349105)
              ·
                refine ⟨9368809489538236721511829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12491745986050982295349105 9368809489538236721511829)
                ·
                  refine ⟨439162944822104846320867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9368809489538236721511829 439162944822104846320867)
                  ·
                    rfl

theorem cell23_7697401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_7697401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697401 prefixEnd_7697401 := by exact prefixLift 7697401
  have htrace : WordTrace (prefixWord ++ tailWord_7697401) baseStart_7697401 baseEnd_7697401 := by
    simpa [prefixWord, tailWord_7697401, baseEnd_7697401] using wordTrace_append hprefix tailTrace_7697401
  have hstable : (prefixWord ++ tailWord_7697401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697401).length < 2 ^ (prefixWord ++ tailWord_7697401).sum := by decide
  have hdescent : baseEnd_7697401 < baseStart_7697401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697462 : List Nat := [5, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3]
def baseStart_7697462 : Nat := 118140960795 + 7697462 * 2 ^ 59
def prefixEnd_7697462 : Nat := 4983230072969 + 3 ^ 40 * 7697462 * 2
def baseEnd_7697462 : Nat := 3952497825718867878225023

theorem tailTrace_7697462 : CollatzResearch.WordTrace tailWord_7697462 prefixEnd_7697462 3952497825718867878225023 := by
  unfold tailWord_7697462
  simp only [CollatzResearch.WordTrace]
  refine ⟨17546843977463579418269915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187166335759611513794879093 17546843977463579418269915)
  ·
    refine ⟨26320265966195369127404873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17546843977463579418269915 26320265966195369127404873)
    ·
      refine ⟨19740199474646526845553655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26320265966195369127404873 19740199474646526845553655)
      ·
        refine ⟨29610299211969790268330483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19740199474646526845553655 29610299211969790268330483)
        ·
          refine ⟨44415448817954685402495725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29610299211969790268330483 44415448817954685402495725)
          ·
            refine ⟨16655793306733007025935897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44415448817954685402495725 16655793306733007025935897)
            ·
              refine ⟨12491844980049755269451923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16655793306733007025935897 12491844980049755269451923)
              ·
                refine ⟨18737767470074632904177885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12491844980049755269451923 18737767470074632904177885)
                ·
                  refine ⟨7026662801277987339066707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18737767470074632904177885 7026662801277987339066707)
                  ·
                    refine ⟨10539994201916981008600061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7026662801277987339066707 10539994201916981008600061)
                    ·
                      refine ⟨3952497825718867878225023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10539994201916981008600061 3952497825718867878225023)
                      ·
                        rfl

theorem cell23_7697462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_7697462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697462 prefixEnd_7697462 := by exact prefixLift 7697462
  have htrace : WordTrace (prefixWord ++ tailWord_7697462) baseStart_7697462 baseEnd_7697462 := by
    simpa [prefixWord, tailWord_7697462, baseEnd_7697462] using wordTrace_append hprefix tailTrace_7697462
  have hstable : (prefixWord ++ tailWord_7697462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697462).length < 2 ^ (prefixWord ++ tailWord_7697462).sum := by decide
  have hdescent : baseEnd_7697462 < baseStart_7697462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697481 : List Nat := [1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_7697481 : Nat := 118140960795 + 7697481 * 2 ^ 59
def prefixEnd_7697481 : Nat := 4983230072969 + 3 ^ 40 * 7697481 * 2
def baseEnd_7697481 : Nat := 3952507581851303303887435

theorem tailTrace_7697481 : CollatzResearch.WordTrace tailWord_7697481 prefixEnd_7697481 3952507581851303303887435 := by
  unfold tailWord_7697481
  simp only [CollatzResearch.WordTrace]
  refine ⟨280750196626348436937260297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187166797750898957958173531 280750196626348436937260297)
  ·
    refine ⟨210562647469761327702945223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280750196626348436937260297 210562647469761327702945223)
    ·
      refine ⟨315843971204641991554417835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210562647469761327702945223 315843971204641991554417835)
      ·
        refine ⟨473765956806962987331626753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315843971204641991554417835 473765956806962987331626753)
        ·
          refine ⟨355324467605222240498720065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473765956806962987331626753 355324467605222240498720065)
          ·
            refine ⟨266493350703916680374040049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 355324467605222240498720065 266493350703916680374040049)
            ·
              refine ⟨199870013027937510280530037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 266493350703916680374040049 199870013027937510280530037)
              ·
                refine ⟨18737813721369141588799691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 199870013027937510280530037 18737813721369141588799691)
                ·
                  refine ⟨28106720582053712383199537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18737813721369141588799691 28106720582053712383199537)
                  ·
                    refine ⟨21080040436540284287399653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28106720582053712383199537 21080040436540284287399653)
                    ·
                      refine ⟨3952507581851303303887435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21080040436540284287399653 3952507581851303303887435)
                      ·
                        rfl

theorem cell23_7697481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_7697481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697481 prefixEnd_7697481 := by exact prefixLift 7697481
  have htrace : WordTrace (prefixWord ++ tailWord_7697481) baseStart_7697481 baseEnd_7697481 := by
    simpa [prefixWord, tailWord_7697481, baseEnd_7697481] using wordTrace_append hprefix tailTrace_7697481
  have hstable : (prefixWord ++ tailWord_7697481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697481).length < 2 ^ (prefixWord ++ tailWord_7697481).sum := by decide
  have hdescent : baseEnd_7697481 < baseStart_7697481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697485 : List Nat := [1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_7697485 : Nat := 118140960795 + 7697485 * 2 ^ 59
def prefixEnd_7697485 : Nat := 4983230072969 + 3 ^ 40 * 7697485 * 2
def baseEnd_7697485 : Nat := 3952509635773921288237417

theorem tailTrace_7697485 : CollatzResearch.WordTrace tailWord_7697485 prefixEnd_7697485 3952509635773921288237417 := by
  unfold tailWord_7697485
  simp only [CollatzResearch.WordTrace]
  refine ⟨280750342518333945620405909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187166895012222630413603939 280750342518333945620405909)
  ·
    refine ⟨13160172305546903700956527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 280750342518333945620405909 13160172305546903700956527)
    ·
      refine ⟨19740258458320355551434791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13160172305546903700956527 19740258458320355551434791)
      ·
        refine ⟨29610387687480533327152187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19740258458320355551434791 29610387687480533327152187)
        ·
          refine ⟨44415581531220799990728281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29610387687480533327152187 44415581531220799990728281)
          ·
            refine ⟨33311686148415599993046211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44415581531220799990728281 33311686148415599993046211)
            ·
              refine ⟨49967529222623399989569317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33311686148415599993046211 49967529222623399989569317)
              ·
                refine ⟨9368911729241887498044247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49967529222623399989569317 9368911729241887498044247)
                ·
                  refine ⟨14053367593862831247066371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9368911729241887498044247 14053367593862831247066371)
                  ·
                    refine ⟨21080051390794246870599557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14053367593862831247066371 21080051390794246870599557)
                    ·
                      refine ⟨3952509635773921288237417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21080051390794246870599557 3952509635773921288237417)
                      ·
                        rfl

theorem cell23_7697485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_7697485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697485 prefixEnd_7697485 := by exact prefixLift 7697485
  have htrace : WordTrace (prefixWord ++ tailWord_7697485) baseStart_7697485 baseEnd_7697485 := by
    simpa [prefixWord, tailWord_7697485, baseEnd_7697485] using wordTrace_append hprefix tailTrace_7697485
  have hstable : (prefixWord ++ tailWord_7697485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697485).length < 2 ^ (prefixWord ++ tailWord_7697485).sum := by decide
  have hdescent : baseEnd_7697485 < baseStart_7697485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697519 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 1, 2, 2]
def baseStart_7697519 : Nat := 118140960795 + 7697519 * 2 ^ 59
def prefixEnd_7697519 : Nat := 4983230072969 + 3 ^ 40 * 7697519 * 2
def baseEnd_7697519 : Nat := 3952527094116174155212261

theorem tailTrace_7697519 : CollatzResearch.WordTrace tailWord_7697519 prefixEnd_7697519 3952527094116174155212261 := by
  unfold tailWord_7697519
  simp only [CollatzResearch.WordTrace]
  refine ⟨280751582600210769427143611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187167721733473846284762407 280751582600210769427143611)
  ·
    refine ⟨421127373900316154140715417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280751582600210769427143611 421127373900316154140715417)
    ·
      refine ⟨315845530425237115605536563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421127373900316154140715417 315845530425237115605536563)
      ·
        refine ⟨473768295637855673408304845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315845530425237115605536563 473768295637855673408304845)
        ·
          refine ⟨177663110864195877528114317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473768295637855673408304845 177663110864195877528114317)
          ·
            refine ⟨66623666574073454073042869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177663110864195877528114317 66623666574073454073042869)
            ·
              refine ⟨6245968741319386319347769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66623666574073454073042869 6245968741319386319347769)
              ·
                refine ⟨4684476555989539739510827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6245968741319386319347769 4684476555989539739510827)
                ·
                  refine ⟨7026714833984309609266241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684476555989539739510827 7026714833984309609266241)
                  ·
                    refine ⟨5270036125488232206949681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7026714833984309609266241 5270036125488232206949681)
                    ·
                      refine ⟨3952527094116174155212261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270036125488232206949681 3952527094116174155212261)
                      ·
                        rfl

theorem cell23_7697519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 1, 2, 2].length) (baseStart_7697519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697519 prefixEnd_7697519 := by exact prefixLift 7697519
  have htrace : WordTrace (prefixWord ++ tailWord_7697519) baseStart_7697519 baseEnd_7697519 := by
    simpa [prefixWord, tailWord_7697519, baseEnd_7697519] using wordTrace_append hprefix tailTrace_7697519
  have hstable : (prefixWord ++ tailWord_7697519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697519).length < 2 ^ (prefixWord ++ tailWord_7697519).sum := by decide
  have hdescent : baseEnd_7697519 < baseStart_7697519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697525 : List Nat := [1, 3, 4, 3, 1, 1, 2, 8]
def baseStart_7697525 : Nat := 118140960795 + 7697525 * 2 ^ 59
def prefixEnd_7697525 : Nat := 4983230072969 + 3 ^ 40 * 7697525 * 2
def baseEnd_7697525 : Nat := 146390006481485227101379

theorem tailTrace_7697525 : CollatzResearch.WordTrace tailWord_7697525 prefixEnd_7697525 146390006481485227101379 := by
  unfold tailWord_7697525
  simp only [CollatzResearch.WordTrace]
  refine ⟨280751801438189032451862029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187167867625459354967908019 280751801438189032451862029)
  ·
    refine ⟨105281925539320887169448261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280751801438189032451862029 105281925539320887169448261)
    ·
      refine ⟨19740361038622666344271549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105281925539320887169448261 19740361038622666344271549)
      ·
        refine ⟨7402635389483499879101831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19740361038622666344271549 7402635389483499879101831)
        ·
          refine ⟨11103953084225249818652747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7402635389483499879101831 11103953084225249818652747)
          ·
            refine ⟨16655929626337874727979121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11103953084225249818652747 16655929626337874727979121)
            ·
              refine ⟨12491947219753406045984341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16655929626337874727979121 12491947219753406045984341)
              ·
                refine ⟨146390006481485227101379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12491947219753406045984341 146390006481485227101379)
                ·
                  rfl

theorem cell23_7697525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 8].length) (baseStart_7697525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697525 prefixEnd_7697525 := by exact prefixLift 7697525
  have htrace : WordTrace (prefixWord ++ tailWord_7697525) baseStart_7697525 baseEnd_7697525 := by
    simpa [prefixWord, tailWord_7697525, baseEnd_7697525] using wordTrace_append hprefix tailTrace_7697525
  have hstable : (prefixWord ++ tailWord_7697525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697525).length < 2 ^ (prefixWord ++ tailWord_7697525).sum := by decide
  have hdescent : baseEnd_7697525 < baseStart_7697525 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697529 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 2, 4]
def baseStart_7697529 : Nat := 118140960795 + 7697529 * 2 ^ 59
def prefixEnd_7697529 : Nat := 4983230072969 + 3 ^ 40 * 7697529 * 2
def baseEnd_7697529 : Nat := 1317510742974239705362405

theorem tailTrace_7697529 : CollatzResearch.WordTrace tailWord_7697529 prefixEnd_7697529 1317510742974239705362405 := by
  unfold tailWord_7697529
  simp only [CollatzResearch.WordTrace]
  refine ⟨280751947330174541135007641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187167964886783027423338427 280751947330174541135007641)
  ·
    refine ⟨210563960497630905851255731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280751947330174541135007641 210563960497630905851255731)
    ·
      refine ⟨315845940746446358776883597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210563960497630905851255731 315845940746446358776883597)
      ·
        refine ⟨118442227779917384541331349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315845940746446358776883597 118442227779917384541331349)
        ·
          refine ⟨5551979427183627400374907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 118442227779917384541331349 5551979427183627400374907)
          ·
            refine ⟨8327969140775441100562361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5551979427183627400374907 8327969140775441100562361)
            ·
              refine ⟨6245976855581580825421771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8327969140775441100562361 6245976855581580825421771)
              ·
                refine ⟨9368965283372371238132657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6245976855581580825421771 9368965283372371238132657)
                ·
                  refine ⟨7026723962529278428599493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9368965283372371238132657 7026723962529278428599493)
                  ·
                    refine ⟨1317510742974239705362405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026723962529278428599493 1317510742974239705362405)
                    ·
                      rfl

theorem cell23_7697529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 2, 4].length) (baseStart_7697529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697529 prefixEnd_7697529 := by exact prefixLift 7697529
  have htrace : WordTrace (prefixWord ++ tailWord_7697529) baseStart_7697529 baseEnd_7697529 := by
    simpa [prefixWord, tailWord_7697529, baseEnd_7697529] using wordTrace_append hprefix tailTrace_7697529
  have hstable : (prefixWord ++ tailWord_7697529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697529).length < 2 ^ (prefixWord ++ tailWord_7697529).sum := by decide
  have hdescent : baseEnd_7697529 < baseStart_7697529 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697545 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 3, 3, 2]
def baseStart_7697545 : Nat := 118140960795 + 7697545 * 2 ^ 59
def prefixEnd_7697545 : Nat := 4983230072969 + 3 ^ 40 * 7697545 * 2
def baseEnd_7697545 : Nat := 3952540444613191053487141

theorem tailTrace_7697545 : CollatzResearch.WordTrace tailWord_7697545 prefixEnd_7697545 3952540444613191053487141 := by
  unfold tailWord_7697545
  simp only [CollatzResearch.WordTrace]
  refine ⟨280752530898116575867590089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187168353932077717245060059 280752530898116575867590089)
  ·
    refine ⟨210564398173587431900692567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280752530898116575867590089 210564398173587431900692567)
    ·
      refine ⟨315846597260381147851038851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210564398173587431900692567 315846597260381147851038851)
      ·
        refine ⟨473769895890571721776558277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315846597260381147851038851 473769895890571721776558277)
        ·
          refine ⟨88831855479482197833104677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 473769895890571721776558277 88831855479482197833104677)
          ·
            refine ⟨16655972902402912093707127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88831855479482197833104677 16655972902402912093707127)
            ·
              refine ⟨24983959353604368140560691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16655972902402912093707127 24983959353604368140560691)
              ·
                refine ⟨37475939030406552210841037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24983959353604368140560691 37475939030406552210841037)
                ·
                  refine ⟨14053477136402457079065389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37475939030406552210841037 14053477136402457079065389)
                  ·
                    refine ⟨5270053926150921404649521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14053477136402457079065389 5270053926150921404649521)
                    ·
                      refine ⟨3952540444613191053487141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270053926150921404649521 3952540444613191053487141)
                      ·
                        rfl

theorem cell23_7697545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 3, 2].length) (baseStart_7697545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697545 prefixEnd_7697545 := by exact prefixLift 7697545
  have htrace : WordTrace (prefixWord ++ tailWord_7697545) baseStart_7697545 baseEnd_7697545 := by
    simpa [prefixWord, tailWord_7697545, baseEnd_7697545] using wordTrace_append hprefix tailTrace_7697545
  have hstable : (prefixWord ++ tailWord_7697545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697545).length < 2 ^ (prefixWord ++ tailWord_7697545).sum := by decide
  have hdescent : baseEnd_7697545 < baseStart_7697545 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697570 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_7697570 : Nat := 118140960795 + 7697570 * 2 ^ 59
def prefixEnd_7697570 : Nat := 4983230072969 + 3 ^ 40 * 7697570 * 2
def baseEnd_7697570 : Nat := 3952553281629553455674527

theorem tailTrace_7697570 : CollatzResearch.WordTrace tailWord_7697570 prefixEnd_7697570 3952553281629553455674527 := by
  unfold tailWord_7697570
  simp only [CollatzResearch.WordTrace]
  refine ⟨70188360680756501284312541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187168961815350670091500109 70188360680756501284312541)
  ·
    refine ⟨26320635255283687981617203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70188360680756501284312541 26320635255283687981617203)
    ·
      refine ⟨39480952882925531972425805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26320635255283687981617203 39480952882925531972425805)
      ·
        refine ⟨14805357331097074489659677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39480952882925531972425805 14805357331097074489659677)
        ·
          refine ⟨5552008999161402933622379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14805357331097074489659677 5552008999161402933622379)
          ·
            refine ⟨8328013498742104400433569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552008999161402933622379 8328013498742104400433569)
            ·
              refine ⟨6246010124056578300325177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8328013498742104400433569 6246010124056578300325177)
              ·
                refine ⟨4684507593042433725243883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246010124056578300325177 4684507593042433725243883)
                ·
                  refine ⟨7026761389563650587865825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684507593042433725243883 7026761389563650587865825)
                  ·
                    refine ⟨5270071042172737940899369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7026761389563650587865825 5270071042172737940899369)
                    ·
                      refine ⟨3952553281629553455674527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270071042172737940899369 3952553281629553455674527)
                      ·
                        rfl

theorem cell23_7697570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_7697570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697570 prefixEnd_7697570 := by exact prefixLift 7697570
  have htrace : WordTrace (prefixWord ++ tailWord_7697570) baseStart_7697570 baseEnd_7697570 := by
    simpa [prefixWord, tailWord_7697570, baseEnd_7697570] using wordTrace_append hprefix tailTrace_7697570
  have hstable : (prefixWord ++ tailWord_7697570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697570).length < 2 ^ (prefixWord ++ tailWord_7697570).sum := by decide
  have hdescent : baseEnd_7697570 < baseStart_7697570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697571 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4]
def baseStart_7697571 : Nat := 118140960795 + 7697571 * 2 ^ 59
def prefixEnd_7697571 : Nat := 4983230072969 + 3 ^ 40 * 7697571 * 2
def baseEnd_7697571 : Nat := 3952553795110207951762021

theorem tailTrace_7697571 : CollatzResearch.WordTrace tailWord_7697571 prefixEnd_7697571 3952553795110207951762021 := by
  unfold tailWord_7697571
  simp only [CollatzResearch.WordTrace]
  refine ⟨280753479196022382308036567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187168986130681588205357711 280753479196022382308036567)
  ·
    refine ⟨421130218794033573462054851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280753479196022382308036567 421130218794033573462054851)
    ·
      refine ⟨631695328191050360193082277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421130218794033573462054851 631695328191050360193082277)
      ·
        refine ⟨118442874035821942536202927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 631695328191050360193082277 118442874035821942536202927)
        ·
          refine ⟨177664311053732913804304391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118442874035821942536202927 177664311053732913804304391)
          ·
            refine ⟨266496466580599370706456587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177664311053732913804304391 266496466580599370706456587)
            ·
              refine ⟨399744699870899056059684881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 266496466580599370706456587 399744699870899056059684881)
              ·
                refine ⟨299808524903174292044763661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 399744699870899056059684881 299808524903174292044763661)
                ·
                  refine ⟨112428196838690359516786373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299808524903174292044763661 112428196838690359516786373)
                  ·
                    refine ⟨21080286907254442409397445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112428196838690359516786373 21080286907254442409397445)
                    ·
                      refine ⟨3952553795110207951762021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21080286907254442409397445 3952553795110207951762021)
                      ·
                        rfl

theorem cell23_7697571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_7697571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697571 prefixEnd_7697571 := by exact prefixLift 7697571
  have htrace : WordTrace (prefixWord ++ tailWord_7697571) baseStart_7697571 baseEnd_7697571 := by
    simpa [prefixWord, tailWord_7697571, baseEnd_7697571] using wordTrace_append hprefix tailTrace_7697571
  have hstable : (prefixWord ++ tailWord_7697571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697571).length < 2 ^ (prefixWord ++ tailWord_7697571).sum := by decide
  have hdescent : baseEnd_7697571 < baseStart_7697571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697598 : List Nat := [4, 2, 1, 1, 3, 1, 1, 1, 9]
def baseStart_7697598 : Nat := 118140960795 + 7697598 * 2 ^ 59
def prefixEnd_7697598 : Nat := 4983230072969 + 3 ^ 40 * 7697598 * 2
def baseEnd_7697598 : Nat := 439174184343097705124933

theorem tailTrace_7697598 : CollatzResearch.WordTrace tailWord_7697598 prefixEnd_7697598 439174184343097705124933 := by
  unfold tailWord_7697598
  simp only [CollatzResearch.WordTrace]
  refine ⟨35094307995865570739908681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187169642644616377279512965 35094307995865570739908681)
  ·
    refine ⟨26320730996899178054931511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35094307995865570739908681 26320730996899178054931511)
    ·
      refine ⟨39481096495348767082397267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26320730996899178054931511 39481096495348767082397267)
      ·
        refine ⟨59221644743023150623595901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39481096495348767082397267 59221644743023150623595901)
        ·
          refine ⟨22208116778633681483848463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59221644743023150623595901 22208116778633681483848463)
          ·
            refine ⟨33312175167950522225772695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22208116778633681483848463 33312175167950522225772695)
            ·
              refine ⟨49968262751925783338659043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33312175167950522225772695 49968262751925783338659043)
              ·
                refine ⟨74952394127888675007988565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49968262751925783338659043 74952394127888675007988565)
                ·
                  refine ⟨439174184343097705124933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74952394127888675007988565 439174184343097705124933)
                  ·
                    rfl

theorem cell23_7697598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 9].length) (baseStart_7697598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697598 prefixEnd_7697598 := by exact prefixLift 7697598
  have htrace : WordTrace (prefixWord ++ tailWord_7697598) baseStart_7697598 baseEnd_7697598 := by
    simpa [prefixWord, tailWord_7697598, baseEnd_7697598] using wordTrace_append hprefix tailTrace_7697598
  have hstable : (prefixWord ++ tailWord_7697598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697598).length < 2 ^ (prefixWord ++ tailWord_7697598).sum := by decide
  have hdescent : baseEnd_7697598 < baseStart_7697598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697641 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_7697641 : Nat := 118140960795 + 7697641 * 2 ^ 59
def prefixEnd_7697641 : Nat := 4983230072969 + 3 ^ 40 * 7697641 * 2
def baseEnd_7697641 : Nat := 1317529912918674225962233

theorem tailTrace_7697641 : CollatzResearch.WordTrace tailWord_7697641 prefixEnd_7697641 1317529912918674225962233 := by
  unfold tailWord_7697641
  simp only [CollatzResearch.WordTrace]
  refine ⟨280756032305768784263084777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187170688203845856175389851 280756032305768784263084777)
  ·
    refine ⟨210567024229326588197313583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280756032305768784263084777 210567024229326588197313583)
    ·
      refine ⟨315850536343989882295970375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210567024229326588197313583 315850536343989882295970375)
      ·
        refine ⟨473775804515984823443955563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315850536343989882295970375 473775804515984823443955563)
        ·
          refine ⟨710663706773977235165933345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473775804515984823443955563 710663706773977235165933345)
          ·
            refine ⟨532997780080482926374450009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 710663706773977235165933345 532997780080482926374450009)
            ·
              refine ⟨399748335060362194780837507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 532997780080482926374450009 399748335060362194780837507)
              ·
                refine ⟨599622502590543292171256261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399748335060362194780837507 599622502590543292171256261)
                ·
                  refine ⟨112429219235726867282110549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 599622502590543292171256261 112429219235726867282110549)
                  ·
                    refine ⟨1317529912918674225962233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 112429219235726867282110549 1317529912918674225962233)
                    ·
                      rfl

theorem cell23_7697641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_7697641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697641 prefixEnd_7697641 := by exact prefixLift 7697641
  have htrace : WordTrace (prefixWord ++ tailWord_7697641) baseStart_7697641 baseEnd_7697641 := by
    simpa [prefixWord, tailWord_7697641, baseEnd_7697641] using wordTrace_append hprefix tailTrace_7697641
  have hstable : (prefixWord ++ tailWord_7697641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697641).length < 2 ^ (prefixWord ++ tailWord_7697641).sum := by decide
  have hdescent : baseEnd_7697641 < baseStart_7697641 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697666 : List Nat := [3, 4, 1, 1, 4, 1, 1, 3, 5]
def baseStart_7697666 : Nat := 118140960795 + 7697666 * 2 ^ 59
def prefixEnd_7697666 : Nat := 4983230072969 + 3 ^ 40 * 7697666 * 2
def baseEnd_7697666 : Nat := 439178063974709453341565

theorem tailTrace_7697666 : CollatzResearch.WordTrace tailWord_7697666 prefixEnd_7697666 439178063974709453341565 := by
  unfold tailWord_7697666
  simp only [CollatzResearch.WordTrace]
  refine ⟨70189236032669553383186213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187171296087118809021829901 70189236032669553383186213)
  ·
    refine ⟨13160481756125541259347415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70189236032669553383186213 13160481756125541259347415)
    ·
      refine ⟨19740722634188311889021123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13160481756125541259347415 19740722634188311889021123)
      ·
        refine ⟨29611083951282467833531685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19740722634188311889021123 29611083951282467833531685)
        ·
          refine ⟨5552078240865462718787191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29611083951282467833531685 5552078240865462718787191)
          ·
            refine ⟨8328117361298194078180787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5552078240865462718787191 8328117361298194078180787)
            ·
              refine ⟨12492176041947291117271181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328117361298194078180787 12492176041947291117271181)
              ·
                refine ⟨4684566015730234168976693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12492176041947291117271181 4684566015730234168976693)
                ·
                  refine ⟨439178063974709453341565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4684566015730234168976693 439178063974709453341565)
                  ·
                    rfl

theorem cell23_7697666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_7697666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697666 prefixEnd_7697666 := by exact prefixLift 7697666
  have htrace : WordTrace (prefixWord ++ tailWord_7697666) baseStart_7697666 baseEnd_7697666 := by
    simpa [prefixWord, tailWord_7697666, baseEnd_7697666] using wordTrace_append hprefix tailTrace_7697666
  have hstable : (prefixWord ++ tailWord_7697666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697666).length < 2 ^ (prefixWord ++ tailWord_7697666).sum := by decide
  have hdescent : baseEnd_7697666 < baseStart_7697666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697688 : List Nat := [2, 1, 2, 3, 1, 3, 2, 1, 8]
def baseStart_7697688 : Nat := 118140960795 + 7697688 * 2 ^ 59
def prefixEnd_7697688 : Nat := 4983230072969 + 3 ^ 40 * 7697688 * 2
def baseEnd_7697688 : Nat := 439179319149642665999887

theorem tailTrace_7697688 : CollatzResearch.WordTrace tailWord_7697688 prefixEnd_7697688 439179319149642665999887 := by
  unfold tailWord_7697688
  simp only [CollatzResearch.WordTrace]
  refine ⟨140378873268299255645022859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187171831024399007526697145 140378873268299255645022859)
  ·
    refine ⟨210568309902448883467534289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140378873268299255645022859 210568309902448883467534289)
    ·
      refine ⟨157926232426836662600650717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210568309902448883467534289 157926232426836662600650717)
      ·
        refine ⟨59222337160063748475244019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157926232426836662600650717 59222337160063748475244019)
        ·
          refine ⟨88833505740095622712866029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59222337160063748475244019 88833505740095622712866029)
          ·
            refine ⟨33312564652535858517324761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88833505740095622712866029 33312564652535858517324761)
            ·
              refine ⟨24984423489401893887993571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33312564652535858517324761 24984423489401893887993571)
              ·
                refine ⟨37476635234102840831990357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24984423489401893887993571 37476635234102840831990357)
                ·
                  refine ⟨439179319149642665999887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37476635234102840831990357 439179319149642665999887)
                  ·
                    rfl

theorem cell23_7697688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 8].length) (baseStart_7697688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697688 prefixEnd_7697688 := by exact prefixLift 7697688
  have htrace : WordTrace (prefixWord ++ tailWord_7697688) baseStart_7697688 baseEnd_7697688 := by
    simpa [prefixWord, tailWord_7697688, baseEnd_7697688] using wordTrace_append hprefix tailTrace_7697688
  have hstable : (prefixWord ++ tailWord_7697688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697688).length < 2 ^ (prefixWord ++ tailWord_7697688).sum := by decide
  have hdescent : baseEnd_7697688 < baseStart_7697688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697692 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 1, 4]
def baseStart_7697692 : Nat := 118140960795 + 7697692 * 2 ^ 59
def prefixEnd_7697692 : Nat := 4983230072969 + 3 ^ 40 * 7697692 * 2
def baseEnd_7697692 : Nat := 1317538642089800659449655

theorem tailTrace_7697692 : CollatzResearch.WordTrace tailWord_7697692 prefixEnd_7697692 1317538642089800659449655 := by
  unfold tailWord_7697692
  simp only [CollatzResearch.WordTrace]
  refine ⟨140378946214292009986595665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187171928285722679982127553 140378946214292009986595665)
  ·
    refine ⟨105284209660719007489946749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140378946214292009986595665 105284209660719007489946749)
    ·
      refine ⟨39481578622769627808730031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105284209660719007489946749 39481578622769627808730031)
      ·
        refine ⟨59222367934154441713095047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39481578622769627808730031 59222367934154441713095047)
        ·
          refine ⟨88833551901231662569642571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59222367934154441713095047 88833551901231662569642571)
          ·
            refine ⟨133250327851847493854463857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88833551901231662569642571 133250327851847493854463857)
            ·
              refine ⟨99937745888885620390847893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 133250327851847493854463857 99937745888885620390847893)
              ·
                refine ⟨4684581838541513455820995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99937745888885620390847893 4684581838541513455820995)
                ·
                  refine ⟨7026872757812270183731493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684581838541513455820995 7026872757812270183731493)
                  ·
                    refine ⟨1317538642089800659449655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026872757812270183731493 1317538642089800659449655)
                    ·
                      rfl

theorem cell23_7697692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_7697692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697692 prefixEnd_7697692 := by exact prefixLift 7697692
  have htrace : WordTrace (prefixWord ++ tailWord_7697692) baseStart_7697692 baseEnd_7697692 := by
    simpa [prefixWord, tailWord_7697692, baseEnd_7697692] using wordTrace_append hprefix tailTrace_7697692
  have hstable : (prefixWord ++ tailWord_7697692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697692).length < 2 ^ (prefixWord ++ tailWord_7697692).sum := by decide
  have hdescent : baseEnd_7697692 < baseStart_7697692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697742 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2]
def baseStart_7697742 : Nat := 118140960795 + 7697742 * 2 ^ 59
def prefixEnd_7697742 : Nat := 4983230072969 + 3 ^ 40 * 7697742 * 2
def baseEnd_7697742 : Nat := 3952641600302126782723735

theorem tailTrace_7697742 : CollatzResearch.WordTrace tailWord_7697742 prefixEnd_7697742 3952641600302126782723735 := by
  unfold tailWord_7697742
  simp only [CollatzResearch.WordTrace]
  refine ⟨35094964509800359814063935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187173144052268585675007653 35094964509800359814063935)
  ·
    refine ⟨52642446764700539721095903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35094964509800359814063935 52642446764700539721095903)
    ·
      refine ⟨78963670147050809581643855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52642446764700539721095903 78963670147050809581643855)
      ·
        refine ⟨118445505220576214372465783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78963670147050809581643855 118445505220576214372465783)
        ·
          refine ⟨177668257830864321558698675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118445505220576214372465783 177668257830864321558698675)
          ·
            refine ⟨266502386746296482338048013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177668257830864321558698675 266502386746296482338048013)
            ·
              refine ⟨99938395029861180876768005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266502386746296482338048013 99938395029861180876768005)
              ·
                refine ⟨18738449068098971414394001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99938395029861180876768005 18738449068098971414394001)
                ·
                  refine ⟨14053836801074228560795501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18738449068098971414394001 14053836801074228560795501)
                  ·
                    refine ⟨5270188800402835710298313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14053836801074228560795501 5270188800402835710298313)
                    ·
                      refine ⟨3952641600302126782723735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270188800402835710298313 3952641600302126782723735)
                      ·
                        rfl

theorem cell23_7697742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 3, 2].length) (baseStart_7697742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697742 prefixEnd_7697742 := by exact prefixLift 7697742
  have htrace : WordTrace (prefixWord ++ tailWord_7697742) baseStart_7697742 baseEnd_7697742 := by
    simpa [prefixWord, tailWord_7697742, baseEnd_7697742] using wordTrace_append hprefix tailTrace_7697742
  have hstable : (prefixWord ++ tailWord_7697742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697742).length < 2 ^ (prefixWord ++ tailWord_7697742).sum := by decide
  have hdescent : baseEnd_7697742 < baseStart_7697742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697765 : List Nat := [1, 3, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_7697765 : Nat := 118140960795 + 7697765 * 2 ^ 59
def prefixEnd_7697765 : Nat := 4983230072969 + 3 ^ 40 * 7697765 * 2
def baseEnd_7697765 : Nat := 1317551136785726730912043

theorem tailTrace_7697765 : CollatzResearch.WordTrace tailWord_7697765 prefixEnd_7697765 1317551136785726730912043 := by
  unfold tailWord_7697765
  simp only [CollatzResearch.WordTrace]
  refine ⟨280760554957319553440598749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187173703304879702293732499 280760554957319553440598749)
  ·
    refine ⟨105285208108994832540224531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280760554957319553440598749 105285208108994832540224531)
    ·
      refine ⟨157927812163492248810336797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105285208108994832540224531 157927812163492248810336797)
      ·
        refine ⟨59222929561309593303876299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157927812163492248810336797 59222929561309593303876299)
        ·
          refine ⟨88834394341964389955814449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59222929561309593303876299 88834394341964389955814449)
          ·
            refine ⟨66625795756473292466860837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88834394341964389955814449 66625795756473292466860837)
            ·
              refine ⟨12492336704338742337536407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66625795756473292466860837 12492336704338742337536407)
              ·
                refine ⟨18738505056508113506304611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12492336704338742337536407 18738505056508113506304611)
                ·
                  refine ⟨28107757584762170259456917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18738505056508113506304611 28107757584762170259456917)
                  ·
                    refine ⟨1317551136785726730912043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28107757584762170259456917 1317551136785726730912043)
                    ·
                      rfl

theorem cell23_7697765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_7697765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697765 prefixEnd_7697765 := by exact prefixLift 7697765
  have htrace : WordTrace (prefixWord ++ tailWord_7697765) baseStart_7697765 baseEnd_7697765 := by
    simpa [prefixWord, tailWord_7697765, baseEnd_7697765] using wordTrace_append hprefix tailTrace_7697765
  have hstable : (prefixWord ++ tailWord_7697765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697765).length < 2 ^ (prefixWord ++ tailWord_7697765).sum := by decide
  have hdescent : baseEnd_7697765 < baseStart_7697765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697775 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 3]
def baseStart_7697775 : Nat := 118140960795 + 7697775 * 2 ^ 59
def prefixEnd_7697775 : Nat := 4983230072969 + 3 ^ 40 * 7697775 * 2
def baseEnd_7697775 : Nat := 3952658545163725153611083

theorem tailTrace_7697775 : CollatzResearch.WordTrace tailWord_7697775 prefixEnd_7697775 3952658545163725153611083 := by
  unfold tailWord_7697775
  simp only [CollatzResearch.WordTrace]
  refine ⟨280760919687283325148462779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187173946458188883432308519 280760919687283325148462779)
  ·
    refine ⟨421141379530924987722694169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280760919687283325148462779 421141379530924987722694169)
    ·
      refine ⟨315856034648193740792020627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421141379530924987722694169 315856034648193740792020627)
      ·
        refine ⟨473784051972290611188030941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315856034648193740792020627 473784051972290611188030941)
        ·
          refine ⟨177669019489608979195511603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473784051972290611188030941 177669019489608979195511603)
          ·
            refine ⟨266503529234413468793267405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177669019489608979195511603 266503529234413468793267405)
            ·
              refine ⟨99938823462905050797475277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 266503529234413468793267405 99938823462905050797475277)
              ·
                refine ⟨37477058798589394049053229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99938823462905050797475277 37477058798589394049053229)
                ·
                  refine ⟨14053897049471022768394961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37477058798589394049053229 14053897049471022768394961)
                  ·
                    refine ⟨10540422787103267076296221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14053897049471022768394961 10540422787103267076296221)
                    ·
                      refine ⟨3952658545163725153611083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10540422787103267076296221 3952658545163725153611083)
                      ·
                        rfl

theorem cell23_7697775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 3, 2, 3].length) (baseStart_7697775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697775 prefixEnd_7697775 := by exact prefixLift 7697775
  have htrace : WordTrace (prefixWord ++ tailWord_7697775) baseStart_7697775 baseEnd_7697775 := by
    simpa [prefixWord, tailWord_7697775, baseEnd_7697775] using wordTrace_append hprefix tailTrace_7697775
  have hstable : (prefixWord ++ tailWord_7697775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697775).length < 2 ^ (prefixWord ++ tailWord_7697775).sum := by decide
  have hdescent : baseEnd_7697775 < baseStart_7697775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697785 : List Nat := [1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_7697785 : Nat := 118140960795 + 7697785 * 2 ^ 59
def prefixEnd_7697785 : Nat := 4983230072969 + 3 ^ 40 * 7697785 * 2
def baseEnd_7697785 : Nat := 3952663679970270114486037

theorem tailTrace_7697785 : CollatzResearch.WordTrace tailWord_7697785 prefixEnd_7697785 3952663679970270114486037 := by
  unfold tailWord_7697785
  simp only [CollatzResearch.WordTrace]
  refine ⟨280761284417247096856326809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187174189611498064570884539 280761284417247096856326809)
  ·
    refine ⟨210570963312935322642245107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280761284417247096856326809 210570963312935322642245107)
    ·
      refine ⟨315856444969402983963367661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210570963312935322642245107 315856444969402983963367661)
      ·
        refine ⟨118446166863526118986262873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315856444969402983963367661 118446166863526118986262873)
        ·
          refine ⟨88834625147644589239697155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118446166863526118986262873 88834625147644589239697155)
          ·
            refine ⟨133251937721466883859545733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88834625147644589239697155 133251937721466883859545733)
            ·
              refine ⟨24984738322775040723664825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 133251937721466883859545733 24984738322775040723664825)
              ·
                refine ⟨18738553742081280542748619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24984738322775040723664825 18738553742081280542748619)
                ·
                  refine ⟨28107830613121920814122929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18738553742081280542748619 28107830613121920814122929)
                  ·
                    refine ⟨21080872959841440610592197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28107830613121920814122929 21080872959841440610592197)
                    ·
                      refine ⟨3952663679970270114486037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21080872959841440610592197 3952663679970270114486037)
                      ·
                        rfl

theorem cell23_7697785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_7697785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697785 prefixEnd_7697785 := by exact prefixLift 7697785
  have htrace : WordTrace (prefixWord ++ tailWord_7697785) baseStart_7697785 baseEnd_7697785 := by
    simpa [prefixWord, tailWord_7697785, baseEnd_7697785] using wordTrace_append hprefix tailTrace_7697785
  have hstable : (prefixWord ++ tailWord_7697785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697785).length < 2 ^ (prefixWord ++ tailWord_7697785).sum := by decide
  have hdescent : baseEnd_7697785 < baseStart_7697785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697799 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 2, 4]
def baseStart_7697799 : Nat := 118140960795 + 7697799 * 2 ^ 59
def prefixEnd_7697799 : Nat := 4983230072969 + 3 ^ 40 * 7697799 * 2
def baseEnd_7697799 : Nat := 1317556956233144353236991

theorem tailTrace_7697799 : CollatzResearch.WordTrace tailWord_7697799 prefixEnd_7697799 1317556956233144353236991 := by
  unfold tailWord_7697799
  simp only [CollatzResearch.WordTrace]
  refine ⟨280761795039196377247336451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187174530026130918164890967 280761795039196377247336451)
  ·
    refine ⟨421142692558794565871004677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280761795039196377247336451 421142692558794565871004677)
    ·
      refine ⟨78964254854773981100813377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421142692558794565871004677 78964254854773981100813377)
      ·
        refine ⟨59223191141080485825610033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78964254854773981100813377 59223191141080485825610033)
        ·
          refine ⟨44417393355810364369207525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59223191141080485825610033 44417393355810364369207525)
          ·
            refine ⟨8328261254214443319226411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44417393355810364369207525 8328261254214443319226411)
            ·
              refine ⟨12492391881321664978839617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328261254214443319226411 12492391881321664978839617)
              ·
                refine ⟨9369293910991248734129713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12492391881321664978839617 9369293910991248734129713)
                ·
                  refine ⟨7026970433243436550597285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9369293910991248734129713 7026970433243436550597285)
                  ·
                    refine ⟨1317556956233144353236991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026970433243436550597285 1317556956233144353236991)
                    ·
                      rfl

theorem cell23_7697799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_7697799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697799 prefixEnd_7697799 := by exact prefixLift 7697799
  have htrace : WordTrace (prefixWord ++ tailWord_7697799) baseStart_7697799 baseEnd_7697799 := by
    simpa [prefixWord, tailWord_7697799, baseEnd_7697799] using wordTrace_append hprefix tailTrace_7697799
  have hstable : (prefixWord ++ tailWord_7697799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697799).length < 2 ^ (prefixWord ++ tailWord_7697799).sum := by decide
  have hdescent : baseEnd_7697799 < baseStart_7697799 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697816 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 2, 4]
def baseStart_7697816 : Nat := 118140960795 + 7697816 * 2 ^ 59
def prefixEnd_7697816 : Nat := 4983230072969 + 3 ^ 40 * 7697816 * 2
def baseEnd_7697816 : Nat := 1317559865956853164399465

theorem tailTrace_7697816 : CollatzResearch.WordTrace tailWord_7697816 prefixEnd_7697816 1317559865956853164399465 := by
  unfold tailWord_7697816
  simp only [CollatzResearch.WordTrace]
  refine ⟨140381207540067394575352651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187174943386756526100470201 140381207540067394575352651)
  ·
    refine ⟨210571811310101091863028977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140381207540067394575352651 210571811310101091863028977)
    ·
      refine ⟨157928858482575818897271733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210571811310101091863028977 157928858482575818897271733)
      ·
        refine ⟨14805830482741483021619225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157928858482575818897271733 14805830482741483021619225)
        ·
          refine ⟨11104372862056112266214419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14805830482741483021619225 11104372862056112266214419)
          ·
            refine ⟨16656559293084168399321629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104372862056112266214419 16656559293084168399321629)
            ·
              refine ⟨6246209734906563149745611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16656559293084168399321629 6246209734906563149745611)
              ·
                refine ⟨9369314602359844724618417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246209734906563149745611 9369314602359844724618417)
                ·
                  refine ⟨7026985951769883543463813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9369314602359844724618417 7026985951769883543463813)
                  ·
                    refine ⟨1317559865956853164399465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7026985951769883543463813 1317559865956853164399465)
                    ·
                      rfl

theorem cell23_7697816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 2, 4].length) (baseStart_7697816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697816 prefixEnd_7697816 := by exact prefixLift 7697816
  have htrace : WordTrace (prefixWord ++ tailWord_7697816) baseStart_7697816 baseEnd_7697816 := by
    simpa [prefixWord, tailWord_7697816, baseEnd_7697816] using wordTrace_append hprefix tailTrace_7697816
  have hstable : (prefixWord ++ tailWord_7697816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697816).length < 2 ^ (prefixWord ++ tailWord_7697816).sum := by decide
  have hdescent : baseEnd_7697816 < baseStart_7697816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697865 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_7697865 : Nat := 118140960795 + 7697865 * 2 ^ 59
def prefixEnd_7697865 : Nat := 4983230072969 + 3 ^ 40 * 7697865 * 2
def baseEnd_7697865 : Nat := 3952704758422629801485669

theorem tailTrace_7697865 : CollatzResearch.WordTrace tailWord_7697865 prefixEnd_7697865 3952704758422629801485669 := by
  unfold tailWord_7697865
  simp only [CollatzResearch.WordTrace]
  refine ⟨280764202256957270519239049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187176134837971513679492699 280764202256957270519239049)
  ·
    refine ⟨210573151692717952889429287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280764202256957270519239049 210573151692717952889429287)
    ·
      refine ⟨315859727539076929334143931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210573151692717952889429287 315859727539076929334143931)
      ·
        refine ⟨473789591308615394001215897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315859727539076929334143931 473789591308615394001215897)
        ·
          refine ⟨355342193481461545500911923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 473789591308615394001215897 355342193481461545500911923)
          ·
            refine ⟨533013290222192318251367885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355342193481461545500911923 533013290222192318251367885)
            ·
              refine ⟨199879983833322119344262957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533013290222192318251367885 199879983833322119344262957)
              ·
                refine ⟨74954993937495794754098609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199879983833322119344262957 74954993937495794754098609)
                ·
                  refine ⟨56216245453121846065573957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74954993937495794754098609 56216245453121846065573957)
                  ·
                    refine ⟨10540546022460346137295117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56216245453121846065573957 10540546022460346137295117)
                    ·
                      refine ⟨3952704758422629801485669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10540546022460346137295117 3952704758422629801485669)
                      ·
                        rfl

theorem cell23_7697865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_7697865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697865 prefixEnd_7697865 := by exact prefixLift 7697865
  have htrace : WordTrace (prefixWord ++ tailWord_7697865) baseStart_7697865 baseEnd_7697865 := by
    simpa [prefixWord, tailWord_7697865, baseEnd_7697865] using wordTrace_append hprefix tailTrace_7697865
  have hstable : (prefixWord ++ tailWord_7697865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697865).length < 2 ^ (prefixWord ++ tailWord_7697865).sum := by decide
  have hdescent : baseEnd_7697865 < baseStart_7697865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7697995 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_7697995 : Nat := 118140960795 + 7697995 * 2 ^ 59
def prefixEnd_7697995 : Nat := 4983230072969 + 3 ^ 40 * 7697995 * 2
def baseEnd_7697995 : Nat := 3952771510907714292860071

theorem tailTrace_7697995 : CollatzResearch.WordTrace tailWord_7697995 prefixEnd_7697995 3952771510907714292860071 := by
  unfold tailWord_7697995
  simp only [CollatzResearch.WordTrace]
  refine ⟨280768943746486302721471439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187179295830990868480980959 280768943746486302721471439)
  ·
    refine ⟨421153415619729454082207159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280768943746486302721471439 421153415619729454082207159)
    ·
      refine ⟨631730123429594181123310739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421153415619729454082207159 631730123429594181123310739)
      ·
        refine ⟨947595185144391271684966109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631730123429594181123310739 947595185144391271684966109)
        ·
          refine ⟨355348194429146726881862291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 947595185144391271684966109 355348194429146726881862291)
          ·
            refine ⟨533022291643720090322793437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355348194429146726881862291 533022291643720090322793437)
            ·
              refine ⟨199883359366395033871047539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 533022291643720090322793437 199883359366395033871047539)
              ·
                refine ⟨299825039049592550806571309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199883359366395033871047539 299825039049592550806571309)
                ·
                  refine ⟨112434389643597206552464241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 299825039049592550806571309 112434389643597206552464241)
                  ·
                    refine ⟨84325792232697904914348181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112434389643597206552464241 84325792232697904914348181)
                    ·
                      refine ⟨3952771510907714292860071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84325792232697904914348181 3952771510907714292860071)
                      ·
                        rfl

theorem cell23_7697995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_7697995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7697995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7697995 prefixEnd_7697995 := by exact prefixLift 7697995
  have htrace : WordTrace (prefixWord ++ tailWord_7697995) baseStart_7697995 baseEnd_7697995 := by
    simpa [prefixWord, tailWord_7697995, baseEnd_7697995] using wordTrace_append hprefix tailTrace_7697995
  have hstable : (prefixWord ++ tailWord_7697995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7697995).length < 2 ^ (prefixWord ++ tailWord_7697995).sum := by decide
  have hdescent : baseEnd_7697995 < baseStart_7697995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7697995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698030 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 1, 4]
def baseStart_7698030 : Nat := 118140960795 + 7698030 * 2 ^ 59
def prefixEnd_7698030 : Nat := 4983230072969 + 3 ^ 40 * 7698030 * 2
def baseEnd_7698030 : Nat := 1317596494243540551974137

theorem tailTrace_7698030 : CollatzResearch.WordTrace tailWord_7698030 prefixEnd_7698030 1317596494243540551974137 := by
  unfold tailWord_7698030
  simp only [CollatzResearch.WordTrace]
  refine ⟨35096277537669937962374443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187180146867573002465997029 35096277537669937962374443)
  ·
    refine ⟨52644416306504906943561665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35096277537669937962374443 52644416306504906943561665)
    ·
      refine ⟨39483312229878680207671249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52644416306504906943561665 39483312229878680207671249)
      ·
        refine ⟨29612484172409010155753437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39483312229878680207671249 29612484172409010155753437)
        ·
          refine ⟨11104681564653378808407539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29612484172409010155753437 11104681564653378808407539)
          ·
            refine ⟨16657022346980068212611309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104681564653378808407539 16657022346980068212611309)
            ·
              refine ⟨6246383380117525579729241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16657022346980068212611309 6246383380117525579729241)
              ·
                refine ⟨4684787535088144184796931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6246383380117525579729241 4684787535088144184796931)
                ·
                  refine ⟨7027181302632216277195397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684787535088144184796931 7027181302632216277195397)
                  ·
                    refine ⟨1317596494243540551974137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027181302632216277195397 1317596494243540551974137)
                    ·
                      rfl

theorem cell23_7698030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_7698030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698030 prefixEnd_7698030 := by exact prefixLift 7698030
  have htrace : WordTrace (prefixWord ++ tailWord_7698030) baseStart_7698030 baseEnd_7698030 := by
    simpa [prefixWord, tailWord_7698030, baseEnd_7698030] using wordTrace_append hprefix tailTrace_7698030
  have hstable : (prefixWord ++ tailWord_7698030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698030).length < 2 ^ (prefixWord ++ tailWord_7698030).sum := by decide
  have hdescent : baseEnd_7698030 < baseStart_7698030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698056 : List Nat := [2, 1, 3, 5, 1, 1, 1, 1, 3, 5]
def baseStart_7698056 : Nat := 118140960795 + 7698056 * 2 ^ 59
def prefixEnd_7698056 : Nat := 4983230072969 + 3 ^ 40 * 7698056 * 2
def baseEnd_7698056 : Nat := 1317600944409212851399097

theorem tailTrace_7698056 : CollatzResearch.WordTrace tailWord_7698056 prefixEnd_7698056 1317600944409212851399097 := by
  unfold tailWord_7698056
  simp only [CollatzResearch.WordTrace]
  refine ⟨140385584299632655069721011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187180779066176873426294681 140385584299632655069721011)
  ·
    refine ⟨210578376449448982604581517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140385584299632655069721011 210578376449448982604581517)
    ·
      refine ⟨78966891168543368476718069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210578376449448982604581517 78966891168543368476718069)
      ·
        refine ⟨7403146047050940794692319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 78966891168543368476718069 7403146047050940794692319)
        ·
          refine ⟨11104719070576411192038479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403146047050940794692319 11104719070576411192038479)
          ·
            refine ⟨16657078605864616788057719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11104719070576411192038479 16657078605864616788057719)
            ·
              refine ⟨24985617908796925182086579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16657078605864616788057719 24985617908796925182086579)
              ·
                refine ⟨37478426863195387773129869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24985617908796925182086579 37478426863195387773129869)
                ·
                  refine ⟨14054410073698270414923701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37478426863195387773129869 14054410073698270414923701)
                  ·
                    refine ⟨1317600944409212851399097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14054410073698270414923701 1317600944409212851399097)
                    ·
                      rfl

theorem cell23_7698056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 1, 3, 5].length) (baseStart_7698056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698056 prefixEnd_7698056 := by exact prefixLift 7698056
  have htrace : WordTrace (prefixWord ++ tailWord_7698056) baseStart_7698056 baseEnd_7698056 := by
    simpa [prefixWord, tailWord_7698056, baseEnd_7698056] using wordTrace_append hprefix tailTrace_7698056
  have hstable : (prefixWord ++ tailWord_7698056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698056).length < 2 ^ (prefixWord ++ tailWord_7698056).sum := by decide
  have hdescent : baseEnd_7698056 < baseStart_7698056 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698093 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_7698093 : Nat := 118140960795 + 7698093 * 2 ^ 59
def prefixEnd_7698093 : Nat := 4983230072969 + 3 ^ 40 * 7698093 * 2
def baseEnd_7698093 : Nat := 3952821832011854909434621

theorem tailTrace_7698093 : CollatzResearch.WordTrace tailWord_7698093 prefixEnd_7698093 3952821832011854909434621 := by
  unfold tailWord_7698093
  simp only [CollatzResearch.WordTrace]
  refine ⟨280772518100131265458538933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187181678733420843639025955 280772518100131265458538933)
  ·
    refine ⟨26322423571887306136738025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280772518100131265458538933 26322423571887306136738025)
    ·
      refine ⟨19741817678915479602553519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26322423571887306136738025 19741817678915479602553519)
      ·
        refine ⟨29612726518373219403830279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19741817678915479602553519 29612726518373219403830279)
        ·
          refine ⟨44419089777559829105745419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29612726518373219403830279 44419089777559829105745419)
          ·
            refine ⟨66628634666339743658618129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44419089777559829105745419 66628634666339743658618129)
            ·
              refine ⟨49971475999754807743963597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66628634666339743658618129 49971475999754807743963597)
              ·
                refine ⟨18739303499908052903986349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49971475999754807743963597 18739303499908052903986349)
                ·
                  refine ⟨7027238812465519838994881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18739303499908052903986349 7027238812465519838994881)
                  ·
                    refine ⟨5270429109349139879246161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7027238812465519838994881 5270429109349139879246161)
                    ·
                      refine ⟨3952821832011854909434621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270429109349139879246161 3952821832011854909434621)
                      ·
                        rfl

theorem cell23_7698093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_7698093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698093 prefixEnd_7698093 := by exact prefixLift 7698093
  have htrace : WordTrace (prefixWord ++ tailWord_7698093) baseStart_7698093 baseEnd_7698093 := by
    simpa [prefixWord, tailWord_7698093, baseEnd_7698093] using wordTrace_append hprefix tailTrace_7698093
  have hstable : (prefixWord ++ tailWord_7698093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698093).length < 2 ^ (prefixWord ++ tailWord_7698093).sum := by decide
  have hdescent : baseEnd_7698093 < baseStart_7698093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698112 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 2, 7]
def baseStart_7698112 : Nat := 118140960795 + 7698112 * 2 ^ 59
def prefixEnd_7698112 : Nat := 4983230072969 + 3 ^ 40 * 7698112 * 2
def baseEnd_7698112 : Nat := 1317610529381430111699011

theorem tailTrace_7698112 : CollatzResearch.WordTrace tailWord_7698112 prefixEnd_7698112 1317610529381430111699011 := by
  unfold tailWord_7698112
  simp only [CollatzResearch.WordTrace]
  refine ⟨140386605543531215851740295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187182140724708287802320393 140386605543531215851740295)
  ·
    refine ⟨210579908315296823777610443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140386605543531215851740295 210579908315296823777610443)
    ·
      refine ⟨315869862472945235666415665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210579908315296823777610443 315869862472945235666415665)
      ·
        refine ⟨236902396854708926749811749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315869862472945235666415665 236902396854708926749811749)
        ·
          refine ⟨44419199410257923765589703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236902396854708926749811749 44419199410257923765589703)
          ·
            refine ⟨66628799115386885648384555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44419199410257923765589703 66628799115386885648384555)
            ·
              refine ⟨99943198673080328472576833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66628799115386885648384555 99943198673080328472576833)
              ·
                refine ⟨74957399004810246354432625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99943198673080328472576833 74957399004810246354432625)
                ·
                  refine ⟨56218049253607684765824469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74957399004810246354432625 56218049253607684765824469)
                  ·
                    refine ⟨1317610529381430111699011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56218049253607684765824469 1317610529381430111699011)
                    ·
                      rfl

theorem cell23_7698112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 2, 7].length) (baseStart_7698112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698112 prefixEnd_7698112 := by exact prefixLift 7698112
  have htrace : WordTrace (prefixWord ++ tailWord_7698112) baseStart_7698112 baseEnd_7698112 := by
    simpa [prefixWord, tailWord_7698112, baseEnd_7698112] using wordTrace_append hprefix tailTrace_7698112
  have hstable : (prefixWord ++ tailWord_7698112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698112).length < 2 ^ (prefixWord ++ tailWord_7698112).sum := by decide
  have hdescent : baseEnd_7698112 < baseStart_7698112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698114 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_7698114 : Nat := 118140960795 + 7698114 * 2 ^ 59
def prefixEnd_7698114 : Nat := 4983230072969 + 3 ^ 40 * 7698114 * 2
def baseEnd_7698114 : Nat := 3952832615105599327272025

theorem tailTrace_7698114 : CollatzResearch.WordTrace tailWord_7698114 prefixEnd_7698114 3952832615105599327272025 := by
  unfold tailWord_7698114
  simp only [CollatzResearch.WordTrace]
  refine ⟨70193321008263796511263349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187182189355370124030035597 70193321008263796511263349)
  ·
    refine ⟨6580623844524730922930939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 70193321008263796511263349 6580623844524730922930939)
    ·
      refine ⟨9870935766787096384396409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6580623844524730922930939 9870935766787096384396409)
      ·
        refine ⟨7403201825090322288297307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9870935766787096384396409 7403201825090322288297307)
        ·
          refine ⟨11104802737635483432445961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7403201825090322288297307 11104802737635483432445961)
          ·
            refine ⟨8328602053226612574334471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11104802737635483432445961 8328602053226612574334471)
            ·
              refine ⟨12492903079839918861501707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328602053226612574334471 12492903079839918861501707)
              ·
                refine ⟨18739354619759878292252561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12492903079839918861501707 18739354619759878292252561)
                ·
                  refine ⟨14054515964819908719189421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18739354619759878292252561 14054515964819908719189421)
                  ·
                    refine ⟨5270443486807465769696033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14054515964819908719189421 5270443486807465769696033)
                    ·
                      refine ⟨3952832615105599327272025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270443486807465769696033 3952832615105599327272025)
                      ·
                        rfl

theorem cell23_7698114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_7698114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698114 prefixEnd_7698114 := by exact prefixLift 7698114
  have htrace : WordTrace (prefixWord ++ tailWord_7698114) baseStart_7698114 baseEnd_7698114 := by
    simpa [prefixWord, tailWord_7698114, baseEnd_7698114] using wordTrace_append hprefix tailTrace_7698114
  have hstable : (prefixWord ++ tailWord_7698114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698114).length < 2 ^ (prefixWord ++ tailWord_7698114).sum := by decide
  have hdescent : baseEnd_7698114 < baseStart_7698114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698126 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_7698126 : Nat := 118140960795 + 7698126 * 2 ^ 59
def prefixEnd_7698126 : Nat := 4983230072969 + 3 ^ 40 * 7698126 * 2
def baseEnd_7698126 : Nat := 3952838776873453280321969

theorem tailTrace_7698126 : CollatzResearch.WordTrace tailWord_7698126 prefixEnd_7698126 3952838776873453280321969 := by
  unfold tailWord_7698126
  simp only [CollatzResearch.WordTrace]
  refine ⟨35096715213626464011811279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 187182481139341141396326821 35096715213626464011811279)
  ·
    refine ⟨52645072820439696017716919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35096715213626464011811279 52645072820439696017716919)
    ·
      refine ⟨78967609230659544026575379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52645072820439696017716919 78967609230659544026575379)
      ·
        refine ⟨118451413845989316039863069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78967609230659544026575379 118451413845989316039863069)
        ·
          refine ⟨44419280192245993514948651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118451413845989316039863069 44419280192245993514948651)
          ·
            refine ⟨66628920288368990272422977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44419280192245993514948651 66628920288368990272422977)
            ·
              refine ⟨49971690216276742704317233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66628920288368990272422977 49971690216276742704317233)
              ·
                refine ⟨37478767662207557028237925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49971690216276742704317233 37478767662207557028237925)
                ·
                  refine ⟨7027268936663916942794611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37478767662207557028237925 7027268936663916942794611)
                  ·
                    refine ⟨10540903404995875414191917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7027268936663916942794611 10540903404995875414191917)
                    ·
                      refine ⟨3952838776873453280321969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10540903404995875414191917 3952838776873453280321969)
                      ·
                        rfl

theorem cell23_7698126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_7698126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698126 prefixEnd_7698126 := by exact prefixLift 7698126
  have htrace : WordTrace (prefixWord ++ tailWord_7698126) baseStart_7698126 baseEnd_7698126 := by
    simpa [prefixWord, tailWord_7698126, baseEnd_7698126] using wordTrace_append hprefix tailTrace_7698126
  have hstable : (prefixWord ++ tailWord_7698126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698126).length < 2 ^ (prefixWord ++ tailWord_7698126).sum := by decide
  have hdescent : baseEnd_7698126 < baseStart_7698126 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698130 : List Nat := [3, 2, 2, 2, 2, 3, 2, 1, 1, 2, 3]
def baseStart_7698130 : Nat := 118140960795 + 7698130 * 2 ^ 59
def prefixEnd_7698130 : Nat := 4983230072969 + 3 ^ 40 * 7698130 * 2
def baseEnd_7698130 : Nat := 3952840830796071264671951

theorem tailTrace_7698130 : CollatzResearch.WordTrace tailWord_7698130 prefixEnd_7698130 3952840830796071264671951 := by
  unfold tailWord_7698130
  simp only [CollatzResearch.WordTrace]
  refine ⟨70193466900249305194408961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187182578400664813851757229 70193466900249305194408961)
  ·
    refine ⟨52645100175186978895806721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70193466900249305194408961 52645100175186978895806721)
    ·
      refine ⟨39483825131390234171855041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52645100175186978895806721 39483825131390234171855041)
      ·
        refine ⟨29612868848542675628891281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39483825131390234171855041 29612868848542675628891281)
        ·
          refine ⟨22209651636407006721668461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29612868848542675628891281 22209651636407006721668461)
          ·
            refine ⟨8328619363652627520625673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22209651636407006721668461 8328619363652627520625673)
            ·
              refine ⟨6246464522739470640469255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8328619363652627520625673 6246464522739470640469255)
              ·
                refine ⟨9369696784109205960703883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246464522739470640469255 9369696784109205960703883)
                ·
                  refine ⟨14054545176163808941055825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9369696784109205960703883 14054545176163808941055825)
                  ·
                    refine ⟨10540908882122856705791869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14054545176163808941055825 10540908882122856705791869)
                    ·
                      refine ⟨3952840830796071264671951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10540908882122856705791869 3952840830796071264671951)
                      ·
                        rfl

theorem cell23_7698130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_7698130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698130 prefixEnd_7698130 := by exact prefixLift 7698130
  have htrace : WordTrace (prefixWord ++ tailWord_7698130) baseStart_7698130 baseEnd_7698130 := by
    simpa [prefixWord, tailWord_7698130, baseEnd_7698130] using wordTrace_append hprefix tailTrace_7698130
  have hstable : (prefixWord ++ tailWord_7698130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698130).length < 2 ^ (prefixWord ++ tailWord_7698130).sum := by decide
  have hdescent : baseEnd_7698130 < baseStart_7698130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698253 : List Nat := [1, 6, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7698253 : Nat := 118140960795 + 7698253 * 2 ^ 59
def prefixEnd_7698253 : Nat := 4983230072969 + 3 ^ 40 * 7698253 * 2
def baseEnd_7698253 : Nat := 1317634662972191427811295

theorem tailTrace_7698253 : CollatzResearch.WordTrace tailWord_7698253 prefixEnd_7698253 1317634662972191427811295 := by
  unfold tailWord_7698253
  simp only [CollatzResearch.WordTrace]
  refine ⟨280778353779551612784363413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187185569186367741856242275 280778353779551612784363413)
  ·
    refine ⟨13161485333416481849267035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 280778353779551612784363413 13161485333416481849267035)
    ·
      refine ⟨19742228000124722773900553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13161485333416481849267035 19742228000124722773900553)
      ·
        refine ⟨14806671000093542080425415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19742228000124722773900553 14806671000093542080425415)
        ·
          refine ⟨22210006500140313120638123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14806671000093542080425415 22210006500140313120638123)
          ·
            refine ⟨33315009750210469680957185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22210006500140313120638123 33315009750210469680957185)
            ·
              refine ⟨24986257312657852260717889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33315009750210469680957185 24986257312657852260717889)
              ·
                refine ⟨18739692984493389195538417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24986257312657852260717889 18739692984493389195538417)
                ·
                  refine ⟨14054769738370041896653813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18739692984493389195538417 14054769738370041896653813)
                  ·
                    refine ⟨1317634662972191427811295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14054769738370041896653813 1317634662972191427811295)
                    ·
                      rfl

theorem cell23_7698253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7698253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698253 prefixEnd_7698253 := by exact prefixLift 7698253
  have htrace : WordTrace (prefixWord ++ tailWord_7698253) baseStart_7698253 baseEnd_7698253 := by
    simpa [prefixWord, tailWord_7698253, baseEnd_7698253] using wordTrace_append hprefix tailTrace_7698253
  have hstable : (prefixWord ++ tailWord_7698253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698253).length < 2 ^ (prefixWord ++ tailWord_7698253).sum := by decide
  have hdescent : baseEnd_7698253 < baseStart_7698253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698256 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 2, 4, 2]
def baseStart_7698256 : Nat := 118140960795 + 7698256 * 2 ^ 59
def prefixEnd_7698256 : Nat := 4983230072969 + 3 ^ 40 * 7698256 * 2
def baseEnd_7698256 : Nat := 3952905529358537771696371

theorem tailTrace_7698256 : CollatzResearch.WordTrace tailWord_7698256 prefixEnd_7698256 3952905529358537771696371 := by
  unfold tailWord_7698256
  simp only [CollatzResearch.WordTrace]
  refine ⟨140389231599270372148361311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187185642132360496197815081 140389231599270372148361311)
  ·
    refine ⟨210583847398905558222541967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140389231599270372148361311 210583847398905558222541967)
    ·
      refine ⟨315875771098358337333812951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210583847398905558222541967 315875771098358337333812951)
      ·
        refine ⟨473813656647537506000719427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315875771098358337333812951 473813656647537506000719427)
        ·
          refine ⟨710720484971306259001079141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473813656647537506000719427 710720484971306259001079141)
          ·
            refine ⟨133260090932119923562702339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 710720484971306259001079141 133260090932119923562702339)
            ·
              refine ⟨199890136398179885344053509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 133260090932119923562702339 199890136398179885344053509)
              ·
                refine ⟨37479400574658728502010033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199890136398179885344053509 37479400574658728502010033)
                ·
                  refine ⟨28109550430994046376507525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37479400574658728502010033 28109550430994046376507525)
                  ·
                    refine ⟨5270540705811383695595161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28109550430994046376507525 5270540705811383695595161)
                    ·
                      refine ⟨3952905529358537771696371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270540705811383695595161 3952905529358537771696371)
                      ·
                        rfl

theorem cell23_7698256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 4, 2].length) (baseStart_7698256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698256 prefixEnd_7698256 := by exact prefixLift 7698256
  have htrace : WordTrace (prefixWord ++ tailWord_7698256) baseStart_7698256 baseEnd_7698256 := by
    simpa [prefixWord, tailWord_7698256, baseEnd_7698256] using wordTrace_append hprefix tailTrace_7698256
  have hstable : (prefixWord ++ tailWord_7698256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698256).length < 2 ^ (prefixWord ++ tailWord_7698256).sum := by decide
  have hdescent : baseEnd_7698256 < baseStart_7698256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698259 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 3]
def baseStart_7698259 : Nat := 118140960795 + 7698259 * 2 ^ 59
def prefixEnd_7698259 : Nat := 4983230072969 + 3 ^ 40 * 7698259 * 2
def baseEnd_7698259 : Nat := 3952907069800501259958857

theorem tailTrace_7698259 : CollatzResearch.WordTrace tailWord_7698259 prefixEnd_7698259 3952907069800501259958857 := by
  unfold tailWord_7698259
  simp only [CollatzResearch.WordTrace]
  refine ⟨280778572617529875809081831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187185715078353250539387887 280778572617529875809081831)
  ·
    refine ⟨421167858926294813713622747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280778572617529875809081831 421167858926294813713622747)
    ·
      refine ⟨631751788389442220570434121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421167858926294813713622747 631751788389442220570434121)
      ·
        refine ⟨473813841292081665427825591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 631751788389442220570434121 473813841292081665427825591)
        ·
          refine ⟨710720761938122498141738387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 473813841292081665427825591 710720761938122498141738387)
          ·
            refine ⟨1066081142907183747212607581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 710720761938122498141738387 1066081142907183747212607581)
            ·
              refine ⟨399780428590193905204727843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1066081142907183747212607581 399780428590193905204727843)
              ·
                refine ⟨599670642885290857807091765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 399780428590193905204727843 599670642885290857807091765)
                ·
                  refine ⟨56219122770496017919414853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 599670642885290857807091765 56219122770496017919414853)
                  ·
                    refine ⟨10541085519468003359890285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56219122770496017919414853 10541085519468003359890285)
                    ·
                      refine ⟨3952907069800501259958857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10541085519468003359890285 3952907069800501259958857)
                      ·
                        rfl

theorem cell23_7698259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_7698259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698259 prefixEnd_7698259 := by exact prefixLift 7698259
  have htrace : WordTrace (prefixWord ++ tailWord_7698259) baseStart_7698259 baseEnd_7698259 := by
    simpa [prefixWord, tailWord_7698259, baseEnd_7698259] using wordTrace_append hprefix tailTrace_7698259
  have hstable : (prefixWord ++ tailWord_7698259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698259).length < 2 ^ (prefixWord ++ tailWord_7698259).sum := by decide
  have hdescent : baseEnd_7698259 < baseStart_7698259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698266 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_7698266 : Nat := 118140960795 + 7698266 * 2 ^ 59
def prefixEnd_7698266 : Nat := 4983230072969 + 3 ^ 40 * 7698266 * 2
def baseEnd_7698266 : Nat := 1317636888055027577523775

theorem tailTrace_7698266 : CollatzResearch.WordTrace tailWord_7698266 prefixEnd_7698266 1317636888055027577523775 := by
  unfold tailWord_7698266
  simp only [CollatzResearch.WordTrace]
  refine ⟨70194706982126129001146663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187185885285669677336391101 70194706982126129001146663)
  ·
    refine ⟨105292060473189193501719995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70194706982126129001146663 105292060473189193501719995)
    ·
      refine ⟨157938090709783790252579993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105292060473189193501719995 157938090709783790252579993)
      ·
        refine ⟨118453568032337842689434995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157938090709783790252579993 118453568032337842689434995)
        ·
          refine ⟨177680352048506764034152493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118453568032337842689434995 177680352048506764034152493)
          ·
            refine ⟨66630132018190036512807185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177680352048506764034152493 66630132018190036512807185)
            ·
              refine ⟨49972599013642527384605389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66630132018190036512807185 49972599013642527384605389)
              ·
                refine ⟨18739724630115947769227021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49972599013642527384605389 18739724630115947769227021)
                ·
                  refine ⟨7027396736293480413460133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18739724630115947769227021 7027396736293480413460133)
                  ·
                    refine ⟨1317636888055027577523775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7027396736293480413460133 1317636888055027577523775)
                    ·
                      rfl

theorem cell23_7698266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_7698266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698266 prefixEnd_7698266 := by exact prefixLift 7698266
  have htrace : WordTrace (prefixWord ++ tailWord_7698266) baseStart_7698266 baseEnd_7698266 := by
    simpa [prefixWord, tailWord_7698266, baseEnd_7698266] using wordTrace_append hprefix tailTrace_7698266
  have hstable : (prefixWord ++ tailWord_7698266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698266).length < 2 ^ (prefixWord ++ tailWord_7698266).sum := by decide
  have hdescent : baseEnd_7698266 < baseStart_7698266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698333 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_7698333 : Nat := 118140960795 + 7698333 * 2 ^ 59
def prefixEnd_7698333 : Nat := 4983230072969 + 3 ^ 40 * 7698333 * 2
def baseEnd_7698333 : Nat := 3952945067368933970433517

theorem tailTrace_7698333 : CollatzResearch.WordTrace tailWord_7698333 prefixEnd_7698333 3952945067368933970433517 := by
  unfold tailWord_7698333
  simp only [CollatzResearch.WordTrace]
  refine ⟨280781271619261786447275653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187187514412841190964850435 280781271619261786447275653)
  ·
    refine ⟨52646488428611584958864185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280781271619261786447275653 52646488428611584958864185)
    ·
      refine ⟨39484866321458688719148139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52646488428611584958864185 39484866321458688719148139)
      ·
        refine ⟨59227299482188033078722209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39484866321458688719148139 59227299482188033078722209)
        ·
          refine ⟨44420474611641024809041657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59227299482188033078722209 44420474611641024809041657)
          ·
            refine ⟨33315355958730768606781243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44420474611641024809041657 33315355958730768606781243)
            ·
              refine ⟨49973033938096152910171865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33315355958730768606781243 49973033938096152910171865)
              ·
                refine ⟨37479775453572114682628899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49973033938096152910171865 37479775453572114682628899)
                ·
                  refine ⟨56219663180358172023943349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37479775453572114682628899 56219663180358172023943349)
                  ·
                    refine ⟨5270593423158578627244689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56219663180358172023943349 5270593423158578627244689)
                    ·
                      refine ⟨3952945067368933970433517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270593423158578627244689 3952945067368933970433517)
                      ·
                        rfl

theorem cell23_7698333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_7698333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698333 prefixEnd_7698333 := by exact prefixLift 7698333
  have htrace : WordTrace (prefixWord ++ tailWord_7698333) baseStart_7698333 baseEnd_7698333 := by
    simpa [prefixWord, tailWord_7698333, baseEnd_7698333] using wordTrace_append hprefix tailTrace_7698333
  have hstable : (prefixWord ++ tailWord_7698333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698333).length < 2 ^ (prefixWord ++ tailWord_7698333).sum := by decide
  have hdescent : baseEnd_7698333 < baseStart_7698333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698343 : List Nat := [1, 1, 6, 1, 2, 1, 1, 4, 1, 5]
def baseStart_7698343 : Nat := 118140960795 + 7698343 * 2 ^ 59
def prefixEnd_7698343 : Nat := 4983230072969 + 3 ^ 40 * 7698343 * 2
def baseEnd_7698343 : Nat := 1317650067391826310436157

theorem tailTrace_7698343 : CollatzResearch.WordTrace tailWord_7698343 prefixEnd_7698343 1317650067391826310436157 := by
  unfold tailWord_7698343
  simp only [CollatzResearch.WordTrace]
  refine ⟨280781636349225558155139683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187187757566150372103426455 280781636349225558155139683)
  ·
    refine ⟨421172454523838337232709525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280781636349225558155139683 421172454523838337232709525)
    ·
      refine ⟨19742458805804922057783259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 421172454523838337232709525 19742458805804922057783259)
      ·
        refine ⟨29613688208707383086674889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742458805804922057783259 29613688208707383086674889)
        ·
          refine ⟨22210266156530537315006167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29613688208707383086674889 22210266156530537315006167)
          ·
            refine ⟨33315399234795805972509251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22210266156530537315006167 33315399234795805972509251)
            ·
              refine ⟨49973098852193708958763877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33315399234795805972509251 49973098852193708958763877)
              ·
                refine ⟨9369956034786320429768227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49973098852193708958763877 9369956034786320429768227)
                ·
                  refine ⟨14054934052179480644652341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9369956034786320429768227 14054934052179480644652341)
                  ·
                    refine ⟨1317650067391826310436157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14054934052179480644652341 1317650067391826310436157)
                    ·
                      rfl

theorem cell23_7698343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_7698343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698343 prefixEnd_7698343 := by exact prefixLift 7698343
  have htrace : WordTrace (prefixWord ++ tailWord_7698343) baseStart_7698343 baseEnd_7698343 := by
    simpa [prefixWord, tailWord_7698343, baseEnd_7698343] using wordTrace_append hprefix tailTrace_7698343
  have hstable : (prefixWord ++ tailWord_7698343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698343).length < 2 ^ (prefixWord ++ tailWord_7698343).sum := by decide
  have hdescent : baseEnd_7698343 < baseStart_7698343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698357 : List Nat := [1, 3, 3, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_7698357 : Nat := 118140960795 + 7698357 * 2 ^ 59
def prefixEnd_7698357 : Nat := 4983230072969 + 3 ^ 40 * 7698357 * 2
def baseEnd_7698357 : Nat := 3952957390904641876533407

theorem tailTrace_7698357 : CollatzResearch.WordTrace tailWord_7698357 prefixEnd_7698357 3952957390904641876533407 := by
  unfold tailWord_7698357
  simp only [CollatzResearch.WordTrace]
  refine ⟨280782146971174838546149325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187188097980783225697432883 280782146971174838546149325)
  ·
    refine ⟨105293305114190564454805997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280782146971174838546149325 105293305114190564454805997)
    ·
      refine ⟨39484989417821461670552249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105293305114190564454805997 39484989417821461670552249)
      ·
        refine ⟨29613742063366096252914187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39484989417821461670552249 29613742063366096252914187)
        ·
          refine ⟨44420613095049144379371281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29613742063366096252914187 44420613095049144379371281)
          ·
            refine ⟨33315459821286858284528461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44420613095049144379371281 33315459821286858284528461)
            ·
              refine ⟨12493297432982571856698173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33315459821286858284528461 12493297432982571856698173)
              ·
                refine ⟨4684986537368464446261815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12493297432982571856698173 4684986537368464446261815)
                ·
                  refine ⟨7027479806052696669392723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4684986537368464446261815 7027479806052696669392723)
                  ·
                    refine ⟨10541219709079045004089085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7027479806052696669392723 10541219709079045004089085)
                    ·
                      refine ⟨3952957390904641876533407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10541219709079045004089085 3952957390904641876533407)
                      ·
                        rfl

theorem cell23_7698357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_7698357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698357 prefixEnd_7698357 := by exact prefixLift 7698357
  have htrace : WordTrace (prefixWord ++ tailWord_7698357) baseStart_7698357 baseEnd_7698357 := by
    simpa [prefixWord, tailWord_7698357, baseEnd_7698357] using wordTrace_append hprefix tailTrace_7698357
  have hstable : (prefixWord ++ tailWord_7698357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698357).length < 2 ^ (prefixWord ++ tailWord_7698357).sum := by decide
  have hdescent : baseEnd_7698357 < baseStart_7698357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698363 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 7, 2, 2]
def baseStart_7698363 : Nat := 118140960795 + 7698363 * 2 ^ 59
def prefixEnd_7698363 : Nat := 4983230072969 + 3 ^ 40 * 7698363 * 2
def baseEnd_7698363 : Nat := 3952960471788568853058379

theorem tailTrace_7698363 : CollatzResearch.WordTrace tailWord_7698363 prefixEnd_7698363 3952960471788568853058379 := by
  unfold tailWord_7698363
  simp only [CollatzResearch.WordTrace]
  refine ⟨280782365809153101570867743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187188243872768734380578495 280782365809153101570867743)
  ·
    refine ⟨421173548713729652356301615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280782365809153101570867743 421173548713729652356301615)
    ·
      refine ⟨631760323070594478534452423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 421173548713729652356301615 631760323070594478534452423)
      ·
        refine ⟨947640484605891717801678635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 631760323070594478534452423 947640484605891717801678635)
        ·
          refine ⟨1421460726908837576702517953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 947640484605891717801678635 1421460726908837576702517953)
          ·
            refine ⟨1066095545181628182526888465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1421460726908837576702517953 1066095545181628182526888465)
            ·
              refine ⟨799571658886221136895166349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066095545181628182526888465 799571658886221136895166349)
              ·
                refine ⟨299839372082332926335687381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 799571658886221136895166349 299839372082332926335687381)
                ·
                  refine ⟨7027485283179677960992673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 299839372082332926335687381 7027485283179677960992673)
                  ·
                    refine ⟨5270613962384758470744505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7027485283179677960992673 5270613962384758470744505)
                    ·
                      refine ⟨3952960471788568853058379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270613962384758470744505 3952960471788568853058379)
                      ·
                        rfl

theorem cell23_7698363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 2, 2].length) (baseStart_7698363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698363 prefixEnd_7698363 := by exact prefixLift 7698363
  have htrace : WordTrace (prefixWord ++ tailWord_7698363) baseStart_7698363 baseEnd_7698363 := by
    simpa [prefixWord, tailWord_7698363, baseEnd_7698363] using wordTrace_append hprefix tailTrace_7698363
  have hstable : (prefixWord ++ tailWord_7698363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698363).length < 2 ^ (prefixWord ++ tailWord_7698363).sum := by decide
  have hdescent : baseEnd_7698363 < baseStart_7698363 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698376 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 1, 1, 6]
def baseStart_7698376 : Nat := 118140960795 + 7698376 * 2 ^ 59
def prefixEnd_7698376 : Nat := 4983230072969 + 3 ^ 40 * 7698376 * 2
def baseEnd_7698376 : Nat := 3952967147037077302195819

theorem tailTrace_7698376 : CollatzResearch.WordTrace tailWord_7698376 prefixEnd_7698376 3952967147037077302195819 := by
  unfold tailWord_7698376
  simp only [CollatzResearch.WordTrace]
  refine ⟨140391419979053002395545491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187188559972070669860727321 140391419979053002395545491)
  ·
    refine ⟨210587129968579503593318237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140391419979053002395545491 210587129968579503593318237)
    ·
      refine ⟨78970173738217313847494339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210587129968579503593318237 78970173738217313847494339)
      ·
        refine ⟨118455260607325970771241509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78970173738217313847494339 118455260607325970771241509)
        ·
          refine ⟨22210361363873619519607783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118455260607325970771241509 22210361363873619519607783)
          ·
            refine ⟨33315542045810429279411675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22210361363873619519607783 33315542045810429279411675)
            ·
              refine ⟨49973313068715643919117513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33315542045810429279411675 49973313068715643919117513)
              ·
                refine ⟨37479984801536732939338135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49973313068715643919117513 37479984801536732939338135)
                ·
                  refine ⟨56219977202305099409007203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37479984801536732939338135 56219977202305099409007203)
                  ·
                    refine ⟨84329965803457649113510805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56219977202305099409007203 84329965803457649113510805)
                    ·
                      refine ⟨3952967147037077302195819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84329965803457649113510805 3952967147037077302195819)
                      ·
                        rfl

theorem cell23_7698376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_7698376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698376 prefixEnd_7698376 := by exact prefixLift 7698376
  have htrace : WordTrace (prefixWord ++ tailWord_7698376) baseStart_7698376 baseEnd_7698376 := by
    simpa [prefixWord, tailWord_7698376, baseEnd_7698376] using wordTrace_append hprefix tailTrace_7698376
  have hstable : (prefixWord ++ tailWord_7698376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698376).length < 2 ^ (prefixWord ++ tailWord_7698376).sum := by decide
  have hdescent : baseEnd_7698376 < baseStart_7698376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698397 : List Nat := [1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_7698397 : Nat := 118140960795 + 7698397 * 2 ^ 59
def prefixEnd_7698397 : Nat := 4983230072969 + 3 ^ 40 * 7698397 * 2
def baseEnd_7698397 : Nat := 3952977930130821720033223

theorem tailTrace_7698397 : CollatzResearch.WordTrace tailWord_7698397 prefixEnd_7698397 3952977930130821720033223 := by
  unfold tailWord_7698397
  simp only [CollatzResearch.WordTrace]
  refine ⟨280783605891029925377605445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187189070594019950251736963 280783605891029925377605445)
  ·
    refine ⟨52646926104568111008301021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280783605891029925377605445 52646926104568111008301021)
    ·
      refine ⟨19742597289213041628112883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52646926104568111008301021 19742597289213041628112883)
      ·
        refine ⟨29613895933819562442169325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742597289213041628112883 29613895933819562442169325)
        ·
          refine ⟨11105210975182335915813497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29613895933819562442169325 11105210975182335915813497)
          ·
            refine ⟨8328908231386751936860123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11105210975182335915813497 8328908231386751936860123)
            ·
              refine ⟨12493362347080127905290185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8328908231386751936860123 12493362347080127905290185)
              ·
                refine ⟨9370021760310095928967639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12493362347080127905290185 9370021760310095928967639)
                ·
                  refine ⟨14055032640465143893451459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370021760310095928967639 14055032640465143893451459)
                  ·
                    refine ⟨21082548960697715840177189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14055032640465143893451459 21082548960697715840177189)
                    ·
                      refine ⟨3952977930130821720033223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21082548960697715840177189 3952977930130821720033223)
                      ·
                        rfl

theorem cell23_7698397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_7698397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698397 prefixEnd_7698397 := by exact prefixLift 7698397
  have htrace : WordTrace (prefixWord ++ tailWord_7698397) baseStart_7698397 baseEnd_7698397 := by
    simpa [prefixWord, tailWord_7698397, baseEnd_7698397] using wordTrace_append hprefix tailTrace_7698397
  have hstable : (prefixWord ++ tailWord_7698397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698397).length < 2 ^ (prefixWord ++ tailWord_7698397).sum := by decide
  have hdescent : baseEnd_7698397 < baseStart_7698397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698417 : List Nat := [1, 2, 2, 2, 5, 1, 3, 1, 1, 2, 3]
def baseStart_7698417 : Nat := 118140960795 + 7698417 * 2 ^ 59
def prefixEnd_7698417 : Nat := 4983230072969 + 3 ^ 40 * 7698417 * 2
def baseEnd_7698417 : Nat := 3952988199743911641783131

theorem tailTrace_7698417 : CollatzResearch.WordTrace tailWord_7698417 prefixEnd_7698417 3952988199743911641783131 := by
  unfold tailWord_7698417
  simp only [CollatzResearch.WordTrace]
  refine ⟨280784335350957468793333505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187189556900638312528889003 280784335350957468793333505)
  ·
    refine ⟨210588251513218101595000129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280784335350957468793333505 210588251513218101595000129)
    ·
      refine ⟨157941188634913576196250097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210588251513218101595000129 157941188634913576196250097)
      ·
        refine ⟨118455891476185182147187573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157941188634913576196250097 118455891476185182147187573)
        ·
          refine ⟨11105239825892360826298835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118455891476185182147187573 11105239825892360826298835)
          ·
            refine ⟨16657859738838541239448253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11105239825892360826298835 16657859738838541239448253)
            ·
              refine ⟨6246697402064452964793095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16657859738838541239448253 6246697402064452964793095)
              ·
                refine ⟨9370046103096679447189643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246697402064452964793095 9370046103096679447189643)
                ·
                  refine ⟨14055069154645019170784465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370046103096679447189643 14055069154645019170784465)
                  ·
                    refine ⟨10541301865983764378088349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14055069154645019170784465 10541301865983764378088349)
                    ·
                      refine ⟨3952988199743911641783131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10541301865983764378088349 3952988199743911641783131)
                      ·
                        rfl

theorem cell23_7698417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_7698417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698417 prefixEnd_7698417 := by exact prefixLift 7698417
  have htrace : WordTrace (prefixWord ++ tailWord_7698417) baseStart_7698417 baseEnd_7698417 := by
    simpa [prefixWord, tailWord_7698417, baseEnd_7698417] using wordTrace_append hprefix tailTrace_7698417
  have hstable : (prefixWord ++ tailWord_7698417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698417).length < 2 ^ (prefixWord ++ tailWord_7698417).sum := by decide
  have hdescent : baseEnd_7698417 < baseStart_7698417 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698474 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_7698474 : Nat := 118140960795 + 7698474 * 2 ^ 59
def prefixEnd_7698474 : Nat := 4983230072969 + 3 ^ 40 * 7698474 * 2
def baseEnd_7698474 : Nat := 3953017468141217918770369

theorem tailTrace_7698474 : CollatzResearch.WordTrace tailWord_7698474 prefixEnd_7698474 3953017468141217918770369 := by
  unfold tailWord_7698474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70196603577937741882039619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 187190942874500645018772317 70196603577937741882039619)
  ·
    refine ⟨105294905366906612823059429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70196603577937741882039619 105294905366906612823059429)
    ·
      refine ⟨19742794756294989904323643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105294905366906612823059429 19742794756294989904323643)
      ·
        refine ⟨29614192134442484856485465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19742794756294989904323643 29614192134442484856485465)
        ·
          refine ⟨22210644100831863642364099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29614192134442484856485465 22210644100831863642364099)
          ·
            refine ⟨33315966151247795463546149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22210644100831863642364099 33315966151247795463546149)
            ·
              refine ⟨6246743653358961649414903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33315966151247795463546149 6246743653358961649414903)
              ·
                refine ⟨9370115480038442474122355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6246743653358961649414903 9370115480038442474122355)
                ·
                  refine ⟨14055173220057663711183533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370115480038442474122355 14055173220057663711183533)
                  ·
                    refine ⟨5270689957521623891693825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14055173220057663711183533 5270689957521623891693825)
                    ·
                      refine ⟨3953017468141217918770369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270689957521623891693825 3953017468141217918770369)
                      ·
                        rfl

theorem cell23_7698474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_7698474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698474 prefixEnd_7698474 := by exact prefixLift 7698474
  have htrace : WordTrace (prefixWord ++ tailWord_7698474) baseStart_7698474 baseEnd_7698474 := by
    simpa [prefixWord, tailWord_7698474, baseEnd_7698474] using wordTrace_append hprefix tailTrace_7698474
  have hstable : (prefixWord ++ tailWord_7698474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698474).length < 2 ^ (prefixWord ++ tailWord_7698474).sum := by decide
  have hdescent : baseEnd_7698474 < baseStart_7698474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698487 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 2, 2, 2]
def baseStart_7698487 : Nat := 118140960795 + 7698487 * 2 ^ 59
def prefixEnd_7698487 : Nat := 4983230072969 + 3 ^ 40 * 7698487 * 2
def baseEnd_7698487 : Nat := 3953024143389726367907809

theorem tailTrace_7698487 : CollatzResearch.WordTrace tailWord_7698487 prefixEnd_7698487 3953024143389726367907809 := by
  unfold tailWord_7698487
  simp only [CollatzResearch.WordTrace]
  refine ⟨280786888460703870748381715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187191258973802580498921143 280786888460703870748381715)
  ·
    refine ⟨421180332691055806122572573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280786888460703870748381715 421180332691055806122572573)
    ·
      refine ⟨157942624759145927295964715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 421180332691055806122572573 157942624759145927295964715)
      ·
        refine ⟨236913937138718890943947073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157942624759145927295964715 236913937138718890943947073)
        ·
          refine ⟨177685452854039168207960305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236913937138718890943947073 177685452854039168207960305)
          ·
            refine ⟨133264089640529376155970229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177685452854039168207960305 133264089640529376155970229)
            ·
              refine ⟨12493508403799629014622209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 133264089640529376155970229 12493508403799629014622209)
              ·
                refine ⟨9370131302849721760966657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12493508403799629014622209 9370131302849721760966657)
                ·
                  refine ⟨7027598477137291320724993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9370131302849721760966657 7027598477137291320724993)
                  ·
                    refine ⟨5270698857852968490543745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7027598477137291320724993 5270698857852968490543745)
                    ·
                      refine ⟨3953024143389726367907809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270698857852968490543745 3953024143389726367907809)
                      ·
                        rfl

theorem cell23_7698487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 2, 2].length) (baseStart_7698487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698487 prefixEnd_7698487 := by exact prefixLift 7698487
  have htrace : WordTrace (prefixWord ++ tailWord_7698487) baseStart_7698487 baseEnd_7698487 := by
    simpa [prefixWord, tailWord_7698487, baseEnd_7698487] using wordTrace_append hprefix tailTrace_7698487
  have hstable : (prefixWord ++ tailWord_7698487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698487).length < 2 ^ (prefixWord ++ tailWord_7698487).sum := by decide
  have hdescent : baseEnd_7698487 < baseStart_7698487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698493 : List Nat := [1, 4, 1, 3, 1, 1, 4, 1, 7]
def baseStart_7698493 : Nat := 118140960795 + 7698493 * 2 ^ 59
def prefixEnd_7698493 : Nat := 4983230072969 + 3 ^ 40 * 7698493 * 2
def baseEnd_7698493 : Nat := 439225247141517038270309

theorem tailTrace_7698493 : CollatzResearch.WordTrace tailWord_7698493 prefixEnd_7698493 439225247141517038270309 := by
  unfold tailWord_7698493
  simp only [CollatzResearch.WordTrace]
  refine ⟨280787107298682133773100133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187191404865788089182066755 280787107298682133773100133)
  ·
    refine ⟨52647582618502900082456275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280787107298682133773100133 52647582618502900082456275)
    ·
      refine ⟨78971373927754350123684413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52647582618502900082456275 78971373927754350123684413)
      ·
        refine ⟨29614265222907881296381655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78971373927754350123684413 29614265222907881296381655)
        ·
          refine ⟨44421397834361821944572483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29614265222907881296381655 44421397834361821944572483)
          ·
            refine ⟨66632096751542732916858725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44421397834361821944572483 66632096751542732916858725)
            ·
              refine ⟨12493518140914262421911011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66632096751542732916858725 12493518140914262421911011)
              ·
                refine ⟨18740277211371393632866517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12493518140914262421911011 18740277211371393632866517)
                ·
                  refine ⟨439225247141517038270309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18740277211371393632866517 439225247141517038270309)
                  ·
                    rfl

theorem cell23_7698493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_7698493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698493 prefixEnd_7698493 := by exact prefixLift 7698493
  have htrace : WordTrace (prefixWord ++ tailWord_7698493) baseStart_7698493 baseEnd_7698493 := by
    simpa [prefixWord, tailWord_7698493, baseEnd_7698493] using wordTrace_append hprefix tailTrace_7698493
  have hstable : (prefixWord ++ tailWord_7698493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698493).length < 2 ^ (prefixWord ++ tailWord_7698493).sum := by decide
  have hdescent : baseEnd_7698493 < baseStart_7698493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698503 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 3]
def baseStart_7698503 : Nat := 118140960795 + 7698503 * 2 ^ 59
def prefixEnd_7698503 : Nat := 4983230072969 + 3 ^ 40 * 7698503 * 2
def baseEnd_7698503 : Nat := 3953032359080198305307735

theorem tailTrace_7698503 : CollatzResearch.WordTrace tailWord_7698503 prefixEnd_7698503 3953032359080198305307735 := by
  unfold tailWord_7698503
  simp only [CollatzResearch.WordTrace]
  refine ⟨280787472028645905480964163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187191648019097270320642775 280787472028645905480964163)
  ·
    refine ⟨421181208042968858221446245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280787472028645905480964163 421181208042968858221446245)
    ·
      refine ⟨78971476508056660916521171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 421181208042968858221446245 78971476508056660916521171)
      ·
        refine ⟨118457214762084991374781757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78971476508056660916521171 118457214762084991374781757)
        ·
          refine ⟨44421455535781871765543159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118457214762084991374781757 44421455535781871765543159)
          ·
            refine ⟨66632183303672807648314739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44421455535781871765543159 66632183303672807648314739)
            ·
              refine ⟨99948274955509211472472109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66632183303672807648314739 99948274955509211472472109)
              ·
                refine ⟨37480603108315954302177041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99948274955509211472472109 37480603108315954302177041)
                ·
                  refine ⟨28110452331236965726632781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37480603108315954302177041 28110452331236965726632781)
                  ·
                    refine ⟨10541419624213862147487293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28110452331236965726632781 10541419624213862147487293)
                    ·
                      refine ⟨3953032359080198305307735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10541419624213862147487293 3953032359080198305307735)
                      ·
                        rfl

theorem cell23_7698503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 3].length) (baseStart_7698503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698503 prefixEnd_7698503 := by exact prefixLift 7698503
  have htrace : WordTrace (prefixWord ++ tailWord_7698503) baseStart_7698503 baseEnd_7698503 := by
    simpa [prefixWord, tailWord_7698503, baseEnd_7698503] using wordTrace_append hprefix tailTrace_7698503
  have hstable : (prefixWord ++ tailWord_7698503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698503).length < 2 ^ (prefixWord ++ tailWord_7698503).sum := by decide
  have hdescent : baseEnd_7698503 < baseStart_7698503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698543 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 4]
def baseStart_7698543 : Nat := 118140960795 + 7698543 * 2 ^ 59
def prefixEnd_7698543 : Nat := 4983230072969 + 3 ^ 40 * 7698543 * 2
def baseEnd_7698543 : Nat := 3953052898306378148807551

theorem tailTrace_7698543 : CollatzResearch.WordTrace tailWord_7698543 prefixEnd_7698543 3953052898306378148807551 := by
  unfold tailWord_7698543
  simp only [CollatzResearch.WordTrace]
  refine ⟨280788930948500992312420283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187192620632333994874946855 280788930948500992312420283)
  ·
    refine ⟨421183396422751488468630425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280788930948500992312420283 421183396422751488468630425)
    ·
      refine ⟨315887547317063616351472819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421183396422751488468630425 315887547317063616351472819)
      ·
        refine ⟨473831320975595424527209229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315887547317063616351472819 473831320975595424527209229)
        ·
          refine ⟨177686745365848284197703461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 473831320975595424527209229 177686745365848284197703461)
          ·
            refine ⟨33316264756096553287069399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177686745365848284197703461 33316264756096553287069399)
            ·
              refine ⟨49974397134144829930604099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33316264756096553287069399 49974397134144829930604099)
              ·
                refine ⟨74961595701217244895906149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49974397134144829930604099 74961595701217244895906149)
                ·
                  refine ⟨14055299193978233417982403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 74961595701217244895906149 14055299193978233417982403)
                  ·
                    refine ⟨21082948790967350126973605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14055299193978233417982403 21082948790967350126973605)
                    ·
                      refine ⟨3953052898306378148807551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21082948790967350126973605 3953052898306378148807551)
                      ·
                        rfl

theorem cell23_7698543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 4].length) (baseStart_7698543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698543 prefixEnd_7698543 := by exact prefixLift 7698543
  have htrace : WordTrace (prefixWord ++ tailWord_7698543) baseStart_7698543 baseEnd_7698543 := by
    simpa [prefixWord, tailWord_7698543, baseEnd_7698543] using wordTrace_append hprefix tailTrace_7698543
  have hstable : (prefixWord ++ tailWord_7698543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698543).length < 2 ^ (prefixWord ++ tailWord_7698543).sum := by decide
  have hdescent : baseEnd_7698543 < baseStart_7698543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698550 : List Nat := [5, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_7698550 : Nat := 118140960795 + 7698550 * 2 ^ 59
def prefixEnd_7698550 : Nat := 4983230072969 + 3 ^ 40 * 7698550 * 2
def baseEnd_7698550 : Nat := 3953056492670959621420019

theorem tailTrace_7698550 : CollatzResearch.WordTrace tailWord_7698550 prefixEnd_7698550 3953056492670959621420019 := by
  unfold tailWord_7698550
  simp only [CollatzResearch.WordTrace]
  refine ⟨17549324141217227031745319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 187192790839650421671950069 17549324141217227031745319)
  ·
    refine ⟨26323986211825840547617979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17549324141217227031745319 26323986211825840547617979)
    ·
      refine ⟨39485979317738760821426969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26323986211825840547617979 39485979317738760821426969)
      ·
        refine ⟨29614484488304070616070227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39485979317738760821426969 29614484488304070616070227)
        ·
          refine ⟨44421726732456105924105341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29614484488304070616070227 44421726732456105924105341)
          ·
            refine ⟨16658147524671039721539503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44421726732456105924105341 16658147524671039721539503)
            ·
              refine ⟨24987221287006559582309255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16658147524671039721539503 24987221287006559582309255)
              ·
                refine ⟨37480831930509839373463883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24987221287006559582309255 37480831930509839373463883)
                ·
                  refine ⟨56221247895764759060195825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37480831930509839373463883 56221247895764759060195825)
                  ·
                    refine ⟨42165935921823569295146869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56221247895764759060195825 42165935921823569295146869)
                    ·
                      refine ⟨3953056492670959621420019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42165935921823569295146869 3953056492670959621420019)
                      ·
                        rfl

theorem cell23_7698550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_7698550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698550 prefixEnd_7698550 := by exact prefixLift 7698550
  have htrace : WordTrace (prefixWord ++ tailWord_7698550) baseStart_7698550 baseEnd_7698550 := by
    simpa [prefixWord, tailWord_7698550, baseEnd_7698550] using wordTrace_append hprefix tailTrace_7698550
  have hstable : (prefixWord ++ tailWord_7698550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698550).length < 2 ^ (prefixWord ++ tailWord_7698550).sum := by decide
  have hdescent : baseEnd_7698550 < baseStart_7698550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698684 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 3, 2, 2]
def baseStart_7698684 : Nat := 118140960795 + 7698684 * 2 ^ 59
def prefixEnd_7698684 : Nat := 4983230072969 + 3 ^ 40 * 7698684 * 2
def baseEnd_7698684 : Nat := 3953125299078662097144403

theorem tailTrace_7698684 : CollatzResearch.WordTrace tailWord_7698684 prefixEnd_7698684 3953125299078662097144403 := by
  unfold tailWord_7698684
  simp only [CollatzResearch.WordTrace]
  refine ⟨140397036820495086696651553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 187196049093993448928868737 140397036820495086696651553)
  ·
    refine ⟨105297777615371315022488665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140397036820495086696651553 105297777615371315022488665)
    ·
      refine ⟨78973333211528486266866499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105297777615371315022488665 78973333211528486266866499)
      ·
        refine ⟨118459999817292729400299749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78973333211528486266866499 118459999817292729400299749)
        ·
          refine ⟨22211249965742386762556203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118459999817292729400299749 22211249965742386762556203)
          ·
            refine ⟨33316874948613580143834305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22211249965742386762556203 33316874948613580143834305)
            ·
              refine ⟨24987656211460185107875729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33316874948613580143834305 24987656211460185107875729)
              ·
                refine ⟨18740742158595138830906797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24987656211460185107875729 18740742158595138830906797)
                ·
                  refine ⟨7027778309473177061590049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18740742158595138830906797 7027778309473177061590049)
                  ·
                    refine ⟨5270833732104882796192537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7027778309473177061590049 5270833732104882796192537)
                    ·
                      refine ⟨3953125299078662097144403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5270833732104882796192537 3953125299078662097144403)
                      ·
                        rfl

theorem cell23_7698684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 2, 2].length) (baseStart_7698684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698684 prefixEnd_7698684 := by exact prefixLift 7698684
  have htrace : WordTrace (prefixWord ++ tailWord_7698684) baseStart_7698684 baseEnd_7698684 := by
    simpa [prefixWord, tailWord_7698684, baseEnd_7698684] using wordTrace_append hprefix tailTrace_7698684
  have hstable : (prefixWord ++ tailWord_7698684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698684).length < 2 ^ (prefixWord ++ tailWord_7698684).sum := by decide
  have hdescent : baseEnd_7698684 < baseStart_7698684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7698687 : List Nat := [1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 3]
def baseStart_7698687 : Nat := 118140960795 + 7698687 * 2 ^ 59
def prefixEnd_7698687 : Nat := 4983230072969 + 3 ^ 40 * 7698687 * 2
def baseEnd_7698687 : Nat := 3953126839520625585406889

theorem tailTrace_7698687 : CollatzResearch.WordTrace tailWord_7698687 prefixEnd_7698687 3953126839520625585406889 := by
  unfold tailWord_7698687
  simp only [CollatzResearch.WordTrace]
  refine ⟨280794183059979304905662315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 187196122039986203270441543 280794183059979304905662315)
  ·
    refine ⟨421191274589968957358493473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280794183059979304905662315 421191274589968957358493473)
    ·
      refine ⟨315893455942476718018870105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 421191274589968957358493473 315893455942476718018870105)
      ·
        refine ⟨236920091956857538514152579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315893455942476718018870105 236920091956857538514152579)
        ·
          refine ⟨355380137935286307771228869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236920091956857538514152579 355380137935286307771228869)
          ·
            refine ⟨66633775862866182707105413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 355380137935286307771228869 66633775862866182707105413)
            ·
              refine ⟨12493832974287409257582265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66633775862866182707105413 12493832974287409257582265)
              ·
                refine ⟨9370374730715556943186699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12493832974287409257582265 9370374730715556943186699)
                ·
                  refine ⟨14055562096073335414780049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9370374730715556943186699 14055562096073335414780049)
                  ·
                    refine ⟨10541671572055001561085037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14055562096073335414780049 10541671572055001561085037)
                    ·
                      refine ⟨3953126839520625585406889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10541671572055001561085037 3953126839520625585406889)
                      ·
                        rfl

theorem cell23_7698687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_7698687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7698687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7698687 prefixEnd_7698687 := by exact prefixLift 7698687
  have htrace : WordTrace (prefixWord ++ tailWord_7698687) baseStart_7698687 baseEnd_7698687 := by
    simpa [prefixWord, tailWord_7698687, baseEnd_7698687] using wordTrace_append hprefix tailTrace_7698687
  have hstable : (prefixWord ++ tailWord_7698687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7698687).length < 2 ^ (prefixWord ++ tailWord_7698687).sum := by decide
  have hdescent : baseEnd_7698687 < baseStart_7698687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7698687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
