import V185TrunkScan23Chunk0408

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2418316 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_2418316 : Nat := 118140960795 + 2418316 * 2 ^ 59
def prefixEnd_2418316 : Nat := 4983230072969 + 3 ^ 40 * 2418316 * 2
def baseEnd_2418316 : Nat := 413919494152821853742791

theorem tailTrace_2418316 : CollatzResearch.WordTrace tailWord_2418316 prefixEnd_2418316 413919494152821853742791 := by
  unfold tailWord_2418316
  simp only [CollatzResearch.WordTrace]
  refine ⟨44101615353430811168033401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58802153804574414890711201 44101615353430811168033401)
  ·
    refine ⟨33076211515073108376025051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44101615353430811168033401 33076211515073108376025051)
    ·
      refine ⟨49614317272609662564037577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33076211515073108376025051 49614317272609662564037577)
      ·
        refine ⟨37210737954457246923028183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49614317272609662564037577 37210737954457246923028183)
        ·
          refine ⟨55816106931685870384542275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37210737954457246923028183 55816106931685870384542275)
          ·
            refine ⟨83724160397528805576813413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55816106931685870384542275 83724160397528805576813413)
            ·
              refine ⟨15698280074536651045652515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83724160397528805576813413 15698280074536651045652515)
              ·
                refine ⟨23547420111804976568478773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15698280074536651045652515 23547420111804976568478773)
                ·
                  refine ⟨2207570635481716553294885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23547420111804976568478773 2207570635481716553294885)
                  ·
                    refine ⟨413919494152821853742791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2207570635481716553294885 413919494152821853742791)
                    ·
                      rfl

theorem cell23_2418316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_2418316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418316 prefixEnd_2418316 := by exact prefixLift 2418316
  have htrace : WordTrace (prefixWord ++ tailWord_2418316) baseStart_2418316 baseEnd_2418316 := by
    simpa [prefixWord, tailWord_2418316, baseEnd_2418316] using wordTrace_append hprefix tailTrace_2418316
  have hstable : (prefixWord ++ tailWord_2418316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418316).length < 2 ^ (prefixWord ++ tailWord_2418316).sum := by decide
  have hdescent : baseEnd_2418316 < baseStart_2418316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418329 : List Nat := [1, 2, 1, 2, 1, 2, 2, 4, 8]
def baseStart_2418329 : Nat := 118140960795 + 2418329 * 2 ^ 59
def prefixEnd_2418329 : Nat := 4983230072969 + 3 ^ 40 * 2418329 * 2
def baseEnd_2418329 : Nat := 137973906411886001151757

theorem tailTrace_2418329 : CollatzResearch.WordTrace tailWord_2418329 prefixEnd_2418329 137973906411886001151757 := by
  unfold tailWord_2418329
  simp only [CollatzResearch.WordTrace]
  refine ⟨88203704855814525556290041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58802469903876350370860027 88203704855814525556290041)
  ·
    refine ⟨66152778641860894167217531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88203704855814525556290041 66152778641860894167217531)
    ·
      refine ⟨99229167962791341250826297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66152778641860894167217531 99229167962791341250826297)
      ·
        refine ⟨74421875972093505938119723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99229167962791341250826297 74421875972093505938119723)
        ·
          refine ⟨111632813958140258907179585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74421875972093505938119723 111632813958140258907179585)
          ·
            refine ⟨83724610468605194180384689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111632813958140258907179585 83724610468605194180384689)
            ·
              refine ⟨62793457851453895635288517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83724610468605194180384689 62793457851453895635288517)
              ·
                refine ⟨11773773347147605431616597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62793457851453895635288517 11773773347147605431616597)
                ·
                  refine ⟨137973906411886001151757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11773773347147605431616597 137973906411886001151757)
                  ·
                    rfl

theorem cell23_2418329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 8].length) (baseStart_2418329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418329 prefixEnd_2418329 := by exact prefixLift 2418329
  have htrace : WordTrace (prefixWord ++ tailWord_2418329) baseStart_2418329 baseEnd_2418329 := by
    simpa [prefixWord, tailWord_2418329, baseEnd_2418329] using wordTrace_append hprefix tailTrace_2418329
  have hstable : (prefixWord ++ tailWord_2418329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418329).length < 2 ^ (prefixWord ++ tailWord_2418329).sum := by decide
  have hdescent : baseEnd_2418329 < baseStart_2418329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418373 : List Nat := [1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 3]
def baseStart_2418373 : Nat := 118140960795 + 2418373 * 2 ^ 59
def prefixEnd_2418373 : Nat := 4983230072969 + 3 ^ 40 * 2418373 * 2
def baseEnd_2418373 : Nat := 1241787750855771838215611

theorem tailTrace_2418373 : CollatzResearch.WordTrace tailWord_2418373 prefixEnd_2418373 1241787750855771838215611 := by
  unfold tailWord_2418373
  simp only [CollatzResearch.WordTrace]
  refine ⟨88205309667655121070891773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58803539778436747380594515 88205309667655121070891773)
  ·
    refine ⟨33076991125370670401584415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88205309667655121070891773 33076991125370670401584415)
    ·
      refine ⟨49615486688056005602376623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33076991125370670401584415 49615486688056005602376623)
      ·
        refine ⟨74423230032084008403564935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49615486688056005602376623 74423230032084008403564935)
        ·
          refine ⟨111634845048126012605347403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74423230032084008403564935 111634845048126012605347403)
          ·
            refine ⟨167452267572189018908021105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111634845048126012605347403 167452267572189018908021105)
            ·
              refine ⟨125589200679141764181015829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167452267572189018908021105 125589200679141764181015829)
              ·
                refine ⟨5886993781834770195985117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 125589200679141764181015829 5886993781834770195985117)
                ·
                  refine ⟨2207622668188038823494419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5886993781834770195985117 2207622668188038823494419)
                  ·
                    refine ⟨3311434002282058235241629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2207622668188038823494419 3311434002282058235241629)
                    ·
                      refine ⟨1241787750855771838215611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3311434002282058235241629 1241787750855771838215611)
                      ·
                        rfl

theorem cell23_2418373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 6, 3, 1, 3].length) (baseStart_2418373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418373 prefixEnd_2418373 := by exact prefixLift 2418373
  have htrace : WordTrace (prefixWord ++ tailWord_2418373) baseStart_2418373 baseEnd_2418373 := by
    simpa [prefixWord, tailWord_2418373, baseEnd_2418373] using wordTrace_append hprefix tailTrace_2418373
  have hstable : (prefixWord ++ tailWord_2418373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418373).length < 2 ^ (prefixWord ++ tailWord_2418373).sum := by decide
  have hdescent : baseEnd_2418373 < baseStart_2418373 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418374 : List Nat := [6, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4]
def baseStart_2418374 : Nat := 118140960795 + 2418374 * 2 ^ 59
def prefixEnd_2418374 : Nat := 4983230072969 + 3 ^ 40 * 2418374 * 2
def baseEnd_2418374 : Nat := 1241788264336426334303107

theorem tailTrace_2418374 : CollatzResearch.WordTrace tailWord_2418374 prefixEnd_2418374 1241788264336426334303107 := by
  unfold tailWord_2418374
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756417066895359320052443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58803564093767665494452117 2756417066895359320052443)
  ·
    refine ⟨4134625600343038980078665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2756417066895359320052443 4134625600343038980078665)
    ·
      refine ⟨3100969200257279235058999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4134625600343038980078665 3100969200257279235058999)
      ·
        refine ⟨4651453800385918852588499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3100969200257279235058999 4651453800385918852588499)
        ·
          refine ⟨6977180700578878278882749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651453800385918852588499 6977180700578878278882749)
          ·
            refine ⟨2616442762717079354581031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6977180700578878278882749 2616442762717079354581031)
            ·
              refine ⟨3924664144075619031871547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616442762717079354581031 3924664144075619031871547)
              ·
                refine ⟨5886996216113428547807321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3924664144075619031871547 5886996216113428547807321)
                ·
                  refine ⟨4415247162085071410855491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5886996216113428547807321 4415247162085071410855491)
                  ·
                    refine ⟨6622870743127607116283237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415247162085071410855491 6622870743127607116283237)
                    ·
                      refine ⟨1241788264336426334303107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6622870743127607116283237 1241788264336426334303107)
                      ·
                        rfl

theorem cell23_2418374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_2418374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418374 prefixEnd_2418374 := by exact prefixLift 2418374
  have htrace : WordTrace (prefixWord ++ tailWord_2418374) baseStart_2418374 baseEnd_2418374 := by
    simpa [prefixWord, tailWord_2418374, baseEnd_2418374] using wordTrace_append hprefix tailTrace_2418374
  have hstable : (prefixWord ++ tailWord_2418374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418374).length < 2 ^ (prefixWord ++ tailWord_2418374).sum := by decide
  have hdescent : baseEnd_2418374 < baseStart_2418374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418376 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 3, 5]
def baseStart_2418376 : Nat := 118140960795 + 2418376 * 2 ^ 59
def prefixEnd_2418376 : Nat := 4983230072969 + 3 ^ 40 * 2418376 * 2
def baseEnd_2418376 : Nat := 413929763765911775492699

theorem tailTrace_2418376 : CollatzResearch.WordTrace tailWord_2418376 prefixEnd_2418376 413929763765911775492699 := by
  unfold tailWord_2418376
  simp only [CollatzResearch.WordTrace]
  refine ⟨44102709543322126291625491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58803612724429501722167321 44102709543322126291625491)
  ·
    refine ⟨66154064314983189437438237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44102709543322126291625491 66154064314983189437438237)
    ·
      refine ⟨24807774118118696039039339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66154064314983189437438237 24807774118118696039039339)
      ·
        refine ⟨37211661177178044058559009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24807774118118696039039339 37211661177178044058559009)
        ·
          refine ⟨27908745882883533043919257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37211661177178044058559009 27908745882883533043919257)
          ·
            refine ⟨20931559412162649782939443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27908745882883533043919257 20931559412162649782939443)
            ·
              refine ⟨31397339118243974674409165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20931559412162649782939443 31397339118243974674409165)
              ·
                refine ⟨11774002169341490502903437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31397339118243974674409165 11774002169341490502903437)
                ·
                  refine ⟨4415250813503058938588789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11774002169341490502903437 4415250813503058938588789)
                  ·
                    refine ⟨413929763765911775492699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4415250813503058938588789 413929763765911775492699)
                    ·
                      rfl

theorem cell23_2418376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_2418376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418376 prefixEnd_2418376 := by exact prefixLift 2418376
  have htrace : WordTrace (prefixWord ++ tailWord_2418376) baseStart_2418376 baseEnd_2418376 := by
    simpa [prefixWord, tailWord_2418376, baseEnd_2418376] using wordTrace_append hprefix tailTrace_2418376
  have hstable : (prefixWord ++ tailWord_2418376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418376).length < 2 ^ (prefixWord ++ tailWord_2418376).sum := by decide
  have hdescent : baseEnd_2418376 < baseStart_2418376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418393 : List Nat := [1, 2, 1, 2, 3, 4, 1, 3, 1, 5]
def baseStart_2418393 : Nat := 118140960795 + 2418393 * 2 ^ 59
def prefixEnd_2418393 : Nat := 4983230072969 + 3 ^ 40 * 2418393 * 2
def baseEnd_2418393 : Nat := 413932673489620586655173

theorem tailTrace_2418393 : CollatzResearch.WordTrace tailWord_2418393 prefixEnd_2418393 413932673489620586655173 := by
  unfold tailWord_2418393
  simp only [CollatzResearch.WordTrace]
  refine ⟨88206039127582664486619833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58804026085055109657746555 88206039127582664486619833)
  ·
    refine ⟨66154529345686998364964875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88206039127582664486619833 66154529345686998364964875)
    ·
      refine ⟨99231794018530497547447313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66154529345686998364964875 99231794018530497547447313)
      ·
        refine ⟨74423845513897873160585485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99231794018530497547447313 74423845513897873160585485)
        ·
          refine ⟨27908942067711702435219557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74423845513897873160585485 27908942067711702435219557)
          ·
            refine ⟨5232926637695944206603667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27908942067711702435219557 5232926637695944206603667)
            ·
              refine ⟨7849389956543916309905501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5232926637695944206603667 7849389956543916309905501)
              ·
                refine ⟨2943521233703968616214563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7849389956543916309905501 2943521233703968616214563)
                ·
                  refine ⟨4415281850555952924321845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943521233703968616214563 4415281850555952924321845)
                  ·
                    refine ⟨413932673489620586655173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4415281850555952924321845 413932673489620586655173)
                    ·
                      rfl

theorem cell23_2418393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 1, 5].length) (baseStart_2418393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418393 prefixEnd_2418393 := by exact prefixLift 2418393
  have htrace : WordTrace (prefixWord ++ tailWord_2418393) baseStart_2418393 baseEnd_2418393 := by
    simpa [prefixWord, tailWord_2418393, baseEnd_2418393] using wordTrace_append hprefix tailTrace_2418393
  have hstable : (prefixWord ++ tailWord_2418393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418393).length < 2 ^ (prefixWord ++ tailWord_2418393).sum := by decide
  have hdescent : baseEnd_2418393 < baseStart_2418393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418397 : List Nat := [1, 4, 3, 3, 1, 2, 1, 2, 6]
def baseStart_2418397 : Nat := 118140960795 + 2418397 * 2 ^ 59
def prefixEnd_2418397 : Nat := 4983230072969 + 3 ^ 40 * 2418397 * 2
def baseEnd_2418397 : Nat := 137977786043497749368389

theorem tailTrace_2418397 : CollatzResearch.WordTrace tailWord_2418397 prefixEnd_2418397 137977786043497749368389 := by
  unfold tailWord_2418397
  simp only [CollatzResearch.WordTrace]
  refine ⟨88206185019568173169765445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58804123346378782113176963 88206185019568173169765445)
  ·
    refine ⟨16538659691169032469331021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88206185019568173169765445 16538659691169032469331021)
    ·
      refine ⟨6201997384188387175999133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16538659691169032469331021 6201997384188387175999133)
      ·
        refine ⟨2325749019070645190999675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6201997384188387175999133 2325749019070645190999675)
        ·
          refine ⟨3488623528605967786499513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325749019070645190999675 3488623528605967786499513)
          ·
            refine ⟨2616467646454475839874635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3488623528605967786499513 2616467646454475839874635)
            ·
              refine ⟨3924701469681713759811953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616467646454475839874635 3924701469681713759811953)
              ·
                refine ⟨2943526102261285319858965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924701469681713759811953 2943526102261285319858965)
                ·
                  refine ⟨137977786043497749368389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2943526102261285319858965 137977786043497749368389)
                  ·
                    rfl

theorem cell23_2418397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_2418397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418397 prefixEnd_2418397 := by exact prefixLift 2418397
  have htrace : WordTrace (prefixWord ++ tailWord_2418397) baseStart_2418397 baseEnd_2418397 := by
    simpa [prefixWord, tailWord_2418397, baseEnd_2418397] using wordTrace_append hprefix tailTrace_2418397
  have hstable : (prefixWord ++ tailWord_2418397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418397).length < 2 ^ (prefixWord ++ tailWord_2418397).sum := by decide
  have hdescent : baseEnd_2418397 < baseStart_2418397 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418416 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3]
def baseStart_2418416 : Nat := 118140960795 + 2418416 * 2 ^ 59
def prefixEnd_2418416 : Nat := 4983230072969 + 3 ^ 40 * 2418416 * 2
def baseEnd_2418416 : Nat := 1241809830523915169977913

theorem tailTrace_2418416 : CollatzResearch.WordTrace tailWord_2418416 prefixEnd_2418416 1241809830523915169977913 := by
  unfold tailWord_2418416
  simp only [CollatzResearch.WordTrace]
  refine ⟨44103439003249669707353551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58804585337666226276471401 44103439003249669707353551)
  ·
    refine ⟨66155158504874504561030327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44103439003249669707353551 66155158504874504561030327)
    ·
      refine ⟨99232737757311756841545491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66155158504874504561030327 99232737757311756841545491)
      ·
        refine ⟨148849106635967635262318237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99232737757311756841545491 148849106635967635262318237)
        ·
          refine ⟨55818414988487863223369339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148849106635967635262318237 55818414988487863223369339)
          ·
            refine ⟨83727622482731794835054009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55818414988487863223369339 83727622482731794835054009)
            ·
              refine ⟨62795716862048846126290507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83727622482731794835054009 62795716862048846126290507)
              ·
                refine ⟨94193575293073269189435761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62795716862048846126290507 94193575293073269189435761)
                ·
                  refine ⟨70645181469804951892076821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94193575293073269189435761 70645181469804951892076821)
                  ·
                    refine ⟨3311492881397107119941101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 70645181469804951892076821 3311492881397107119941101)
                    ·
                      refine ⟨1241809830523915169977913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3311492881397107119941101 1241809830523915169977913)
                      ·
                        rfl

theorem cell23_2418416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 3].length) (baseStart_2418416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418416 prefixEnd_2418416 := by exact prefixLift 2418416
  have htrace : WordTrace (prefixWord ++ tailWord_2418416) baseStart_2418416 baseEnd_2418416 := by
    simpa [prefixWord, tailWord_2418416, baseEnd_2418416] using wordTrace_append hprefix tailTrace_2418416
  have hstable : (prefixWord ++ tailWord_2418416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418416).length < 2 ^ (prefixWord ++ tailWord_2418416).sum := by decide
  have hdescent : baseEnd_2418416 < baseStart_2418416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418423 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 2, 4]
def baseStart_2418423 : Nat := 118140960795 + 2418423 * 2 ^ 59
def prefixEnd_2418423 : Nat := 4983230072969 + 3 ^ 40 * 2418423 * 2
def baseEnd_2418423 : Nat := 413937808296165547530127

theorem tailTrace_2418423 : CollatzResearch.WordTrace tailWord_2418423 prefixEnd_2418423 413937808296165547530127 := by
  unfold tailWord_2418423
  simp only [CollatzResearch.WordTrace]
  refine ⟨88207133317473979610211923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58804755544982653073474615 88207133317473979610211923)
  ·
    refine ⟨132310699976210969415317885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88207133317473979610211923 132310699976210969415317885)
    ·
      refine ⟨49616512491079113530744207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132310699976210969415317885 49616512491079113530744207)
      ·
        refine ⟨74424768736618670296116311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49616512491079113530744207 74424768736618670296116311)
        ·
          refine ⟨111637153104928005444174467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74424768736618670296116311 111637153104928005444174467)
          ·
            refine ⟨167455729657392008166261701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111637153104928005444174467 167455729657392008166261701)
            ·
              refine ⟨31397949310761001531174069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167455729657392008166261701 31397949310761001531174069)
              ·
                refine ⟨2943557747883843893547569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31397949310761001531174069 2943557747883843893547569)
                ·
                  refine ⟨2207668310912882920160677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2943557747883843893547569 2207668310912882920160677)
                  ·
                    refine ⟨413937808296165547530127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2207668310912882920160677 413937808296165547530127)
                    ·
                      rfl

theorem cell23_2418423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 2, 4].length) (baseStart_2418423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418423 prefixEnd_2418423 := by exact prefixLift 2418423
  have htrace : WordTrace (prefixWord ++ tailWord_2418423) baseStart_2418423 baseEnd_2418423 := by
    simpa [prefixWord, tailWord_2418423, baseEnd_2418423] using wordTrace_append hprefix tailTrace_2418423
  have hstable : (prefixWord ++ tailWord_2418423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418423).length < 2 ^ (prefixWord ++ tailWord_2418423).sum := by decide
  have hdescent : baseEnd_2418423 < baseStart_2418423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418433 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_2418433 : Nat := 118140960795 + 2418433 * 2 ^ 59
def prefixEnd_2418433 : Nat := 4983230072969 + 3 ^ 40 * 2418433 * 2
def baseEnd_2418433 : Nat := 1241818559695041603465335

theorem tailTrace_2418433 : CollatzResearch.WordTrace tailWord_2418433 prefixEnd_2418433 1241818559695041603465335 := by
  unfold tailWord_2418433
  simp only [CollatzResearch.WordTrace]
  refine ⟨88207498047437751318075953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58804998698291834212050635 88207498047437751318075953)
  ·
    refine ⟨66155623535578313488556965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88207498047437751318075953 66155623535578313488556965)
    ·
      refine ⟨12404179412920933779104431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66155623535578313488556965 12404179412920933779104431)
      ·
        refine ⟨18606269119381400668656647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12404179412920933779104431 18606269119381400668656647)
        ·
          refine ⟨27909403679072101002984971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18606269119381400668656647 27909403679072101002984971)
          ·
            refine ⟨41864105518608151504477457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27909403679072101002984971 41864105518608151504477457)
            ·
              refine ⟨31398079138956113628358093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41864105518608151504477457 31398079138956113628358093)
              ·
                refine ⟨11774279677108542610634285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31398079138956113628358093 11774279677108542610634285)
                ·
                  refine ⟨4415354878915703478987857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11774279677108542610634285 4415354878915703478987857)
                  ·
                    refine ⟨3311516159186777609240893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4415354878915703478987857 3311516159186777609240893)
                    ·
                      refine ⟨1241818559695041603465335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3311516159186777609240893 1241818559695041603465335)
                      ·
                        rfl

theorem cell23_2418433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_2418433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418433 prefixEnd_2418433 := by exact prefixLift 2418433
  have htrace : WordTrace (prefixWord ++ tailWord_2418433) baseStart_2418433 baseEnd_2418433 := by
    simpa [prefixWord, tailWord_2418433, baseEnd_2418433] using wordTrace_append hprefix tailTrace_2418433
  have hstable : (prefixWord ++ tailWord_2418433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418433).length < 2 ^ (prefixWord ++ tailWord_2418433).sum := by decide
  have hdescent : baseEnd_2418433 < baseStart_2418433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418447 : List Nat := [1, 1, 2, 1, 1, 1, 4, 7, 1, 2, 2]
def baseStart_2418447 : Nat := 118140960795 + 2418447 * 2 ^ 59
def prefixEnd_2418447 : Nat := 4983230072969 + 3 ^ 40 * 2418447 * 2
def baseEnd_2418447 : Nat := 1241825748424204548690271

theorem tailTrace_2418447 : CollatzResearch.WordTrace tailWord_2418447 prefixEnd_2418447 1241825748424204548690271 := by
  unfold tailWord_2418447
  simp only [CollatzResearch.WordTrace]
  refine ⟨88208008669387031709085595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58805339112924687806057063 88208008669387031709085595)
  ·
    refine ⟨132312013004080547563628393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88208008669387031709085595 132312013004080547563628393)
    ·
      refine ⟨99234009753060410672721295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132312013004080547563628393 99234009753060410672721295)
      ·
        refine ⟨148851014629590616009081943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99234009753060410672721295 148851014629590616009081943)
        ·
          refine ⟨223276521944385924013622915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148851014629590616009081943 223276521944385924013622915)
          ·
            refine ⟨334914782916578886020434373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223276521944385924013622915 334914782916578886020434373)
            ·
              refine ⟨62796521796858541128831445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 334914782916578886020434373 62796521796858541128831445)
              ·
                refine ⟨1471793479613872057706987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62796521796858541128831445 1471793479613872057706987)
                ·
                  refine ⟨2207690219420808086560481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471793479613872057706987 2207690219420808086560481)
                  ·
                    refine ⟨1655767664565606064920361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207690219420808086560481 1655767664565606064920361)
                    ·
                      refine ⟨1241825748424204548690271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655767664565606064920361 1241825748424204548690271)
                      ·
                        rfl

theorem cell23_2418447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 7, 1, 2, 2].length) (baseStart_2418447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418447 prefixEnd_2418447 := by exact prefixLift 2418447
  have htrace : WordTrace (prefixWord ++ tailWord_2418447) baseStart_2418447 baseEnd_2418447 := by
    simpa [prefixWord, tailWord_2418447, baseEnd_2418447] using wordTrace_append hprefix tailTrace_2418447
  have hstable : (prefixWord ++ tailWord_2418447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418447).length < 2 ^ (prefixWord ++ tailWord_2418447).sum := by decide
  have hdescent : baseEnd_2418447 < baseStart_2418447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418450 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2418450 : Nat := 118140960795 + 2418450 * 2 ^ 59
def prefixEnd_2418450 : Nat := 4983230072969 + 3 ^ 40 * 2418450 * 2
def baseEnd_2418450 : Nat := 1241827288866168036952757

theorem tailTrace_2418450 : CollatzResearch.WordTrace tailWord_2418450 prefixEnd_2418450 1241827288866168036952757 := by
  unfold tailWord_2418450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22052029522094040805361201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58805412058917442147629869 22052029522094040805361201)
  ·
    refine ⟨16539022141570530604020901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22052029522094040805361201 16539022141570530604020901)
    ·
      refine ⟨3101066651544474488253919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16539022141570530604020901 3101066651544474488253919)
      ·
        refine ⟨4651599977316711732380879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101066651544474488253919 4651599977316711732380879)
        ·
          refine ⟨6977399965975067598571319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651599977316711732380879 6977399965975067598571319)
          ·
            refine ⟨10466099948962601397856979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6977399965975067598571319 10466099948962601397856979)
            ·
              refine ⟨15699149923443902096785469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10466099948962601397856979 15699149923443902096785469)
              ·
                refine ⟨5887181221291463286294551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15699149923443902096785469 5887181221291463286294551)
                ·
                  refine ⟨8830771831937194929441827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5887181221291463286294551 8830771831937194929441827)
                  ·
                    refine ⟨13246157747905792394162741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8830771831937194929441827 13246157747905792394162741)
                    ·
                      refine ⟨1241827288866168036952757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13246157747905792394162741 1241827288866168036952757)
                      ·
                        rfl

theorem cell23_2418450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2418450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418450 prefixEnd_2418450 := by exact prefixLift 2418450
  have htrace : WordTrace (prefixWord ++ tailWord_2418450) baseStart_2418450 baseEnd_2418450 := by
    simpa [prefixWord, tailWord_2418450, baseEnd_2418450] using wordTrace_append hprefix tailTrace_2418450
  have hstable : (prefixWord ++ tailWord_2418450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418450).length < 2 ^ (prefixWord ++ tailWord_2418450).sum := by decide
  have hdescent : baseEnd_2418450 < baseStart_2418450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418484 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2418484 : Nat := 118140960795 + 2418484 * 2 ^ 59
def prefixEnd_2418484 : Nat := 4983230072969 + 3 ^ 40 * 2418484 * 2
def baseEnd_2418484 : Nat := 1241844747208420903927601

theorem tailTrace_2418484 : CollatzResearch.WordTrace tailWord_2418484 prefixEnd_2418484 1241844747208420903927601 := by
  unfold tailWord_2418484
  simp only [CollatzResearch.WordTrace]
  refine ⟨44104679085126493514091253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58806238780168658018788337 44104679085126493514091253)
  ·
    refine ⟨4134813664230608766946055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44104679085126493514091253 4134813664230608766946055)
    ·
      refine ⟨6202220496345913150419083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4134813664230608766946055 6202220496345913150419083)
      ·
        refine ⟨9303330744518869725628625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6202220496345913150419083 9303330744518869725628625)
        ·
          refine ⟨6977498058389152294221469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9303330744518869725628625 6977498058389152294221469)
          ·
            refine ⟨2616561771895932110333051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6977498058389152294221469 2616561771895932110333051)
            ·
              refine ⟨3924842657843898165499577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616561771895932110333051 3924842657843898165499577)
              ·
                refine ⟨2943631993382923624124683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3924842657843898165499577 2943631993382923624124683)
                ·
                  refine ⟨4415447990074385436187025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943631993382923624124683 4415447990074385436187025)
                  ·
                    refine ⟨3311585992555789077140269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4415447990074385436187025 3311585992555789077140269)
                    ·
                      refine ⟨1241844747208420903927601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3311585992555789077140269 1241844747208420903927601)
                      ·
                        rfl

theorem cell23_2418484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2418484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418484 prefixEnd_2418484 := by exact prefixLift 2418484
  have htrace : WordTrace (prefixWord ++ tailWord_2418484) baseStart_2418484 baseEnd_2418484 := by
    simpa [prefixWord, tailWord_2418484, baseEnd_2418484] using wordTrace_append hprefix tailTrace_2418484
  have hstable : (prefixWord ++ tailWord_2418484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418484).length < 2 ^ (prefixWord ++ tailWord_2418484).sum := by decide
  have hdescent : baseEnd_2418484 < baseStart_2418484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418496 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 6, 6]
def baseStart_2418496 : Nat := 118140960795 + 2418496 * 2 ^ 59
def prefixEnd_2418496 : Nat := 4983230072969 + 3 ^ 40 * 2418496 * 2
def baseEnd_2418496 : Nat := 413950302992091618992515

theorem tailTrace_2418496 : CollatzResearch.WordTrace tailWord_2418496 prefixEnd_2418496 413950302992091618992515 := by
  unfold tailWord_2418496
  simp only [CollatzResearch.WordTrace]
  refine ⟨44104897923104756538809671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58806530564139675385079561 44104897923104756538809671)
  ·
    refine ⟨66157346884657134808214507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44104897923104756538809671 66157346884657134808214507)
    ·
      refine ⟨99236020326985702212321761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66157346884657134808214507 99236020326985702212321761)
      ·
        refine ⟨74427015245239276659241321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99236020326985702212321761 74427015245239276659241321)
        ·
          refine ⟨55820261433929457494430991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74427015245239276659241321 55820261433929457494430991)
          ·
            refine ⟨83730392150894186241646487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55820261433929457494430991 83730392150894186241646487)
            ·
              refine ⟨125595588226341279362469731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83730392150894186241646487 125595588226341279362469731)
              ·
                refine ⟨188393382339511919043704597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125595588226341279362469731 188393382339511919043704597)
                ·
                  refine ⟨8830939797164621205173653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188393382339511919043704597 8830939797164621205173653)
                  ·
                    refine ⟨413950302992091618992515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8830939797164621205173653 413950302992091618992515)
                    ·
                      rfl

theorem cell23_2418496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_2418496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418496 prefixEnd_2418496 := by exact prefixLift 2418496
  have htrace : WordTrace (prefixWord ++ tailWord_2418496) baseStart_2418496 baseEnd_2418496 := by
    simpa [prefixWord, tailWord_2418496, baseEnd_2418496] using wordTrace_append hprefix tailTrace_2418496
  have hstable : (prefixWord ++ tailWord_2418496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418496).length < 2 ^ (prefixWord ++ tailWord_2418496).sum := by decide
  have hdescent : baseEnd_2418496 < baseStart_2418496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418530 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2418530 : Nat := 118140960795 + 2418530 * 2 ^ 59
def prefixEnd_2418530 : Nat := 4983230072969 + 3 ^ 40 * 2418530 * 2
def baseEnd_2418530 : Nat := 413956122439509241317463

theorem tailTrace_2418530 : CollatzResearch.WordTrace tailWord_2418530 prefixEnd_2418530 413956122439509241317463 := by
  unfold tailWord_2418530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22052758982021584221089261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58807357285390891256238029 22052758982021584221089261)
  ·
    refine ⟨8269784618258094082908473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22052758982021584221089261 8269784618258094082908473)
    ·
      refine ⟨6202338463693570562181355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8269784618258094082908473 6202338463693570562181355)
      ·
        refine ⟨9303507695540355843272033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6202338463693570562181355 9303507695540355843272033)
        ·
          refine ⟨6977630771655266882454025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9303507695540355843272033 6977630771655266882454025)
          ·
            refine ⟨5233223078741450161840519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6977630771655266882454025 5233223078741450161840519)
            ·
              refine ⟨7849834618112175242760779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233223078741450161840519 7849834618112175242760779)
              ·
                refine ⟨11774751927168262864141169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7849834618112175242760779 11774751927168262864141169)
                ·
                  refine ⟨8831063945376197148105877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11774751927168262864141169 8831063945376197148105877)
                  ·
                    refine ⟨413956122439509241317463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8831063945376197148105877 413956122439509241317463)
                    ·
                      rfl

theorem cell23_2418530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2418530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418530 prefixEnd_2418530 := by exact prefixLift 2418530
  have htrace : WordTrace (prefixWord ++ tailWord_2418530) baseStart_2418530 baseEnd_2418530 := by
    simpa [prefixWord, tailWord_2418530, baseEnd_2418530] using wordTrace_append hprefix tailTrace_2418530
  have hstable : (prefixWord ++ tailWord_2418530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418530).length < 2 ^ (prefixWord ++ tailWord_2418530).sum := by decide
  have hdescent : baseEnd_2418530 < baseStart_2418530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418553 : List Nat := [1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 3]
def baseStart_2418553 : Nat := 118140960795 + 2418553 * 2 ^ 59
def prefixEnd_2418553 : Nat := 4983230072969 + 3 ^ 40 * 2418553 * 2
def baseEnd_2418553 : Nat := 1241880177373581133964783

theorem tailTrace_2418553 : CollatzResearch.WordTrace tailWord_2418553 prefixEnd_2418553 1241880177373581133964783 := by
  unfold tailWord_2418553
  simp only [CollatzResearch.WordTrace]
  refine ⟨88211874807003011812444313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58807916538002007874962875 88211874807003011812444313)
  ·
    refine ⟨66158906105252258859333235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88211874807003011812444313 66158906105252258859333235)
    ·
      refine ⟨99238359157878388288999853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66158906105252258859333235 99238359157878388288999853)
      ·
        refine ⟨37214384684204395608374945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99238359157878388288999853 37214384684204395608374945)
        ·
          refine ⟨27910788513153296706281209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37214384684204395608374945 27910788513153296706281209)
          ·
            refine ⟨20933091384864972529710907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27910788513153296706281209 20933091384864972529710907)
            ·
              refine ⟨31399637077297458794566361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20933091384864972529710907 31399637077297458794566361)
              ·
                refine ⟨23549727807973094095924771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31399637077297458794566361 23549727807973094095924771)
                ·
                  refine ⟨35324591711959641143887157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23549727807973094095924771 35324591711959641143887157)
                  ·
                    refine ⟨3311680472996216357239421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35324591711959641143887157 3311680472996216357239421)
                    ·
                      refine ⟨1241880177373581133964783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3311680472996216357239421 1241880177373581133964783)
                      ·
                        rfl

theorem cell23_2418553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_2418553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418553 prefixEnd_2418553 := by exact prefixLift 2418553
  have htrace : WordTrace (prefixWord ++ tailWord_2418553) baseStart_2418553 baseEnd_2418553 := by
    simpa [prefixWord, tailWord_2418553, baseEnd_2418553] using wordTrace_append hprefix tailTrace_2418553
  have hstable : (prefixWord ++ tailWord_2418553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418553).length < 2 ^ (prefixWord ++ tailWord_2418553).sum := by decide
  have hdescent : baseEnd_2418553 < baseStart_2418553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418558 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2418558 : Nat := 118140960795 + 2418558 * 2 ^ 59
def prefixEnd_2418558 : Nat := 4983230072969 + 3 ^ 40 * 2418558 * 2
def baseEnd_2418558 : Nat := 1241882744776853614402261

theorem tailTrace_2418558 : CollatzResearch.WordTrace tailWord_2418558 prefixEnd_2418558 1241882744776853614402261 := by
  unfold tailWord_2418558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11026507146498112208297041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58808038114656598444250885 11026507146498112208297041)
  ·
    refine ⟨8269880359873584156222781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11026507146498112208297041 8269880359873584156222781)
    ·
      refine ⟨3101205134952594058583543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8269880359873584156222781 3101205134952594058583543)
      ·
        refine ⟨4651807702428891087875315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101205134952594058583543 4651807702428891087875315)
        ·
          refine ⟨6977711553643336631812973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4651807702428891087875315 6977711553643336631812973)
          ·
            refine ⟨2616641832616251236929865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6977711553643336631812973 2616641832616251236929865)
            ·
              refine ⟨1962481374462188427697399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2616641832616251236929865 1962481374462188427697399)
              ·
                refine ⟨2943722061693282641546099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962481374462188427697399 2943722061693282641546099)
                ·
                  refine ⟨4415583092539923962319149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943722061693282641546099 4415583092539923962319149)
                  ·
                    refine ⟨1655843659702471485869681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4415583092539923962319149 1655843659702471485869681)
                    ·
                      refine ⟨1241882744776853614402261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655843659702471485869681 1241882744776853614402261)
                      ·
                        rfl

theorem cell23_2418558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2418558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418558 prefixEnd_2418558 := by exact prefixLift 2418558
  have htrace : WordTrace (prefixWord ++ tailWord_2418558) baseStart_2418558 baseEnd_2418558 := by
    simpa [prefixWord, tailWord_2418558, baseEnd_2418558] using wordTrace_append hprefix tailTrace_2418558
  have hstable : (prefixWord ++ tailWord_2418558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418558).length < 2 ^ (prefixWord ++ tailWord_2418558).sum := by decide
  have hdescent : baseEnd_2418558 < baseStart_2418558 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418560 : List Nat := [2, 1, 1, 2, 1, 2, 6, 3, 5]
def baseStart_2418560 : Nat := 118140960795 + 2418560 * 2 ^ 59
def prefixEnd_2418560 : Nat := 4983230072969 + 3 ^ 40 * 2418560 * 2
def baseEnd_2418560 : Nat := 137987085748684734064139

theorem tailTrace_2418560 : CollatzResearch.WordTrace tailWord_2418560 prefixEnd_2418560 137987085748684734064139 := by
  unfold tailWord_2418560
  simp only [CollatzResearch.WordTrace]
  refine ⟨44106065058988826003974567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58808086745318434671966089 44106065058988826003974567)
  ·
    refine ⟨66159097588483239005961851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44106065058988826003974567 66159097588483239005961851)
    ·
      refine ⟨99238646382724858508942777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66159097588483239005961851 99238646382724858508942777)
      ·
        refine ⟨74428984787043643881707083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99238646382724858508942777 74428984787043643881707083)
        ·
          refine ⟨111643477180565465822560625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74428984787043643881707083 111643477180565465822560625)
          ·
            refine ⟨83732607885424099366920469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111643477180565465822560625 83732607885424099366920469)
            ·
              refine ⟨3924965994629254657824397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83732607885424099366920469 3924965994629254657824397)
              ·
                refine ⟨1471862247985970496684149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3924965994629254657824397 1471862247985970496684149)
                ·
                  refine ⟨137987085748684734064139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1471862247985970496684149 137987085748684734064139)
                  ·
                    rfl

theorem cell23_2418560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 3, 5].length) (baseStart_2418560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418560 prefixEnd_2418560 := by exact prefixLift 2418560
  have htrace : WordTrace (prefixWord ++ tailWord_2418560) baseStart_2418560 baseEnd_2418560 := by
    simpa [prefixWord, tailWord_2418560, baseEnd_2418560] using wordTrace_append hprefix tailTrace_2418560
  have hstable : (prefixWord ++ tailWord_2418560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418560).length < 2 ^ (prefixWord ++ tailWord_2418560).sum := by decide
  have hdescent : baseEnd_2418560 < baseStart_2418560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418610 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2]
def baseStart_2418610 : Nat := 118140960795 + 2418610 * 2 ^ 59
def prefixEnd_2418610 : Nat := 4983230072969 + 3 ^ 40 * 2418610 * 2
def baseEnd_2418610 : Nat := 1241909445770887410952021

theorem tailTrace_2418610 : CollatzResearch.WordTrace tailWord_2418610 prefixEnd_2418610 1241909445770887410952021 := by
  unfold tailWord_2418610
  simp only [CollatzResearch.WordTrace]
  refine ⟨22053488441949127636817321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58809302511864340364846189 22053488441949127636817321)
  ·
    refine ⟨16540116331461845727612991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22053488441949127636817321 16540116331461845727612991)
    ·
      refine ⟨24810174497192768591419487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16540116331461845727612991 24810174497192768591419487)
      ·
        refine ⟨37215261745789152887129231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24810174497192768591419487 37215261745789152887129231)
        ·
          refine ⟨55822892618683729330693847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37215261745789152887129231 55822892618683729330693847)
          ·
            refine ⟨83734338928025593996040771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55822892618683729330693847 83734338928025593996040771)
            ·
              refine ⟨125601508392038390994061157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83734338928025593996040771 125601508392038390994061157)
              ·
                refine ⟨23550282823507198311386467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125601508392038390994061157 23550282823507198311386467)
                ·
                  refine ⟨35325424235260797467079701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23550282823507198311386467 35325424235260797467079701)
                  ·
                    refine ⟨1655879261027849881269361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35325424235260797467079701 1655879261027849881269361)
                    ·
                      refine ⟨1241909445770887410952021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655879261027849881269361 1241909445770887410952021)
                      ·
                        rfl

theorem cell23_2418610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 1, 6, 2].length) (baseStart_2418610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418610 prefixEnd_2418610 := by exact prefixLift 2418610
  have htrace : WordTrace (prefixWord ++ tailWord_2418610) baseStart_2418610 baseEnd_2418610 := by
    simpa [prefixWord, tailWord_2418610, baseEnd_2418610] using wordTrace_append hprefix tailTrace_2418610
  have hstable : (prefixWord ++ tailWord_2418610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418610).length < 2 ^ (prefixWord ++ tailWord_2418610).sum := by decide
  have hdescent : baseEnd_2418610 < baseStart_2418610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418680 : List Nat := [2, 1, 2, 1, 1, 3, 2, 5, 1, 5]
def baseStart_2418680 : Nat := 118140960795 + 2418680 * 2 ^ 59
def prefixEnd_2418680 : Nat := 4983230072969 + 3 ^ 40 * 2418680 * 2
def baseEnd_2418680 : Nat := 413981796472234045692233

theorem tailTrace_2418680 : CollatzResearch.WordTrace tailWord_2418680 prefixEnd_2418680 413981796472234045692233 := by
  unfold tailWord_2418680
  simp only [CollatzResearch.WordTrace]
  refine ⟨44108253438771456251158747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58811004585028608334878329 44108253438771456251158747)
  ·
    refine ⟨66162380158157184376738121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44108253438771456251158747 66162380158157184376738121)
    ·
      refine ⟨49621785118617888282553591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66162380158157184376738121 49621785118617888282553591)
      ·
        refine ⟨74432677677926832423830387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49621785118617888282553591 74432677677926832423830387)
        ·
          refine ⟨111649016516890248635745581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74432677677926832423830387 111649016516890248635745581)
          ·
            refine ⟨41868381193833843238404593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111649016516890248635745581 41868381193833843238404593)
            ·
              refine ⟨31401285895375382428803445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41868381193833843238404593 31401285895375382428803445)
              ·
                refine ⟨2943870552691442102700323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31401285895375382428803445 2943870552691442102700323)
                ·
                  refine ⟨4415805829037163154050485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943870552691442102700323 4415805829037163154050485)
                  ·
                    refine ⟨413981796472234045692233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4415805829037163154050485 413981796472234045692233)
                    ·
                      rfl

theorem cell23_2418680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_2418680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418680 prefixEnd_2418680 := by exact prefixLift 2418680
  have htrace : WordTrace (prefixWord ++ tailWord_2418680) baseStart_2418680 baseEnd_2418680 := by
    simpa [prefixWord, tailWord_2418680, baseEnd_2418680] using wordTrace_append hprefix tailTrace_2418680
  have hstable : (prefixWord ++ tailWord_2418680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418680).length < 2 ^ (prefixWord ++ tailWord_2418680).sum := by decide
  have hdescent : baseEnd_2418680 < baseStart_2418680 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418700 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 5, 1, 4]
def baseStart_2418700 : Nat := 118140960795 + 2418700 * 2 ^ 59
def prefixEnd_2418700 : Nat := 4983230072969 + 3 ^ 40 * 2418700 * 2
def baseEnd_2418700 : Nat := 1241955659029792058826607

theorem tailTrace_2418700 : CollatzResearch.WordTrace tailWord_2418700 prefixEnd_2418700 1241955659029792058826607 := by
  unfold tailWord_2418700
  simp only [CollatzResearch.WordTrace]
  refine ⟨44108618168735227959022777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58811490891646970612030369 44108618168735227959022777)
  ·
    refine ⟨33081463626551420969267083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44108618168735227959022777 33081463626551420969267083)
    ·
      refine ⟨49622195439827131453900625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33081463626551420969267083 49622195439827131453900625)
      ·
        refine ⟨37216646579870348590425469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49622195439827131453900625 37216646579870348590425469)
        ·
          refine ⟨13956242467451380721409551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37216646579870348590425469 13956242467451380721409551)
          ·
            refine ⟨20934363701177071082114327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13956242467451380721409551 20934363701177071082114327)
            ·
              refine ⟨31401545551765606623171491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20934363701177071082114327 31401545551765606623171491)
              ·
                refine ⟨47102318327648409934757237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31401545551765606623171491 47102318327648409934757237)
                ·
                  refine ⟨4415842343217038431383491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47102318327648409934757237 4415842343217038431383491)
                  ·
                    refine ⟨6623763514825557647075237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415842343217038431383491 6623763514825557647075237)
                    ·
                      refine ⟨1241955659029792058826607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6623763514825557647075237 1241955659029792058826607)
                      ·
                        rfl

theorem cell23_2418700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_2418700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418700 prefixEnd_2418700 := by exact prefixLift 2418700
  have htrace : WordTrace (prefixWord ++ tailWord_2418700) baseStart_2418700 baseEnd_2418700 := by
    simpa [prefixWord, tailWord_2418700, baseEnd_2418700] using wordTrace_append hprefix tailTrace_2418700
  have hstable : (prefixWord ++ tailWord_2418700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418700).length < 2 ^ (prefixWord ++ tailWord_2418700).sum := by decide
  have hdescent : baseEnd_2418700 < baseStart_2418700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418717 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2418717 : Nat := 118140960795 + 2418717 * 2 ^ 59
def prefixEnd_2418717 : Nat := 4983230072969 + 3 ^ 40 * 2418717 * 2
def baseEnd_2418717 : Nat := 1241964388200918492314029

theorem tailTrace_2418717 : CollatzResearch.WordTrace tailWord_2418717 prefixEnd_2418717 1241964388200918492314029 := by
  unfold tailWord_2418717
  simp only [CollatzResearch.WordTrace]
  refine ⟨88217856378408867821414405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58811904252272578547609603 88217856378408867821414405)
  ·
    refine ⟨16540848070951662716515201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88217856378408867821414405 16540848070951662716515201)
    ·
      refine ⟨12405636053213747037386401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16540848070951662716515201 12405636053213747037386401)
      ·
        refine ⟨9304227039910310278039801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12405636053213747037386401 9304227039910310278039801)
        ·
          refine ⟨6978170279932732708529851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9304227039910310278039801 6978170279932732708529851)
          ·
            refine ⟨10467255419899099062794777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978170279932732708529851 10467255419899099062794777)
            ·
              refine ⟨7850441564924324297096083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10467255419899099062794777 7850441564924324297096083)
              ·
                refine ⟨11775662347386486445644125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7850441564924324297096083 11775662347386486445644125)
                ·
                  refine ⟨4415873380269932417116547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11775662347386486445644125 4415873380269932417116547)
                  ·
                    refine ⟨6623810070404898625674821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415873380269932417116547 6623810070404898625674821)
                    ·
                      refine ⟨1241964388200918492314029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6623810070404898625674821 1241964388200918492314029)
                      ·
                        rfl

theorem cell23_2418717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2418717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418717 prefixEnd_2418717 := by exact prefixLift 2418717
  have htrace : WordTrace (prefixWord ++ tailWord_2418717) baseStart_2418717 baseEnd_2418717 := by
    simpa [prefixWord, tailWord_2418717, baseEnd_2418717] using wordTrace_append hprefix tailTrace_2418717
  have hstable : (prefixWord ++ tailWord_2418717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418717).length < 2 ^ (prefixWord ++ tailWord_2418717).sum := by decide
  have hdescent : baseEnd_2418717 < baseStart_2418717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418721 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_2418721 : Nat := 118140960795 + 2418721 * 2 ^ 59
def prefixEnd_2418721 : Nat := 4983230072969 + 3 ^ 40 * 2418721 * 2
def baseEnd_2418721 : Nat := 1241966442123536476664011

theorem tailTrace_2418721 : CollatzResearch.WordTrace tailWord_2418721 prefixEnd_2418721 1241966442123536476664011 := by
  unfold tailWord_2418721
  simp only [CollatzResearch.WordTrace]
  refine ⟨88218002270394376504560017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58812001513596251003040011 88218002270394376504560017)
  ·
    refine ⟨66163501702795782378420013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88218002270394376504560017 66163501702795782378420013)
    ·
      refine ⟨24811313138548418391907505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66163501702795782378420013 24811313138548418391907505)
      ·
        refine ⟨18608484853911313793930629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24811313138548418391907505 18608484853911313793930629)
        ·
          refine ⟨3489090910108371336361993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18608484853911313793930629 3489090910108371336361993)
          ·
            refine ⟨2616818182581278502271495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3489090910108371336361993 2616818182581278502271495)
            ·
              refine ⟨3925227273871917753407243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2616818182581278502271495 3925227273871917753407243)
              ·
                refine ⟨5887840910807876630110865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925227273871917753407243 5887840910807876630110865)
                ·
                  refine ⟨4415880683105907472583149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5887840910807876630110865 4415880683105907472583149)
                  ·
                    refine ⟨1655955256164715302218681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4415880683105907472583149 1655955256164715302218681)
                    ·
                      refine ⟨1241966442123536476664011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655955256164715302218681 1241966442123536476664011)
                      ·
                        rfl

theorem cell23_2418721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_2418721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418721 prefixEnd_2418721 := by exact prefixLift 2418721
  have htrace : WordTrace (prefixWord ++ tailWord_2418721) baseStart_2418721 baseEnd_2418721 := by
    simpa [prefixWord, tailWord_2418721, baseEnd_2418721] using wordTrace_append hprefix tailTrace_2418721
  have hstable : (prefixWord ++ tailWord_2418721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418721).length < 2 ^ (prefixWord ++ tailWord_2418721).sum := by decide
  have hdescent : baseEnd_2418721 < baseStart_2418721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418734 : List Nat := [4, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2418734 : Nat := 118140960795 + 2418734 * 2 ^ 59
def prefixEnd_2418734 : Nat := 4983230072969 + 3 ^ 40 * 2418734 * 2
def baseEnd_2418734 : Nat := 1241973117372044925801451

theorem tailTrace_2418734 : CollatzResearch.WordTrace tailWord_2418734 prefixEnd_2418734 1241973117372044925801451 := by
  unfold tailWord_2418734
  simp only [CollatzResearch.WordTrace]
  refine ⟨11027309552418409965597907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58812317612898186483188837 11027309552418409965597907)
  ·
    refine ⟨16540964328627614948396861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11027309552418409965597907 16540964328627614948396861)
    ·
      refine ⟨6202861623235355605648823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16540964328627614948396861 6202861623235355605648823)
      ·
        refine ⟨9304292434853033408473235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6202861623235355605648823 9304292434853033408473235)
        ·
          refine ⟨13956438652279550112709853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9304292434853033408473235 13956438652279550112709853)
          ·
            refine ⟨5233664494604831292266195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13956438652279550112709853 5233664494604831292266195)
            ·
              refine ⟨7850496741907246938399293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233664494604831292266195 7850496741907246938399293)
              ·
                refine ⟨2943936278215217601899735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7850496741907246938399293 2943936278215217601899735)
                ·
                  refine ⟨4415904417322826402849603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2943936278215217601899735 4415904417322826402849603)
                  ·
                    refine ⟨6623856625984239604274405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4415904417322826402849603 6623856625984239604274405)
                    ·
                      refine ⟨1241973117372044925801451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6623856625984239604274405 1241973117372044925801451)
                      ·
                        rfl

theorem cell23_2418734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2418734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418734 prefixEnd_2418734 := by exact prefixLift 2418734
  have htrace : WordTrace (prefixWord ++ tailWord_2418734) baseStart_2418734 baseEnd_2418734 := by
    simpa [prefixWord, tailWord_2418734, baseEnd_2418734] using wordTrace_append hprefix tailTrace_2418734
  have hstable : (prefixWord ++ tailWord_2418734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418734).length < 2 ^ (prefixWord ++ tailWord_2418734).sum := by decide
  have hdescent : baseEnd_2418734 < baseStart_2418734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418751 : List Nat := [1, 1, 2, 2, 3, 1, 4, 4, 1, 2, 2]
def baseStart_2418751 : Nat := 118140960795 + 2418751 * 2 ^ 59
def prefixEnd_2418751 : Nat := 4983230072969 + 3 ^ 40 * 2418751 * 2
def baseEnd_2418751 : Nat := 1241981846543171359288873

theorem tailTrace_2418751 : CollatzResearch.WordTrace tailWord_2418751 prefixEnd_2418751 1241981846543171359288873 := by
  unfold tailWord_2418751
  simp only [CollatzResearch.WordTrace]
  refine ⟨88219096460285691628152107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58812730973523794418768071 88219096460285691628152107)
  ·
    refine ⟨132328644690428537442228161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88219096460285691628152107 132328644690428537442228161)
    ·
      refine ⟨99246483517821403081671121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132328644690428537442228161 99246483517821403081671121)
      ·
        refine ⟨74434862638366052311253341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99246483517821403081671121 74434862638366052311253341)
        ·
          refine ⟨27913073489387269616720003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74434862638366052311253341 27913073489387269616720003)
          ·
            refine ⟨41869610234080904425080005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27913073489387269616720003 41869610234080904425080005)
            ·
              refine ⟨7850551918890169579702501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41869610234080904425080005 7850551918890169579702501)
              ·
                refine ⟨1471978484791906796194219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7850551918890169579702501 1471978484791906796194219)
                ·
                  refine ⟨2207967727187860194291329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1471978484791906796194219 2207967727187860194291329)
                  ·
                    refine ⟨1655975795390895145718497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2207967727187860194291329 1655975795390895145718497)
                    ·
                      refine ⟨1241981846543171359288873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1655975795390895145718497 1241981846543171359288873)
                      ·
                        rfl

theorem cell23_2418751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 4, 1, 2, 2].length) (baseStart_2418751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418751 prefixEnd_2418751 := by exact prefixLift 2418751
  have htrace : WordTrace (prefixWord ++ tailWord_2418751) baseStart_2418751 baseEnd_2418751 := by
    simpa [prefixWord, tailWord_2418751, baseEnd_2418751] using wordTrace_append hprefix tailTrace_2418751
  have hstable : (prefixWord ++ tailWord_2418751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418751).length < 2 ^ (prefixWord ++ tailWord_2418751).sum := by decide
  have hdescent : baseEnd_2418751 < baseStart_2418751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418774 : List Nat := [5, 2, 2, 1, 1, 2, 1, 9]
def baseStart_2418774 : Nat := 118140960795 + 2418774 * 2 ^ 59
def prefixEnd_2418774 : Nat := 4983230072969 + 3 ^ 40 * 2418774 * 2
def baseEnd_2418774 : Nat := 45999765059193509974121

theorem tailTrace_2418774 : CollatzResearch.WordTrace tailWord_2418774 prefixEnd_2418774 45999765059193509974121 := by
  unfold tailWord_2418774
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513745958700147909764961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58813290226134911037492917 5513745958700147909764961)
  ·
    refine ⟨4135309469025110932323721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5513745958700147909764961 4135309469025110932323721)
    ·
      refine ⟨3101482101768833199242791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4135309469025110932323721 3101482101768833199242791)
      ·
        refine ⟨4652223152653249798864187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3101482101768833199242791 4652223152653249798864187)
        ·
          refine ⟨6978334728979874698296281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652223152653249798864187 6978334728979874698296281)
          ·
            refine ⟨5233751046734906023722211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6978334728979874698296281 5233751046734906023722211)
            ·
              refine ⟨7850626570102359035583317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233751046734906023722211 7850626570102359035583317)
              ·
                refine ⟨45999765059193509974121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7850626570102359035583317 45999765059193509974121)
                ·
                  rfl

theorem cell23_2418774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 9].length) (baseStart_2418774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418774 prefixEnd_2418774 := by exact prefixLift 2418774
  have htrace : WordTrace (prefixWord ++ tailWord_2418774) baseStart_2418774 baseEnd_2418774 := by
    simpa [prefixWord, tailWord_2418774, baseEnd_2418774] using wordTrace_append hprefix tailTrace_2418774
  have hstable : (prefixWord ++ tailWord_2418774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418774).length < 2 ^ (prefixWord ++ tailWord_2418774).sum := by decide
  have hdescent : baseEnd_2418774 < baseStart_2418774 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418868 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_2418868 : Nat := 118140960795 + 2418868 * 2 ^ 59
def prefixEnd_2418868 : Nat := 4983230072969 + 3 ^ 40 * 2418868 * 2
def baseEnd_2418868 : Nat := 414013974593249133841945

theorem tailTrace_2418868 : CollatzResearch.WordTrace tailWord_2418868 prefixEnd_2418868 414013974593249133841945 := by
  unfold tailWord_2418868
  simp only [CollatzResearch.WordTrace]
  refine ⟨44111681900430910305080629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58815575867241213740107505 44111681900430910305080629)
  ·
    refine ⟨4135470178165397841101309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44111681900430910305080629 4135470178165397841101309)
    ·
      refine ⟨1550801316812024190412991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4135470178165397841101309 1550801316812024190412991)
      ·
        refine ⟨2326201975218036285619487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1550801316812024190412991 2326201975218036285619487)
        ·
          refine ⟨3489302962827054428429231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326201975218036285619487 3489302962827054428429231)
          ·
            refine ⟨5233954444240581642643847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489302962827054428429231 5233954444240581642643847)
            ·
              refine ⟨7850931666360872463965771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5233954444240581642643847 7850931666360872463965771)
              ·
                refine ⟨11776397499541308695948657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7850931666360872463965771 11776397499541308695948657)
                ·
                  refine ⟨8832298124655981521961493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11776397499541308695948657 8832298124655981521961493)
                  ·
                    refine ⟨414013974593249133841945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8832298124655981521961493 414013974593249133841945)
                    ·
                      rfl

theorem cell23_2418868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_2418868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418868 prefixEnd_2418868 := by exact prefixLift 2418868
  have htrace : WordTrace (prefixWord ++ tailWord_2418868) baseStart_2418868 baseEnd_2418868 := by
    simpa [prefixWord, tailWord_2418868, baseEnd_2418868] using wordTrace_append hprefix tailTrace_2418868
  have hstable : (prefixWord ++ tailWord_2418868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418868).length < 2 ^ (prefixWord ++ tailWord_2418868).sum := by decide
  have hdescent : baseEnd_2418868 < baseStart_2418868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418894 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_2418894 : Nat := 118140960795 + 2418894 * 2 ^ 59
def prefixEnd_2418894 : Nat := 4983230072969 + 3 ^ 40 * 2418894 * 2
def baseEnd_2418894 : Nat := 414018424758921433266905

theorem tailTrace_2418894 : CollatzResearch.WordTrace tailWord_2418894 prefixEnd_2418894 414018424758921433266905 := by
  unfold tailWord_2418894
  simp only [CollatzResearch.WordTrace]
  refine ⟨11028039012345953381325967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58816208065845084700405157 11028039012345953381325967)
  ·
    refine ⟨16542058518518930071988951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11028039012345953381325967 16542058518518930071988951)
    ·
      refine ⟨24813087777778395107983427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16542058518518930071988951 24813087777778395107983427)
      ·
        refine ⟨37219631666667592661975141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24813087777778395107983427 37219631666667592661975141)
        ·
          refine ⟨6978680937500173624120339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37219631666667592661975141 6978680937500173624120339)
          ·
            refine ⟨10468021406250260436180509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978680937500173624120339 10468021406250260436180509)
            ·
              refine ⟨3925508027343847663567691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10468021406250260436180509 3925508027343847663567691)
              ·
                refine ⟨5888262041015771495351537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925508027343847663567691 5888262041015771495351537)
                ·
                  refine ⟨4416196530761828621513653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5888262041015771495351537 4416196530761828621513653)
                  ·
                    refine ⟨414018424758921433266905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4416196530761828621513653 414018424758921433266905)
                    ·
                      rfl

theorem cell23_2418894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_2418894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418894 prefixEnd_2418894 := by exact prefixLift 2418894
  have htrace : WordTrace (prefixWord ++ tailWord_2418894) baseStart_2418894 baseEnd_2418894 := by
    simpa [prefixWord, tailWord_2418894, baseEnd_2418894] using wordTrace_append hprefix tailTrace_2418894
  have hstable : (prefixWord ++ tailWord_2418894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418894).length < 2 ^ (prefixWord ++ tailWord_2418894).sum := by decide
  have hdescent : baseEnd_2418894 < baseStart_2418894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418924 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_2418924 : Nat := 118140960795 + 2418924 * 2 ^ 59
def prefixEnd_2418924 : Nat := 4983230072969 + 3 ^ 40 * 2418924 * 2
def baseEnd_2418924 : Nat := 414023559565466394141859

theorem tailTrace_2418924 : CollatzResearch.WordTrace tailWord_2418924 prefixEnd_2418924 414023559565466394141859 := by
  unfold tailWord_2418924
  simp only [CollatzResearch.WordTrace]
  refine ⟨44112703144329471087099913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58816937525772628116133217 44112703144329471087099913)
  ·
    refine ⟨33084527358247103315324935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44112703144329471087099913 33084527358247103315324935)
    ·
      refine ⟨49626791037370654972987403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33084527358247103315324935 49626791037370654972987403)
      ·
        refine ⟨74440186556055982459481105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49626791037370654972987403 74440186556055982459481105)
        ·
          refine ⟨55830139917041986844610829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74440186556055982459481105 55830139917041986844610829)
          ·
            refine ⟨20936302468890745066729061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55830139917041986844610829 20936302468890745066729061)
            ·
              refine ⟨3925556712917014700011699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20936302468890745066729061 3925556712917014700011699)
              ·
                refine ⟨5888335069375522050017549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925556712917014700011699 5888335069375522050017549)
                ·
                  refine ⟨2208125651015820768756581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5888335069375522050017549 2208125651015820768756581)
                  ·
                    refine ⟨414023559565466394141859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208125651015820768756581 414023559565466394141859)
                    ·
                      rfl

theorem cell23_2418924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_2418924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418924 prefixEnd_2418924 := by exact prefixLift 2418924
  have htrace : WordTrace (prefixWord ++ tailWord_2418924) baseStart_2418924 baseEnd_2418924 := by
    simpa [prefixWord, tailWord_2418924, baseEnd_2418924] using wordTrace_append hprefix tailTrace_2418924
  have hstable : (prefixWord ++ tailWord_2418924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418924).length < 2 ^ (prefixWord ++ tailWord_2418924).sum := by decide
  have hdescent : baseEnd_2418924 < baseStart_2418924 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418934 : List Nat := [5, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_2418934 : Nat := 118140960795 + 2418934 * 2 ^ 59
def prefixEnd_2418934 : Nat := 4983230072969 + 3 ^ 40 * 2418934 * 2
def baseEnd_2418934 : Nat := 1242075813502944143300531

theorem tailTrace_2418934 : CollatzResearch.WordTrace tailWord_2418934 prefixEnd_2418934 1242075813502944143300531 := by
  unfold tailWord_2418934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5514110688663919617628991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58817180679081809254709237 5514110688663919617628991)
  ·
    refine ⟨8271166032995879426443487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5514110688663919617628991 8271166032995879426443487)
    ·
      refine ⟨12406749049493819139665231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8271166032995879426443487 12406749049493819139665231)
      ·
        refine ⟨18610123574240728709497847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12406749049493819139665231 18610123574240728709497847)
        ·
          refine ⟨27915185361361093064246771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18610123574240728709497847 27915185361361093064246771)
          ·
            refine ⟨41872778042041639596370157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27915185361361093064246771 41872778042041639596370157)
            ·
              refine ⟨15702291765765614848638809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41872778042041639596370157 15702291765765614848638809)
              ·
                refine ⟨11776718824324211136479107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15702291765765614848638809 11776718824324211136479107)
                ·
                  refine ⟨17665078236486316704718661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11776718824324211136479107 17665078236486316704718661)
                  ·
                    refine ⟨3312202169341184382134749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17665078236486316704718661 3312202169341184382134749)
                    ·
                      refine ⟨1242075813502944143300531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312202169341184382134749 1242075813502944143300531)
                      ·
                        rfl

theorem cell23_2418934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_2418934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418934 prefixEnd_2418934 := by exact prefixLift 2418934
  have htrace : WordTrace (prefixWord ++ tailWord_2418934) baseStart_2418934 baseEnd_2418934 := by
    simpa [prefixWord, tailWord_2418934, baseEnd_2418934] using wordTrace_append hprefix tailTrace_2418934
  have hstable : (prefixWord ++ tailWord_2418934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418934).length < 2 ^ (prefixWord ++ tailWord_2418934).sum := by decide
  have hdescent : baseEnd_2418934 < baseStart_2418934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2418947 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 3]
def baseStart_2418947 : Nat := 118140960795 + 2418947 * 2 ^ 59
def prefixEnd_2418947 : Nat := 4983230072969 + 3 ^ 40 * 2418947 * 2
def baseEnd_2418947 : Nat := 1242082488751452592437971

theorem tailTrace_2418947 : CollatzResearch.WordTrace tailWord_2418947 prefixEnd_2418947 1242082488751452592437971 := by
  unfold tailWord_2418947
  simp only [CollatzResearch.WordTrace]
  refine ⟨88226245167575617102287095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58817496778383744734858063 88226245167575617102287095)
  ·
    refine ⟨132339367751363425653430643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88226245167575617102287095 132339367751363425653430643)
    ·
      refine ⟨198509051627045138480145965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132339367751363425653430643 198509051627045138480145965)
      ·
        refine ⟨74440894360141926930054737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198509051627045138480145965 74440894360141926930054737)
        ·
          refine ⟨55830670770106445197541053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74440894360141926930054737 55830670770106445197541053)
          ·
            refine ⟨20936501538789916949077895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55830670770106445197541053 20936501538789916949077895)
            ·
              refine ⟨31404752308184875423616843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20936501538789916949077895 31404752308184875423616843)
              ·
                refine ⟨47107128462277313135425265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31404752308184875423616843 47107128462277313135425265)
                ·
                  refine ⟨35330346346707984851568949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47107128462277313135425265 35330346346707984851568949)
                  ·
                    refine ⟨3312219970003873579834589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35330346346707984851568949 3312219970003873579834589)
                    ·
                      refine ⟨1242082488751452592437971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312219970003873579834589 1242082488751452592437971)
                      ·
                        rfl

theorem cell23_2418947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_2418947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2418947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2418947 prefixEnd_2418947 := by exact prefixLift 2418947
  have htrace : WordTrace (prefixWord ++ tailWord_2418947) baseStart_2418947 baseEnd_2418947 := by
    simpa [prefixWord, tailWord_2418947, baseEnd_2418947] using wordTrace_append hprefix tailTrace_2418947
  have hstable : (prefixWord ++ tailWord_2418947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2418947).length < 2 ^ (prefixWord ++ tailWord_2418947).sum := by decide
  have hdescent : baseEnd_2418947 < baseStart_2418947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2418947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419001 : List Nat := [1, 2, 1, 6, 1, 1, 3, 2, 1, 5]
def baseStart_2419001 : Nat := 118140960795 + 2419001 * 2 ^ 59
def prefixEnd_2419001 : Nat := 4983230072969 + 3 ^ 40 * 2419001 * 2
def baseEnd_2419001 : Nat := 414036738902265127054241

theorem tailTrace_2419001 : CollatzResearch.WordTrace tailWord_2419001 prefixEnd_2419001 414036738902265127054241 := by
  unfold tailWord_2419001
  simp only [CollatzResearch.WordTrace]
  refine ⟨88228214709379984324752857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58818809806253322883168571 88228214709379984324752857)
  ·
    refine ⟨66171161032034988243564643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88228214709379984324752857 66171161032034988243564643)
    ·
      refine ⟨99256741548052482365346965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66171161032034988243564643 99256741548052482365346965)
      ·
        refine ⟨4652659760064960110875639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 99256741548052482365346965 4652659760064960110875639)
        ·
          refine ⟨6978989640097440166313459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4652659760064960110875639 6978989640097440166313459)
          ·
            refine ⟨10468484460146160249470189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6978989640097440166313459 10468484460146160249470189)
            ·
              refine ⟨3925681672554810093551321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10468484460146160249470189 3925681672554810093551321)
              ·
                refine ⟨2944261254416107570163491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3925681672554810093551321 2944261254416107570163491)
                ·
                  refine ⟨4416391881624161355245237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944261254416107570163491 4416391881624161355245237)
                  ·
                    refine ⟨414036738902265127054241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4416391881624161355245237 414036738902265127054241)
                    ·
                      rfl

theorem cell23_2419001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 2, 1, 5].length) (baseStart_2419001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419001 prefixEnd_2419001 := by exact prefixLift 2419001
  have htrace : WordTrace (prefixWord ++ tailWord_2419001) baseStart_2419001 baseEnd_2419001 := by
    simpa [prefixWord, tailWord_2419001, baseEnd_2419001] using wordTrace_append hprefix tailTrace_2419001
  have hstable : (prefixWord ++ tailWord_2419001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419001).length < 2 ^ (prefixWord ++ tailWord_2419001).sum := by decide
  have hdescent : baseEnd_2419001 < baseStart_2419001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419004 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2419004 : Nat := 118140960795 + 2419004 * 2 ^ 59
def prefixEnd_2419004 : Nat := 4983230072969 + 3 ^ 40 * 2419004 * 2
def baseEnd_2419004 : Nat := 1242111757148758869425209

theorem tailTrace_2419004 : CollatzResearch.WordTrace tailWord_2419004 prefixEnd_2419004 1242111757148758869425209 := by
  unfold tailWord_2419004
  simp only [CollatzResearch.WordTrace]
  refine ⟨44114162064184557918556033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58818882752246077224741377 44114162064184557918556033)
  ·
    refine ⟨33085621548138418438917025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44114162064184557918556033 33085621548138418438917025)
    ·
      refine ⟨24814216161103813829187769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33085621548138418438917025 24814216161103813829187769)
      ·
        refine ⟨18610662120827860371890827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24814216161103813829187769 18610662120827860371890827)
        ·
          refine ⟨27915993181241790557836241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18610662120827860371890827 27915993181241790557836241)
          ·
            refine ⟨20936994885931342918377181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27915993181241790557836241 20936994885931342918377181)
            ·
              refine ⟨7851373082224253594391443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20936994885931342918377181 7851373082224253594391443)
              ·
                refine ⟨11777059623336380391587165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7851373082224253594391443 11777059623336380391587165)
                ·
                  refine ⟨4416397358751142646845187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11777059623336380391587165 4416397358751142646845187)
                  ·
                    refine ⟨6624596038126713970267781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4416397358751142646845187 6624596038126713970267781)
                    ·
                      refine ⟨1242111757148758869425209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6624596038126713970267781 1242111757148758869425209)
                      ·
                        rfl

theorem cell23_2419004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2419004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419004 prefixEnd_2419004 := by exact prefixLift 2419004
  have htrace : WordTrace (prefixWord ++ tailWord_2419004) baseStart_2419004 baseEnd_2419004 := by
    simpa [prefixWord, tailWord_2419004, baseEnd_2419004] using wordTrace_append hprefix tailTrace_2419004
  have hstable : (prefixWord ++ tailWord_2419004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419004).length < 2 ^ (prefixWord ++ tailWord_2419004).sum := by decide
  have hdescent : baseEnd_2419004 < baseStart_2419004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419024 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5]
def baseStart_2419024 : Nat := 118140960795 + 2419024 * 2 ^ 59
def prefixEnd_2419024 : Nat := 4983230072969 + 3 ^ 40 * 2419024 * 2
def baseEnd_2419024 : Nat := 1242122026761848791175117

theorem tailTrace_2419024 : CollatzResearch.WordTrace tailWord_2419024 prefixEnd_2419024 1242122026761848791175117 := by
  unfold tailWord_2419024
  simp only [CollatzResearch.WordTrace]
  refine ⟨44114526794148329626420063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58819369058864439501893417 44114526794148329626420063)
  ·
    refine ⟨66171790191222494439630095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44114526794148329626420063 66171790191222494439630095)
    ·
      refine ⟨99257685286833741659445143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66171790191222494439630095 99257685286833741659445143)
      ·
        refine ⟨148886527930250612489167715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99257685286833741659445143 148886527930250612489167715)
        ·
          refine ⟨223329791895375918733751573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148886527930250612489167715 223329791895375918733751573)
          ·
            refine ⟨10468583995095746190644605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 223329791895375918733751573 10468583995095746190644605)
            ·
              refine ⟨3925718998160904821491727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10468583995095746190644605 3925718998160904821491727)
              ·
                refine ⟨5888578497241357232237591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925718998160904821491727 5888578497241357232237591)
                ·
                  refine ⟨8832867745862035848356387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888578497241357232237591 8832867745862035848356387)
                  ·
                    refine ⟨13249301618793053772534581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8832867745862035848356387 13249301618793053772534581)
                    ·
                      refine ⟨1242122026761848791175117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13249301618793053772534581 1242122026761848791175117)
                      ·
                        rfl

theorem cell23_2419024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 5].length) (baseStart_2419024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419024 prefixEnd_2419024 := by exact prefixLift 2419024
  have htrace : WordTrace (prefixWord ++ tailWord_2419024) baseStart_2419024 baseEnd_2419024 := by
    simpa [prefixWord, tailWord_2419024, baseEnd_2419024] using wordTrace_append hprefix tailTrace_2419024
  have hstable : (prefixWord ++ tailWord_2419024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419024).length < 2 ^ (prefixWord ++ tailWord_2419024).sum := by decide
  have hdescent : baseEnd_2419024 < baseStart_2419024 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419031 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 2, 4]
def baseStart_2419031 : Nat := 118140960795 + 2419031 * 2 ^ 59
def prefixEnd_2419031 : Nat := 4983230072969 + 3 ^ 40 * 2419031 * 2
def baseEnd_2419031 : Nat := 414041873708810087929195

theorem tailTrace_2419031 : CollatzResearch.WordTrace tailWord_2419031 prefixEnd_2419031 414041873708810087929195 := by
  unfold tailWord_2419031
  simp only [CollatzResearch.WordTrace]
  refine ⟨88229308899271299448344947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58819539266180866298896631 88229308899271299448344947)
  ·
    refine ⟨132343963348906949172517421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88229308899271299448344947 132343963348906949172517421)
    ·
      refine ⟨49628986255840105939694033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132343963348906949172517421 49628986255840105939694033)
      ·
        refine ⟨37221739691880079454770525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49628986255840105939694033 37221739691880079454770525)
        ·
          refine ⟨13958152384455029795538947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37221739691880079454770525 13958152384455029795538947)
          ·
            refine ⟨20937228576682544693308421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13958152384455029795538947 20937228576682544693308421)
            ·
              refine ⟨3925730358127977129995329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20937228576682544693308421 3925730358127977129995329)
              ·
                refine ⟨2944297768595982847496497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3925730358127977129995329 2944297768595982847496497)
                ·
                  refine ⟨2208223326446987135622373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944297768595982847496497 2208223326446987135622373)
                  ·
                    refine ⟨414041873708810087929195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208223326446987135622373 414041873708810087929195)
                    ·
                      rfl

theorem cell23_2419031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 2, 4].length) (baseStart_2419031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419031 prefixEnd_2419031 := by exact prefixLift 2419031
  have htrace : WordTrace (prefixWord ++ tailWord_2419031) baseStart_2419031 baseEnd_2419031 := by
    simpa [prefixWord, tailWord_2419031, baseEnd_2419031] using wordTrace_append hprefix tailTrace_2419031
  have hstable : (prefixWord ++ tailWord_2419031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419031).length < 2 ^ (prefixWord ++ tailWord_2419031).sum := by decide
  have hdescent : baseEnd_2419031 < baseStart_2419031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419057 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 4, 7]
def baseStart_2419057 : Nat := 118140960795 + 2419057 * 2 ^ 59
def prefixEnd_2419057 : Nat := 4983230072969 + 3 ^ 40 * 2419057 * 2
def baseEnd_2419057 : Nat := 414046323874482387354155

theorem tailTrace_2419057 : CollatzResearch.WordTrace tailWord_2419057 prefixEnd_2419057 414046323874482387354155 := by
  unfold tailWord_2419057
  simp only [CollatzResearch.WordTrace]
  refine ⟨88230257197177105888791425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58820171464784737259194283 88230257197177105888791425)
  ·
    refine ⟨66172692897882829416593569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88230257197177105888791425 66172692897882829416593569)
    ·
      refine ⟨49629519673412122062445177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66172692897882829416593569 49629519673412122062445177)
      ·
        refine ⟨37222139755059091546833883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49629519673412122062445177 37222139755059091546833883)
        ·
          refine ⟨55833209632588637320250825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37222139755059091546833883 55833209632588637320250825)
          ·
            refine ⟨41874907224441477990188119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55833209632588637320250825 41874907224441477990188119)
            ·
              refine ⟨62812360836662216985282179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41874907224441477990188119 62812360836662216985282179)
              ·
                refine ⟨94218541254993325477923269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62812360836662216985282179 94218541254993325477923269)
                ·
                  refine ⟨17665976485311248527110613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94218541254993325477923269 17665976485311248527110613)
                  ·
                    refine ⟨414046323874482387354155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17665976485311248527110613 414046323874482387354155)
                    ·
                      rfl

theorem cell23_2419057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_2419057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419057 prefixEnd_2419057 := by exact prefixLift 2419057
  have htrace : WordTrace (prefixWord ++ tailWord_2419057) baseStart_2419057 baseEnd_2419057 := by
    simpa [prefixWord, tailWord_2419057, baseEnd_2419057] using wordTrace_append hprefix tailTrace_2419057
  have hstable : (prefixWord ++ tailWord_2419057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419057).length < 2 ^ (prefixWord ++ tailWord_2419057).sum := by decide
  have hdescent : baseEnd_2419057 < baseStart_2419057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419061 : List Nat := [1, 3, 4, 1, 2, 2, 3, 7]
def baseStart_2419061 : Nat := 118140960795 + 2419061 * 2 ^ 59
def prefixEnd_2419061 : Nat := 4983230072969 + 3 ^ 40 * 2419061 * 2
def baseEnd_2419061 : Nat := 46005223168372783200461

theorem tailTrace_2419061 : CollatzResearch.WordTrace tailWord_2419061 prefixEnd_2419061 46005223168372783200461 := by
  unfold tailWord_2419061
  simp only [CollatzResearch.WordTrace]
  refine ⟨88230403089162614571937037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58820268726108409714624691 88230403089162614571937037)
  ·
    refine ⟨33086401158435980464476389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88230403089162614571937037 33086401158435980464476389)
    ·
      refine ⟨6203700217206746337089323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33086401158435980464476389 6203700217206746337089323)
      ·
        refine ⟨9305550325810119505633985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6203700217206746337089323 9305550325810119505633985)
        ·
          refine ⟨6979162744357589629225489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9305550325810119505633985 6979162744357589629225489)
          ·
            refine ⟨5234372058268192221919117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6979162744357589629225489 5234372058268192221919117)
            ·
              refine ⟨1962889521850572083219669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5234372058268192221919117 1962889521850572083219669)
              ·
                refine ⟨46005223168372783200461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1962889521850572083219669 46005223168372783200461)
                ·
                  rfl

theorem cell23_2419061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 7].length) (baseStart_2419061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419061 prefixEnd_2419061 := by exact prefixLift 2419061
  have htrace : WordTrace (prefixWord ++ tailWord_2419061) baseStart_2419061 baseEnd_2419061 := by
    simpa [prefixWord, tailWord_2419061, baseEnd_2419061] using wordTrace_append hprefix tailTrace_2419061
  have hstable : (prefixWord ++ tailWord_2419061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419061).length < 2 ^ (prefixWord ++ tailWord_2419061).sum := by decide
  have hdescent : baseEnd_2419061 < baseStart_2419061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419075 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 1, 2, 3]
def baseStart_2419075 : Nat := 118140960795 + 2419075 * 2 ^ 59
def prefixEnd_2419075 : Nat := 4983230072969 + 3 ^ 40 * 2419075 * 2
def baseEnd_2419075 : Nat := 1242148214275228091637383

theorem tailTrace_2419075 : CollatzResearch.WordTrace tailWord_2419075 prefixEnd_2419075 1242148214275228091637383 := by
  unfold tailWord_2419075
  simp only [CollatzResearch.WordTrace]
  refine ⟨88230913711111894962946679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58820609140741263308631119 88230913711111894962946679)
  ·
    refine ⟨132346370566667842444420019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88230913711111894962946679 132346370566667842444420019)
    ·
      refine ⟨198519555850001763666630029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132346370566667842444420019 198519555850001763666630029)
      ·
        refine ⟨74444833443750661374986261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198519555850001763666630029 74444833443750661374986261)
        ·
          refine ⟨3489601567675812251952481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74444833443750661374986261 3489601567675812251952481)
          ·
            refine ⟨2617201175756859188964361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3489601567675812251952481 2617201175756859188964361)
            ·
              refine ⟨1962900881817644391723271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2617201175756859188964361 1962900881817644391723271)
              ·
                refine ⟨2944351322726466587584907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962900881817644391723271 2944351322726466587584907)
                ·
                  refine ⟨4416526984089699881377361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944351322726466587584907 4416526984089699881377361)
                  ·
                    refine ⟨3312395238067274911033021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4416526984089699881377361 3312395238067274911033021)
                    ·
                      refine ⟨1242148214275228091637383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312395238067274911033021 1242148214275228091637383)
                      ·
                        rfl

theorem cell23_2419075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 1, 2, 3].length) (baseStart_2419075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419075 prefixEnd_2419075 := by exact prefixLift 2419075
  have htrace : WordTrace (prefixWord ++ tailWord_2419075) baseStart_2419075 baseEnd_2419075 := by
    simpa [prefixWord, tailWord_2419075, baseEnd_2419075] using wordTrace_append hprefix tailTrace_2419075
  have hstable : (prefixWord ++ tailWord_2419075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419075).length < 2 ^ (prefixWord ++ tailWord_2419075).sum := by decide
  have hdescent : baseEnd_2419075 < baseStart_2419075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419082 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 2, 4]
def baseStart_2419082 : Nat := 118140960795 + 2419082 * 2 ^ 59
def prefixEnd_2419082 : Nat := 4983230072969 + 3 ^ 40 * 2419082 * 2
def baseEnd_2419082 : Nat := 414050602879936521416617

theorem tailTrace_2419082 : CollatzResearch.WordTrace tailWord_2419082 prefixEnd_2419082 414050602879936521416617 := by
  unfold tailWord_2419082
  simp only [CollatzResearch.WordTrace]
  refine ⟨22057792255521633789612875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58820779348057690105634333 22057792255521633789612875)
  ·
    refine ⟨33086688383282450684419313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22057792255521633789612875 33086688383282450684419313)
    ·
      refine ⟨24815016287461838013314485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33086688383282450684419313 24815016287461838013314485)
      ·
        refine ⟨2326407776949547313748233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24815016287461838013314485 2326407776949547313748233)
        ·
          refine ⟨1744805832712160485311175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2326407776949547313748233 1744805832712160485311175)
          ·
            refine ⟨2617208749068240727966763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1744805832712160485311175 2617208749068240727966763)
            ·
              refine ⟨3925813123602361091950145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617208749068240727966763 3925813123602361091950145)
              ·
                refine ⟨2944359842701770818962609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3925813123602361091950145 2944359842701770818962609)
                ·
                  refine ⟨2208269882026328114221957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944359842701770818962609 2208269882026328114221957)
                  ·
                    refine ⟨414050602879936521416617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208269882026328114221957 414050602879936521416617)
                    ·
                      rfl

theorem cell23_2419082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_2419082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419082 prefixEnd_2419082 := by exact prefixLift 2419082
  have htrace : WordTrace (prefixWord ++ tailWord_2419082) baseStart_2419082 baseEnd_2419082 := by
    simpa [prefixWord, tailWord_2419082, baseEnd_2419082] using wordTrace_append hprefix tailTrace_2419082
  have hstable : (prefixWord ++ tailWord_2419082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419082).length < 2 ^ (prefixWord ++ tailWord_2419082).sum := by decide
  have hdescent : baseEnd_2419082 < baseStart_2419082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419104 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 2, 6]
def baseStart_2419104 : Nat := 118140960795 + 2419104 * 2 ^ 59
def prefixEnd_2419104 : Nat := 4983230072969 + 3 ^ 40 * 2419104 * 2
def baseEnd_2419104 : Nat := 414054368404736159391583

theorem tailTrace_2419104 : CollatzResearch.WordTrace tailWord_2419104 prefixEnd_2419104 414054368404736159391583 := by
  unfold tailWord_2419104
  simp only [CollatzResearch.WordTrace]
  refine ⟨44115985714003416457876183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58821314285337888610501577 44115985714003416457876183)
  ·
    refine ⟨66173978571005124686814275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44115985714003416457876183 66173978571005124686814275)
    ·
      refine ⟨99260967856507687030221413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66173978571005124686814275 99260967856507687030221413)
      ·
        refine ⟨18611431473095191318166515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99260967856507687030221413 18611431473095191318166515)
        ·
          refine ⟨27917147209642786977249773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18611431473095191318166515 27917147209642786977249773)
          ·
            refine ⟨10468930203616045116468665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27917147209642786977249773 10468930203616045116468665)
            ·
              refine ⟨7851697652712033837351499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10468930203616045116468665 7851697652712033837351499)
              ·
                refine ⟨11777546479068050756027249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7851697652712033837351499 11777546479068050756027249)
                ·
                  refine ⟨8833159859301038067020437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11777546479068050756027249 8833159859301038067020437)
                  ·
                    refine ⟨414054368404736159391583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8833159859301038067020437 414054368404736159391583)
                    ·
                      rfl

theorem cell23_2419104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_2419104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419104 prefixEnd_2419104 := by exact prefixLift 2419104
  have htrace : WordTrace (prefixWord ++ tailWord_2419104) baseStart_2419104 baseEnd_2419104 := by
    simpa [prefixWord, tailWord_2419104, baseEnd_2419104] using wordTrace_append hprefix tailTrace_2419104
  have hstable : (prefixWord ++ tailWord_2419104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419104).length < 2 ^ (prefixWord ++ tailWord_2419104).sum := by decide
  have hdescent : baseEnd_2419104 < baseStart_2419104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419105 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2419105 : Nat := 118140960795 + 2419105 * 2 ^ 59
def prefixEnd_2419105 : Nat := 4983230072969 + 3 ^ 40 * 2419105 * 2
def baseEnd_2419105 : Nat := 1242163618694862974262245

theorem tailTrace_2419105 : CollatzResearch.WordTrace tailWord_2419105 prefixEnd_2419105 1242163618694862974262245 := by
  unfold tailWord_2419105
  simp only [CollatzResearch.WordTrace]
  refine ⟨88232007901003210086538769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58821338600668806724359179 88232007901003210086538769)
  ·
    refine ⟨66174005925752407564904077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88232007901003210086538769 66174005925752407564904077)
    ·
      refine ⟨24815252222157152836839029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66174005925752407564904077 24815252222157152836839029)
      ·
        refine ⟨2326429895827233078453659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24815252222157152836839029 2326429895827233078453659)
        ·
          refine ⟨3489644843740849617680489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326429895827233078453659 3489644843740849617680489)
          ·
            refine ⟨2617233632805637213260367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3489644843740849617680489 2617233632805637213260367)
            ·
              refine ⟨3925850449208455819890551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617233632805637213260367 3925850449208455819890551)
              ·
                refine ⟨5888775673812683729835827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3925850449208455819890551 5888775673812683729835827)
                ·
                  refine ⟨8833163510719025594753741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5888775673812683729835827 8833163510719025594753741)
                  ·
                    refine ⟨3312436316519634598032653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8833163510719025594753741 3312436316519634598032653)
                    ·
                      refine ⟨1242163618694862974262245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312436316519634598032653 1242163618694862974262245)
                      ·
                        rfl

theorem cell23_2419105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2419105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419105 prefixEnd_2419105 := by exact prefixLift 2419105
  have htrace : WordTrace (prefixWord ++ tailWord_2419105) baseStart_2419105 baseEnd_2419105 := by
    simpa [prefixWord, tailWord_2419105, baseEnd_2419105] using wordTrace_append hprefix tailTrace_2419105
  have hstable : (prefixWord ++ tailWord_2419105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419105).length < 2 ^ (prefixWord ++ tailWord_2419105).sum := by decide
  have hdescent : baseEnd_2419105 < baseStart_2419105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419134 : List Nat := [4, 2, 1, 1, 1, 1, 2, 2, 9]
def baseStart_2419134 : Nat := 118140960795 + 2419134 * 2 ^ 59
def prefixEnd_2419134 : Nat := 4983230072969 + 3 ^ 40 * 2419134 * 2
def baseEnd_2419134 : Nat := 138019834403760373422179

theorem tailTrace_2419134 : CollatzResearch.WordTrace tailWord_2419134 prefixEnd_2419134 138019834403760373422179 := by
  unfold tailWord_2419134
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029133202237268504918057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58822043745265432026229637 11029133202237268504918057)
  ·
    refine ⟨8271849901677951378688543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11029133202237268504918057 8271849901677951378688543)
    ·
      refine ⟨12407774852516927068032815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8271849901677951378688543 12407774852516927068032815)
      ·
        refine ⟨18611662278775390602049223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12407774852516927068032815 18611662278775390602049223)
        ·
          refine ⟨27917493418163085903073835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18611662278775390602049223 27917493418163085903073835)
          ·
            refine ⟨41876240127244628854610753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27917493418163085903073835 41876240127244628854610753)
            ·
              refine ⟨31407180095433471640958065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41876240127244628854610753 31407180095433471640958065)
              ·
                refine ⟨23555385071575103730718549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31407180095433471640958065 23555385071575103730718549)
                ·
                  refine ⟨138019834403760373422179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23555385071575103730718549 138019834403760373422179)
                  ·
                    rfl

theorem cell23_2419134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_2419134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419134 prefixEnd_2419134 := by exact prefixLift 2419134
  have htrace : WordTrace (prefixWord ++ tailWord_2419134) baseStart_2419134 baseEnd_2419134 := by
    simpa [prefixWord, tailWord_2419134, baseEnd_2419134] using wordTrace_append hprefix tailTrace_2419134
  have hstable : (prefixWord ++ tailWord_2419134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419134).length < 2 ^ (prefixWord ++ tailWord_2419134).sum := by decide
  have hdescent : baseEnd_2419134 < baseStart_2419134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419221 : List Nat := [1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_2419221 : Nat := 118140960795 + 2419221 * 2 ^ 59
def prefixEnd_2419221 : Nat := 4983230072969 + 3 ^ 40 * 2419221 * 2
def baseEnd_2419221 : Nat := 1242223182450784520411711

theorem tailTrace_2419221 : CollatzResearch.WordTrace tailWord_2419221 prefixEnd_2419221 1242223182450784520411711 := by
  unfold tailWord_2419221
  simp only [CollatzResearch.WordTrace]
  refine ⟨88236238768582961897761517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58824159179055307931841011 88236238768582961897761517)
  ·
    refine ⟨33088589538218610711660569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88236238768582961897761517 33088589538218610711660569)
    ·
      refine ⟨24816442153663958033745427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33088589538218610711660569 24816442153663958033745427)
      ·
        refine ⟨37224663230495937050618141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24816442153663958033745427 37224663230495937050618141)
        ·
          refine ⟨13959248711435976393981803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37224663230495937050618141 13959248711435976393981803)
          ·
            refine ⟨20938873067153964590972705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13959248711435976393981803 20938873067153964590972705)
            ·
              refine ⟨15704154800365473443229529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20938873067153964590972705 15704154800365473443229529)
              ·
                refine ⟨11778116100274105082422147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15704154800365473443229529 11778116100274105082422147)
                ·
                  refine ⟨17667174150411157623633221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11778116100274105082422147 17667174150411157623633221)
                  ·
                    refine ⟨3312595153202092054431229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17667174150411157623633221 3312595153202092054431229)
                    ·
                      refine ⟨1242223182450784520411711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312595153202092054431229 1242223182450784520411711)
                      ·
                        rfl

theorem cell23_2419221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_2419221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419221 prefixEnd_2419221 := by exact prefixLift 2419221
  have htrace : WordTrace (prefixWord ++ tailWord_2419221) baseStart_2419221 baseEnd_2419221 := by
    simpa [prefixWord, tailWord_2419221, baseEnd_2419221] using wordTrace_append hprefix tailTrace_2419221
  have hstable : (prefixWord ++ tailWord_2419221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419221).length < 2 ^ (prefixWord ++ tailWord_2419221).sum := by decide
  have hdescent : baseEnd_2419221 < baseStart_2419221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419228 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2419228 : Nat := 118140960795 + 2419228 * 2 ^ 59
def prefixEnd_2419228 : Nat := 4983230072969 + 3 ^ 40 * 2419228 * 2
def baseEnd_2419228 : Nat := 414075592271788664341393

theorem tailTrace_2419228 : CollatzResearch.WordTrace tailWord_2419228 prefixEnd_2419228 414075592271788664341393 := by
  unfold tailWord_2419228
  simp only [CollatzResearch.WordTrace]
  refine ⟨44118247039778801046633169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58824329386371734728844225 44118247039778801046633169)
  ·
    refine ⟨33088685279834100784974877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44118247039778801046633169 33088685279834100784974877)
    ·
      refine ⟨12408256979937787794365579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33088685279834100784974877 12408256979937787794365579)
      ·
        refine ⟨18612385469906681691548369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12408256979937787794365579 18612385469906681691548369)
        ·
          refine ⟨13959289102430011268661277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18612385469906681691548369 13959289102430011268661277)
          ·
            refine ⟨5234733413411254225747979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13959289102430011268661277 5234733413411254225747979)
            ·
              refine ⟨7852100120116881338621969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5234733413411254225747979 7852100120116881338621969)
              ·
                refine ⟨5889075090087661003966477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7852100120116881338621969 5889075090087661003966477)
                ·
                  refine ⟨2208403158782872876487429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5889075090087661003966477 2208403158782872876487429)
                  ·
                    refine ⟨414075592271788664341393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208403158782872876487429 414075592271788664341393)
                    ·
                      rfl

theorem cell23_2419228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2419228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419228 prefixEnd_2419228 := by exact prefixLift 2419228
  have htrace : WordTrace (prefixWord ++ tailWord_2419228) baseStart_2419228 baseEnd_2419228 := by
    simpa [prefixWord, tailWord_2419228, baseEnd_2419228] using wordTrace_append hprefix tailTrace_2419228
  have hstable : (prefixWord ++ tailWord_2419228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419228).length < 2 ^ (prefixWord ++ tailWord_2419228).sum := by decide
  have hdescent : baseEnd_2419228 < baseStart_2419228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419244 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 6]
def baseStart_2419244 : Nat := 118140960795 + 2419244 * 2 ^ 59
def prefixEnd_2419244 : Nat := 4983230072969 + 3 ^ 40 * 2419244 * 2
def baseEnd_2419244 : Nat := 1242234992505837930424105

theorem tailTrace_2419244 : CollatzResearch.WordTrace tailWord_2419244 prefixEnd_2419244 1242234992505837930424105 := by
  unfold tailWord_2419244
  simp only [CollatzResearch.WordTrace]
  refine ⟨44118538823749818412924393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58824718431666424550565857 44118538823749818412924393)
  ·
    refine ⟨33088904117812363809693295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44118538823749818412924393 33088904117812363809693295)
    ·
      refine ⟨49633356176718545714539943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33088904117812363809693295 49633356176718545714539943)
      ·
        refine ⟨74450034265077818571809915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49633356176718545714539943 74450034265077818571809915)
        ·
          refine ⟨111675051397616727857714873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74450034265077818571809915 111675051397616727857714873)
          ·
            refine ⟨83756288548212545893286155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111675051397616727857714873 83756288548212545893286155)
            ·
              refine ⟨125634432822318818839929233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83756288548212545893286155 125634432822318818839929233)
              ·
                refine ⟨94225824616739114129946925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125634432822318818839929233 94225824616739114129946925)
                ·
                  refine ⟨35334684231277167798730097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94225824616739114129946925 35334684231277167798730097)
                  ·
                    refine ⟨26501013173457875849047573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35334684231277167798730097 26501013173457875849047573)
                    ·
                      refine ⟨1242234992505837930424105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26501013173457875849047573 1242234992505837930424105)
                      ·
                        rfl

theorem cell23_2419244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_2419244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419244 prefixEnd_2419244 := by exact prefixLift 2419244
  have htrace : WordTrace (prefixWord ++ tailWord_2419244) baseStart_2419244 baseEnd_2419244 := by
    simpa [prefixWord, tailWord_2419244, baseEnd_2419244] using wordTrace_append hprefix tailTrace_2419244
  have hstable : (prefixWord ++ tailWord_2419244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419244).length < 2 ^ (prefixWord ++ tailWord_2419244).sum := by decide
  have hdescent : baseEnd_2419244 < baseStart_2419244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419258 : List Nat := [3, 1, 1, 1, 3, 5, 1, 2, 6]
def baseStart_2419258 : Nat := 118140960795 + 2419258 * 2 ^ 59
def prefixEnd_2419258 : Nat := 4983230072969 + 3 ^ 40 * 2419258 * 2
def baseEnd_2419258 : Nat := 138026909026111208405449

theorem tailTrace_2419258 : CollatzResearch.WordTrace tailWord_2419258 prefixEnd_2419258 138026909026111208405449 := by
  unfold tailWord_2419258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22059397067362229304214607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58825058846299278144572285 22059397067362229304214607)
  ·
    refine ⟨33089095601043343956321911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22059397067362229304214607 33089095601043343956321911)
    ·
      refine ⟨49633643401565015934482867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33089095601043343956321911 49633643401565015934482867)
      ·
        refine ⟨74450465102347523901724301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49633643401565015934482867 74450465102347523901724301)
        ·
          refine ⟨27918924413380321463146613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74450465102347523901724301 27918924413380321463146613)
          ·
            refine ⟨2617399163754405137169995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27918924413380321463146613 2617399163754405137169995)
            ·
              refine ⟨3926098745631607705754993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617399163754405137169995 3926098745631607705754993)
              ·
                refine ⟨2944574059223705779316245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3926098745631607705754993 2944574059223705779316245)
                ·
                  refine ⟨138026909026111208405449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2944574059223705779316245 138026909026111208405449)
                  ·
                    rfl

theorem cell23_2419258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 2, 6].length) (baseStart_2419258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419258 prefixEnd_2419258 := by exact prefixLift 2419258
  have htrace : WordTrace (prefixWord ++ tailWord_2419258) baseStart_2419258 baseEnd_2419258 := by
    simpa [prefixWord, tailWord_2419258, baseEnd_2419258] using wordTrace_append hprefix tailTrace_2419258
  have hstable : (prefixWord ++ tailWord_2419258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419258).length < 2 ^ (prefixWord ++ tailWord_2419258).sum := by decide
  have hdescent : baseEnd_2419258 < baseStart_2419258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419261 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2419261 : Nat := 118140960795 + 2419261 * 2 ^ 59
def prefixEnd_2419261 : Nat := 4983230072969 + 3 ^ 40 * 2419261 * 2
def baseEnd_2419261 : Nat := 1242243721676964363911527

theorem tailTrace_2419261 : CollatzResearch.WordTrace tailWord_2419261 prefixEnd_2419261 1242243721676964363911527 := by
  unfold tailWord_2419261
  simp only [CollatzResearch.WordTrace]
  refine ⟨88237697688438048729217637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58825131792292032486145091 88237697688438048729217637)
  ·
    refine ⟨16544568316582134136728307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88237697688438048729217637 16544568316582134136728307)
    ·
      refine ⟨24816852474873201205092461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16544568316582134136728307 24816852474873201205092461)
      ·
        refine ⟨9306319678077450451909673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24816852474873201205092461 9306319678077450451909673)
        ·
          refine ⟨6979739758558087838932255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9306319678077450451909673 6979739758558087838932255)
          ·
            refine ⟨10469609637837131758398383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979739758558087838932255 10469609637837131758398383)
            ·
              refine ⟨15704414456755697637597575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10469609637837131758398383 15704414456755697637597575)
              ·
                refine ⟨23556621685133546456396363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15704414456755697637597575 23556621685133546456396363)
                ·
                  refine ⟨35334932527700319684594545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23556621685133546456396363 35334932527700319684594545)
                  ·
                    refine ⟨26501199395775239763445909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35334932527700319684594545 26501199395775239763445909)
                    ·
                      refine ⟨1242243721676964363911527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26501199395775239763445909 1242243721676964363911527)
                      ·
                        rfl

theorem cell23_2419261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2419261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419261 prefixEnd_2419261 := by exact prefixLift 2419261
  have htrace : WordTrace (prefixWord ++ tailWord_2419261) baseStart_2419261 baseEnd_2419261 := by
    simpa [prefixWord, tailWord_2419261, baseEnd_2419261] using wordTrace_append hprefix tailTrace_2419261
  have hstable : (prefixWord ++ tailWord_2419261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419261).length < 2 ^ (prefixWord ++ tailWord_2419261).sum := by decide
  have hdescent : baseEnd_2419261 < baseStart_2419261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419262 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 3, 4]
def baseStart_2419262 : Nat := 118140960795 + 2419262 * 2 ^ 59
def prefixEnd_2419262 : Nat := 4983230072969 + 3 ^ 40 * 2419262 * 2
def baseEnd_2419262 : Nat := 414081411719206286666341

theorem tailTrace_2419262 : CollatzResearch.WordTrace tailWord_2419262 prefixEnd_2419262 414081411719206286666341 := by
  unfold tailWord_2419262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029716770179303237500505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58825156107622950600002693 11029716770179303237500505)
  ·
    refine ⟨8272287577634477428125379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11029716770179303237500505 8272287577634477428125379)
    ·
      refine ⟨12408431366451716142188069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8272287577634477428125379 12408431366451716142188069)
      ·
        refine ⟨2326580881209696776660263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12408431366451716142188069 2326580881209696776660263)
        ·
          refine ⟨3489871321814545164990395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326580881209696776660263 3489871321814545164990395)
          ·
            refine ⟨5234806982721817747485593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489871321814545164990395 5234806982721817747485593)
            ·
              refine ⟨3926105237041363310614195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5234806982721817747485593 3926105237041363310614195)
              ·
                refine ⟨5889157855562044965921293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926105237041363310614195 5889157855562044965921293)
                ·
                  refine ⟨2208434195835766862220485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5889157855562044965921293 2208434195835766862220485)
                  ·
                    refine ⟨414081411719206286666341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208434195835766862220485 414081411719206286666341)
                    ·
                      rfl

theorem cell23_2419262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_2419262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419262 prefixEnd_2419262 := by exact prefixLift 2419262
  have htrace : WordTrace (prefixWord ++ tailWord_2419262) baseStart_2419262 baseEnd_2419262 := by
    simpa [prefixWord, tailWord_2419262, baseEnd_2419262] using wordTrace_append hprefix tailTrace_2419262
  have hstable : (prefixWord ++ tailWord_2419262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419262).length < 2 ^ (prefixWord ++ tailWord_2419262).sum := by decide
  have hdescent : baseEnd_2419262 < baseStart_2419262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419278 : List Nat := [4, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2]
def baseStart_2419278 : Nat := 118140960795 + 2419278 * 2 ^ 59
def prefixEnd_2419278 : Nat := 4983230072969 + 3 ^ 40 * 2419278 * 2
def baseEnd_2419278 : Nat := 1242252450848090797398949

theorem tailTrace_2419278 : CollatzResearch.WordTrace tailWord_2419278 prefixEnd_2419278 1242252450848090797398949 := by
  unfold tailWord_2419278
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029789716172057579073311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58825545152917640421724325 11029789716172057579073311)
  ·
    refine ⟨16544684574258086368609967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11029789716172057579073311 16544684574258086368609967)
    ·
      refine ⟨24817026861387129552914951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16544684574258086368609967 24817026861387129552914951)
      ·
        refine ⟨37225540292080694329372427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24817026861387129552914951 37225540292080694329372427)
        ·
          refine ⟨55838310438121041494058641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37225540292080694329372427 55838310438121041494058641)
          ·
            refine ⟨41878732828590781120543981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55838310438121041494058641 41878732828590781120543981)
            ·
              refine ⟨15704524810721542920203993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41878732828590781120543981 15704524810721542920203993)
              ·
                refine ⟨11778393608041157190152995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15704524810721542920203993 11778393608041157190152995)
                ·
                  refine ⟨17667590412061735785229493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11778393608041157190152995 17667590412061735785229493)
                  ·
                    refine ⟨1656336601130787729865265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17667590412061735785229493 1656336601130787729865265)
                    ·
                      refine ⟨1242252450848090797398949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1656336601130787729865265 1242252450848090797398949)
                      ·
                        rfl

theorem cell23_2419278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2].length) (baseStart_2419278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419278 prefixEnd_2419278 := by exact prefixLift 2419278
  have htrace : WordTrace (prefixWord ++ tailWord_2419278) baseStart_2419278 baseEnd_2419278 := by
    simpa [prefixWord, tailWord_2419278, baseEnd_2419278] using wordTrace_append hprefix tailTrace_2419278
  have hstable : (prefixWord ++ tailWord_2419278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419278).length < 2 ^ (prefixWord ++ tailWord_2419278).sum := by decide
  have hdescent : baseEnd_2419278 < baseStart_2419278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419308 : List Nat := [2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 4]
def baseStart_2419308 : Nat := 118140960795 + 2419308 * 2 ^ 59
def prefixEnd_2419308 : Nat := 4983230072969 + 3 ^ 40 * 2419308 * 2
def baseEnd_2419308 : Nat := 1242267855267725680023811

theorem tailTrace_2419308 : CollatzResearch.WordTrace tailWord_2419308 prefixEnd_2419308 1242267855267725680023811 := by
  unfold tailWord_2419308
  simp only [CollatzResearch.WordTrace]
  refine ⟨44119705959633887878089289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58826274612845183837452385 44119705959633887878089289)
  ·
    refine ⟨33089779469725415908566967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44119705959633887878089289 33089779469725415908566967)
    ·
      refine ⟨49634669204588123862850451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33089779469725415908566967 49634669204588123862850451)
      ·
        refine ⟨74452003806882185794275677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49634669204588123862850451 74452003806882185794275677)
        ·
          refine ⟨27919501427580819672853379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74452003806882185794275677 27919501427580819672853379)
          ·
            refine ⟨41879252141371229509280069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27919501427580819672853379 41879252141371229509280069)
            ·
              refine ⟨7852359776507105532990013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41879252141371229509280069 7852359776507105532990013)
              ·
                refine ⟨2944634916190164574871255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7852359776507105532990013 2944634916190164574871255)
                ·
                  refine ⟨4416952374285246862306883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944634916190164574871255 4416952374285246862306883)
                  ·
                    refine ⟨6625428561427870293460325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4416952374285246862306883 6625428561427870293460325)
                    ·
                      refine ⟨1242267855267725680023811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6625428561427870293460325 1242267855267725680023811)
                      ·
                        rfl

theorem cell23_2419308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_2419308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419308 prefixEnd_2419308 := by exact prefixLift 2419308
  have htrace : WordTrace (prefixWord ++ tailWord_2419308) baseStart_2419308 baseEnd_2419308 := by
    simpa [prefixWord, tailWord_2419308, baseEnd_2419308] using wordTrace_append hprefix tailTrace_2419308
  have hstable : (prefixWord ++ tailWord_2419308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419308).length < 2 ^ (prefixWord ++ tailWord_2419308).sum := by decide
  have hdescent : baseEnd_2419308 < baseStart_2419308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419311 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 5]
def baseStart_2419311 : Nat := 118140960795 + 2419311 * 2 ^ 59
def prefixEnd_2419311 : Nat := 4983230072969 + 3 ^ 40 * 2419311 * 2
def baseEnd_2419311 : Nat := 1242269395709689168286297

theorem tailTrace_2419311 : CollatzResearch.WordTrace tailWord_2419311 prefixEnd_2419311 1242269395709689168286297 := by
  unfold tailWord_2419311
  simp only [CollatzResearch.WordTrace]
  refine ⟨88239521338256907268537787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58826347558837938179025191 88239521338256907268537787)
  ·
    refine ⟨132359282007385360902806681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88239521338256907268537787 132359282007385360902806681)
    ·
      refine ⟨99269461505539020677105011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132359282007385360902806681 99269461505539020677105011)
      ·
        refine ⟨148904192258308531015657517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99269461505539020677105011 148904192258308531015657517)
        ·
          refine ⟨55839072096865699130871569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148904192258308531015657517 55839072096865699130871569)
          ·
            refine ⟨41879304072649274348153677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55839072096865699130871569 41879304072649274348153677)
            ·
              refine ⟨15704739027243477880557629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41879304072649274348153677 15704739027243477880557629)
              ·
                refine ⟨5889277135216304205209111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15704739027243477880557629 5889277135216304205209111)
                ·
                  refine ⟨8833915702824456307813667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889277135216304205209111 8833915702824456307813667)
                  ·
                    refine ⟨13250873554236684461720501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8833915702824456307813667 13250873554236684461720501)
                    ·
                      refine ⟨1242269395709689168286297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13250873554236684461720501 1242269395709689168286297)
                      ·
                        rfl

theorem cell23_2419311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 5].length) (baseStart_2419311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419311 prefixEnd_2419311 := by exact prefixLift 2419311
  have htrace : WordTrace (prefixWord ++ tailWord_2419311) baseStart_2419311 baseEnd_2419311 := by
    simpa [prefixWord, tailWord_2419311, baseEnd_2419311] using wordTrace_append hprefix tailTrace_2419311
  have hstable : (prefixWord ++ tailWord_2419311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419311).length < 2 ^ (prefixWord ++ tailWord_2419311).sum := by decide
  have hdescent : baseEnd_2419311 < baseStart_2419311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419321 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2419321 : Nat := 118140960795 + 2419321 * 2 ^ 59
def prefixEnd_2419321 : Nat := 4983230072969 + 3 ^ 40 * 2419321 * 2
def baseEnd_2419321 : Nat := 1242274530516234129161251

theorem tailTrace_2419321 : CollatzResearch.WordTrace tailWord_2419321 prefixEnd_2419321 1242274530516234129161251 := by
  unfold tailWord_2419321
  simp only [CollatzResearch.WordTrace]
  refine ⟨88239886068220678976401817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58826590712147119317601211 88239886068220678976401817)
  ·
    refine ⟨66179914551165509232301363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88239886068220678976401817 66179914551165509232301363)
    ·
      refine ⟨99269871826748263848452045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66179914551165509232301363 99269871826748263848452045)
      ·
        refine ⟨37226201935030598943169517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99269871826748263848452045 37226201935030598943169517)
        ·
          refine ⟨13959825725636474603688569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37226201935030598943169517 13959825725636474603688569)
          ·
            refine ⟨10469869294227355952766427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13959825725636474603688569 10469869294227355952766427)
            ·
              refine ⟨15704803941341033929149641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10469869294227355952766427 15704803941341033929149641)
              ·
                refine ⟨11778602956005775446862231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15704803941341033929149641 11778602956005775446862231)
                ·
                  refine ⟨17667904434008663170293347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11778602956005775446862231 17667904434008663170293347)
                  ·
                    refine ⟨26501856651012994755440021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17667904434008663170293347 26501856651012994755440021)
                    ·
                      refine ⟨1242274530516234129161251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26501856651012994755440021 1242274530516234129161251)
                      ·
                        rfl

theorem cell23_2419321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2419321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419321 prefixEnd_2419321 := by exact prefixLift 2419321
  have htrace : WordTrace (prefixWord ++ tailWord_2419321) baseStart_2419321 baseEnd_2419321 := by
    simpa [prefixWord, tailWord_2419321, baseEnd_2419321] using wordTrace_append hprefix tailTrace_2419321
  have hstable : (prefixWord ++ tailWord_2419321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419321).length < 2 ^ (prefixWord ++ tailWord_2419321).sum := by decide
  have hdescent : baseEnd_2419321 < baseStart_2419321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419348 : List Nat := [2, 4, 2, 2, 1, 1, 2, 9]
def baseStart_2419348 : Nat := 118140960795 + 2419348 * 2 ^ 59
def prefixEnd_2419348 : Nat := 4983230072969 + 3 ^ 40 * 2419348 * 2
def baseEnd_2419348 : Nat := 46010681277552056426801

theorem tailTrace_2419348 : CollatzResearch.WordTrace tailWord_2419348 prefixEnd_2419348 46010681277552056426801 := by
  unfold tailWord_2419348
  simp only [CollatzResearch.WordTrace]
  refine ⟨44120435419561431293817349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58827247226081908391756465 44120435419561431293817349)
  ·
    refine ⟨8272581641167768367590753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44120435419561431293817349 8272581641167768367590753)
    ·
      refine ⟨6204436230875826275693065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8272581641167768367590753 6204436230875826275693065)
      ·
        refine ⟨4653327173156869706769799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6204436230875826275693065 4653327173156869706769799)
        ·
          refine ⟨6979990759735304560154699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653327173156869706769799 6979990759735304560154699)
          ·
            refine ⟨10469986139602956840232049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979990759735304560154699 10469986139602956840232049)
            ·
              refine ⟨7852489604702217630174037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10469986139602956840232049 7852489604702217630174037)
              ·
                refine ⟨46010681277552056426801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7852489604702217630174037 46010681277552056426801)
                ·
                  rfl

theorem cell23_2419348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 9].length) (baseStart_2419348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419348 prefixEnd_2419348 := by exact prefixLift 2419348
  have htrace : WordTrace (prefixWord ++ tailWord_2419348) baseStart_2419348 baseEnd_2419348 := by
    simpa [prefixWord, tailWord_2419348, baseEnd_2419348] using wordTrace_append hprefix tailTrace_2419348
  have hstable : (prefixWord ++ tailWord_2419348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419348).length < 2 ^ (prefixWord ++ tailWord_2419348).sum := by decide
  have hdescent : baseEnd_2419348 < baseStart_2419348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419370 : List Nat := [3, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2419370 : Nat := 118140960795 + 2419370 * 2 ^ 59
def prefixEnd_2419370 : Nat := 4983230072969 + 3 ^ 40 * 2419370 * 2
def baseEnd_2419370 : Nat := 1242299691068304437448527

theorem tailTrace_2419370 : CollatzResearch.WordTrace tailWord_2419370 prefixEnd_2419370 1242299691068304437448527 := by
  unfold tailWord_2419370
  simp only [CollatzResearch.WordTrace]
  refine ⟨22060418311260790086233891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58827782163362106896623709 22060418311260790086233891)
  ·
    refine ⟨33090627466891185129350837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22060418311260790086233891 33090627466891185129350837)
    ·
      refine ⟨3102246325021048605876641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33090627466891185129350837 3102246325021048605876641)
      ·
        refine ⟨2326684743765786454407481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3102246325021048605876641 2326684743765786454407481)
        ·
          refine ⟨1745013557824339840805611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2326684743765786454407481 1745013557824339840805611)
          ·
            refine ⟨2617520336736509761208417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1745013557824339840805611 2617520336736509761208417)
            ·
              refine ⟨1963140252552382320906313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2617520336736509761208417 1963140252552382320906313)
              ·
                refine ⟨1472355189414286740679735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963140252552382320906313 1472355189414286740679735)
                ·
                  refine ⟨2208532784121430111019603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472355189414286740679735 2208532784121430111019603)
                  ·
                    refine ⟨3312799176182145166529405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2208532784121430111019603 3312799176182145166529405)
                    ·
                      refine ⟨1242299691068304437448527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312799176182145166529405 1242299691068304437448527)
                      ·
                        rfl

theorem cell23_2419370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2419370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419370 prefixEnd_2419370 := by exact prefixLift 2419370
  have htrace : WordTrace (prefixWord ++ tailWord_2419370) baseStart_2419370 baseEnd_2419370 := by
    simpa [prefixWord, tailWord_2419370, baseEnd_2419370] using wordTrace_append hprefix tailTrace_2419370
  have hstable : (prefixWord ++ tailWord_2419370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419370).length < 2 ^ (prefixWord ++ tailWord_2419370).sum := by decide
  have hdescent : baseEnd_2419370 < baseStart_2419370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419375 : List Nat := [1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 3]
def baseStart_2419375 : Nat := 118140960795 + 2419375 * 2 ^ 59
def prefixEnd_2419375 : Nat := 4983230072969 + 3 ^ 40 * 2419375 * 2
def baseEnd_2419375 : Nat := 1242302258471576917886003

theorem tailTrace_2419375 : CollatzResearch.WordTrace tailWord_2419375 prefixEnd_2419375 1242302258471576917886003 := by
  unfold tailWord_2419375
  simp only [CollatzResearch.WordTrace]
  refine ⟨88241855610025046198867579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58827903740016697465911719 88241855610025046198867579)
  ·
    refine ⟨132362783415037569298301369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88241855610025046198867579 132362783415037569298301369)
    ·
      refine ⟨99272087561278176973726027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132362783415037569298301369 99272087561278176973726027)
      ·
        refine ⟨148908131341917265460589041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99272087561278176973726027 148908131341917265460589041)
        ·
          refine ⟨111681098506437949095441781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148908131341917265460589041 111681098506437949095441781)
          ·
            refine ⟨10470102984978557727697667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111681098506437949095441781 10470102984978557727697667)
            ·
              refine ⟨15705154477467836591546501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470102984978557727697667 15705154477467836591546501)
              ·
                refine ⟨2944716464525219360914969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15705154477467836591546501 2944716464525219360914969)
                ·
                  refine ⟨2208537348393914520686227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2944716464525219360914969 2208537348393914520686227)
                  ·
                    refine ⟨3312806022590871781029341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2208537348393914520686227 3312806022590871781029341)
                    ·
                      refine ⟨1242302258471576917886003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312806022590871781029341 1242302258471576917886003)
                      ·
                        rfl

theorem cell23_2419375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 4, 2, 1, 3].length) (baseStart_2419375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419375 prefixEnd_2419375 := by exact prefixLift 2419375
  have htrace : WordTrace (prefixWord ++ tailWord_2419375) baseStart_2419375 baseEnd_2419375 := by
    simpa [prefixWord, tailWord_2419375, baseEnd_2419375] using wordTrace_append hprefix tailTrace_2419375
  have hstable : (prefixWord ++ tailWord_2419375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419375).length < 2 ^ (prefixWord ++ tailWord_2419375).sum := by decide
  have hdescent : baseEnd_2419375 < baseStart_2419375 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419382 : List Nat := [5, 1, 3, 1, 2, 2, 1, 8]
def baseStart_2419382 : Nat := 118140960795 + 2419382 * 2 ^ 59
def prefixEnd_2419382 : Nat := 4983230072969 + 3 ^ 40 * 2419382 * 2
def baseEnd_2419382 : Nat := 46011327882820681129573

theorem tailTrace_2419382 : CollatzResearch.WordTrace tailWord_2419382 prefixEnd_2419382 46011327882820681129573 := by
  unfold tailWord_2419382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5515131932562480399648275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58828073947333124262914933 5515131932562480399648275)
  ·
    refine ⟨8272697898843720599472413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5515131932562480399648275 8272697898843720599472413)
    ·
      refine ⟨3102261712066395224802155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8272697898843720599472413 3102261712066395224802155)
      ·
        refine ⟨4653392568099592837203233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102261712066395224802155 4653392568099592837203233)
        ·
          refine ⟨3490044426074694627902425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4653392568099592837203233 3490044426074694627902425)
          ·
            refine ⟨2617533319556020970926819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490044426074694627902425 2617533319556020970926819)
            ·
              refine ⟨3926299979334031456390229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617533319556020970926819 3926299979334031456390229)
              ·
                refine ⟨46011327882820681129573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3926299979334031456390229 46011327882820681129573)
                ·
                  rfl

theorem cell23_2419382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_2419382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419382 prefixEnd_2419382 := by exact prefixLift 2419382
  have htrace : WordTrace (prefixWord ++ tailWord_2419382) baseStart_2419382 baseEnd_2419382 := by
    simpa [prefixWord, tailWord_2419382, baseEnd_2419382] using wordTrace_append hprefix tailTrace_2419382
  have hstable : (prefixWord ++ tailWord_2419382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419382).length < 2 ^ (prefixWord ++ tailWord_2419382).sum := by decide
  have hdescent : baseEnd_2419382 < baseStart_2419382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419391 : List Nat := [1, 1, 2, 2, 2, 4, 1, 1, 1, 8]
def baseStart_2419391 : Nat := 118140960795 + 2419391 * 2 ^ 59
def prefixEnd_2419391 : Nat := 4983230072969 + 3 ^ 40 * 2419391 * 2
def baseEnd_2419391 : Nat := 414103491387349618428643

theorem tailTrace_2419391 : CollatzResearch.WordTrace tailWord_2419391 prefixEnd_2419391 414103491387349618428643 := by
  unfold tailWord_2419391
  simp only [CollatzResearch.WordTrace]
  refine ⟨88242439177967080931450027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58828292785311387287633351 88242439177967080931450027)
  ·
    refine ⟨132363658766950621397175041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88242439177967080931450027 132363658766950621397175041)
    ·
      refine ⟨99272744075212966047881281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132363658766950621397175041 99272744075212966047881281)
      ·
        refine ⟨74454558056409724535910961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99272744075212966047881281 74454558056409724535910961)
        ·
          refine ⟨55840918542307293401933221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74454558056409724535910961 55840918542307293401933221)
          ·
            refine ⟨10470172226682617512862479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55840918542307293401933221 10470172226682617512862479)
            ·
              refine ⟨15705258340023926269293719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470172226682617512862479 15705258340023926269293719)
              ·
                refine ⟨23557887510035889403940579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15705258340023926269293719 23557887510035889403940579)
                ·
                  refine ⟨35336831265053834105910869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23557887510035889403940579 35336831265053834105910869)
                  ·
                    refine ⟨414103491387349618428643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35336831265053834105910869 414103491387349618428643)
                    ·
                      rfl

theorem cell23_2419391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 8].length) (baseStart_2419391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419391 prefixEnd_2419391 := by exact prefixLift 2419391
  have htrace : WordTrace (prefixWord ++ tailWord_2419391) baseStart_2419391 baseEnd_2419391 := by
    simpa [prefixWord, tailWord_2419391, baseEnd_2419391] using wordTrace_append hprefix tailTrace_2419391
  have hstable : (prefixWord ++ tailWord_2419391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419391).length < 2 ^ (prefixWord ++ tailWord_2419391).sum := by decide
  have hdescent : baseEnd_2419391 < baseStart_2419391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419415 : List Nat := [1, 1, 3, 2, 1, 4, 2, 2, 1, 4, 2]
def baseStart_2419415 : Nat := 118140960795 + 2419415 * 2 ^ 59
def prefixEnd_2419415 : Nat := 4983230072969 + 3 ^ 40 * 2419415 * 2
def baseEnd_2419415 : Nat := 1242322797697756761385819

theorem tailTrace_2419415 : CollatzResearch.WordTrace tailWord_2419415 prefixEnd_2419415 1242322797697756761385819 := by
  unfold tailWord_2419415
  simp only [CollatzResearch.WordTrace]
  refine ⟨88243314529880133030323699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58828876353253422020215799 88243314529880133030323699)
  ·
    refine ⟨132364971794820199545485549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88243314529880133030323699 132364971794820199545485549)
    ·
      refine ⟨49636864423057574829557081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132364971794820199545485549 49636864423057574829557081)
      ·
        refine ⟨37227648317293181122167811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49636864423057574829557081 37227648317293181122167811)
        ·
          refine ⟨55841472475939771683251717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37227648317293181122167811 55841472475939771683251717)
          ·
            refine ⟨10470276089238707190609697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55841472475939771683251717 10470276089238707190609697)
            ·
              refine ⟨7852707066929030392957273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10470276089238707190609697 7852707066929030392957273)
              ·
                refine ⟨5889530300196772794717955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7852707066929030392957273 5889530300196772794717955)
                ·
                  refine ⟨8834295450295159192076933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5889530300196772794717955 8834295450295159192076933)
                  ·
                    refine ⟨1656430396930342348514425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8834295450295159192076933 1656430396930342348514425)
                    ·
                      refine ⟨1242322797697756761385819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1656430396930342348514425 1242322797697756761385819)
                      ·
                        rfl

theorem cell23_2419415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 2, 1, 4, 2].length) (baseStart_2419415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419415 prefixEnd_2419415 := by exact prefixLift 2419415
  have htrace : WordTrace (prefixWord ++ tailWord_2419415) baseStart_2419415 baseEnd_2419415 := by
    simpa [prefixWord, tailWord_2419415, baseEnd_2419415] using wordTrace_append hprefix tailTrace_2419415
  have hstable : (prefixWord ++ tailWord_2419415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419415).length < 2 ^ (prefixWord ++ tailWord_2419415).sum := by decide
  have hdescent : baseEnd_2419415 < baseStart_2419415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419428 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 2, 2, 4]
def baseStart_2419428 : Nat := 118140960795 + 2419428 * 2 ^ 59
def prefixEnd_2419428 : Nat := 4983230072969 + 3 ^ 40 * 2419428 * 2
def baseEnd_2419428 : Nat := 1242329472946265210523259

theorem tailTrace_2419428 : CollatzResearch.WordTrace tailWord_2419428 prefixEnd_2419428 1242329472946265210523259 := by
  unfold tailWord_2419428
  simp only [CollatzResearch.WordTrace]
  refine ⟨44121894339416518125273469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58829192452555357500364625 44121894339416518125273469)
  ·
    refine ⟨16545710377281194296977551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44121894339416518125273469 16545710377281194296977551)
    ·
      refine ⟨24818565565921791445466327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16545710377281194296977551 24818565565921791445466327)
      ·
        refine ⟨37227848348882687168199491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24818565565921791445466327 37227848348882687168199491)
        ·
          refine ⟨55841772523324030752299237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37227848348882687168199491 55841772523324030752299237)
          ·
            refine ⟨10470332348123255766056107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55841772523324030752299237 10470332348123255766056107)
            ·
              refine ⟨15705498522184883649084161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470332348123255766056107 15705498522184883649084161)
              ·
                refine ⟨11779123891638662736813121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15705498522184883649084161 11779123891638662736813121)
                ·
                  refine ⟨8834342918728997052609841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11779123891638662736813121 8834342918728997052609841)
                  ·
                    refine ⟨6625757189046747789457381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8834342918728997052609841 6625757189046747789457381)
                    ·
                      refine ⟨1242329472946265210523259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6625757189046747789457381 1242329472946265210523259)
                      ·
                        rfl

theorem cell23_2419428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_2419428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419428 prefixEnd_2419428 := by exact prefixLift 2419428
  have htrace : WordTrace (prefixWord ++ tailWord_2419428) baseStart_2419428 baseEnd_2419428 := by
    simpa [prefixWord, tailWord_2419428, baseEnd_2419428] using wordTrace_append hprefix tailTrace_2419428
  have hstable : (prefixWord ++ tailWord_2419428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419428).length < 2 ^ (prefixWord ++ tailWord_2419428).sum := by decide
  have hdescent : baseEnd_2419428 < baseStart_2419428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419438 : List Nat := [4, 1, 2, 1, 1, 3, 1, 3, 7]
def baseStart_2419438 : Nat := 118140960795 + 2419438 * 2 ^ 59
def prefixEnd_2419438 : Nat := 4983230072969 + 3 ^ 40 * 2419438 * 2
def baseEnd_2419438 : Nat := 138037178639201130155357

theorem tailTrace_2419438 : CollatzResearch.WordTrace tailWord_2419438 prefixEnd_2419438 138037178639201130155357 := by
  unfold tailWord_2419438
  simp only [CollatzResearch.WordTrace]
  refine ⟨11030519176099600994801371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58829435605864538638940645 11030519176099600994801371)
  ·
    refine ⟨16545778764149401492202057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11030519176099600994801371 16545778764149401492202057)
    ·
      refine ⟨12409334073112051119151543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16545778764149401492202057 12409334073112051119151543)
      ·
        refine ⟨18614001109668076678727315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12409334073112051119151543 18614001109668076678727315)
        ·
          refine ⟨27921001664502115018090973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18614001109668076678727315 27921001664502115018090973)
          ·
            refine ⟨10470375624188293131784115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27921001664502115018090973 10470375624188293131784115)
            ·
              refine ⟨15705563436282439697676173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470375624188293131784115 15705563436282439697676173)
              ·
                refine ⟨5889586288605914886628565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15705563436282439697676173 5889586288605914886628565)
                ·
                  refine ⟨138037178639201130155357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5889586288605914886628565 138037178639201130155357)
                  ·
                    rfl

theorem cell23_2419438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 3, 7].length) (baseStart_2419438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419438 prefixEnd_2419438 := by exact prefixLift 2419438
  have htrace : WordTrace (prefixWord ++ tailWord_2419438) baseStart_2419438 baseEnd_2419438 := by
    simpa [prefixWord, tailWord_2419438, baseEnd_2419438] using wordTrace_append hprefix tailTrace_2419438
  have hstable : (prefixWord ++ tailWord_2419438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419438).length < 2 ^ (prefixWord ++ tailWord_2419438).sum := by decide
  have hdescent : baseEnd_2419438 < baseStart_2419438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419448 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3]
def baseStart_2419448 : Nat := 118140960795 + 2419448 * 2 ^ 59
def prefixEnd_2419448 : Nat := 4983230072969 + 3 ^ 40 * 2419448 * 2
def baseEnd_2419448 : Nat := 1242339742559355132273167

theorem tailTrace_2419448 : CollatzResearch.WordTrace tailWord_2419448 prefixEnd_2419448 1242339742559355132273167 := by
  unfold tailWord_2419448
  simp only [CollatzResearch.WordTrace]
  refine ⟨44122259069380289833137499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58829678759173719777516665 44122259069380289833137499)
  ·
    refine ⟨66183388604070434749706249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44122259069380289833137499 66183388604070434749706249)
    ·
      refine ⟨49637541453052826062279687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66183388604070434749706249 49637541453052826062279687)
      ·
        refine ⟨74456312179579239093419531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49637541453052826062279687 74456312179579239093419531)
        ·
          refine ⟨111684468269368858640129297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74456312179579239093419531 111684468269368858640129297)
          ·
            refine ⟨83763351202026643980096973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111684468269368858640129297 83763351202026643980096973)
            ·
              refine ⟨31411256700759991492536365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83763351202026643980096973 31411256700759991492536365)
              ·
                refine ⟨11779221262784996809701137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31411256700759991492536365 11779221262784996809701137)
                ·
                  refine ⟨8834415947088747607275853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11779221262784996809701137 8834415947088747607275853)
                  ·
                    refine ⟨3312905980158280352728445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8834415947088747607275853 3312905980158280352728445)
                    ·
                      refine ⟨1242339742559355132273167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3312905980158280352728445 1242339742559355132273167)
                      ·
                        rfl

theorem cell23_2419448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 2, 3, 3].length) (baseStart_2419448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419448 prefixEnd_2419448 := by exact prefixLift 2419448
  have htrace : WordTrace (prefixWord ++ tailWord_2419448) baseStart_2419448 baseEnd_2419448 := by
    simpa [prefixWord, tailWord_2419448, baseEnd_2419448] using wordTrace_append hprefix tailTrace_2419448
  have hstable : (prefixWord ++ tailWord_2419448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419448).length < 2 ^ (prefixWord ++ tailWord_2419448).sum := by decide
  have hdescent : baseEnd_2419448 < baseStart_2419448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419468 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_2419468 : Nat := 118140960795 + 2419468 * 2 ^ 59
def prefixEnd_2419468 : Nat := 4983230072969 + 3 ^ 40 * 2419468 * 2
def baseEnd_2419468 : Nat := 414116670724148351341025

theorem tailTrace_2419468 : CollatzResearch.WordTrace tailWord_2419468 prefixEnd_2419468 414116670724148351341025 := by
  unfold tailWord_2419468
  simp only [CollatzResearch.WordTrace]
  refine ⟨44122623799344061541001529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58830165065792082054668705 44122623799344061541001529)
  ·
    refine ⟨33091967849508046155751147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44122623799344061541001529 33091967849508046155751147)
    ·
      refine ⟨49637951774262069233626721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33091967849508046155751147 49637951774262069233626721)
      ·
        refine ⟨37228463830696551925220041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49637951774262069233626721 37228463830696551925220041)
        ·
          refine ⟨27921347873022413943915031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37228463830696551925220041 27921347873022413943915031)
          ·
            refine ⟨41882021809533620915872547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27921347873022413943915031 41882021809533620915872547)
            ·
              refine ⟨62823032714300431373808821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41882021809533620915872547 62823032714300431373808821)
              ·
                refine ⟨5889659316965665441294577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62823032714300431373808821 5889659316965665441294577)
                ·
                  refine ⟨4417244487724249080970933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5889659316965665441294577 4417244487724249080970933)
                  ·
                    refine ⟨414116670724148351341025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4417244487724249080970933 414116670724148351341025)
                    ·
                      rfl

theorem cell23_2419468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_2419468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419468 prefixEnd_2419468 := by exact prefixLift 2419468
  have htrace : WordTrace (prefixWord ++ tailWord_2419468) baseStart_2419468 baseEnd_2419468 := by
    simpa [prefixWord, tailWord_2419468, baseEnd_2419468] using wordTrace_append hprefix tailTrace_2419468
  have hstable : (prefixWord ++ tailWord_2419468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419468).length < 2 ^ (prefixWord ++ tailWord_2419468).sum := by decide
  have hdescent : baseEnd_2419468 < baseStart_2419468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419505 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 1, 6, 2]
def baseStart_2419505 : Nat := 118140960795 + 2419505 * 2 ^ 59
def prefixEnd_2419505 : Nat := 4983230072969 + 3 ^ 40 * 2419505 * 2
def baseEnd_2419505 : Nat := 1242369010956661409260405

theorem tailTrace_2419505 : CollatzResearch.WordTrace tailWord_2419505 prefixEnd_2419505 1242369010956661409260405 := by
  unfold tailWord_2419505
  simp only [CollatzResearch.WordTrace]
  refine ⟨88246597099554078401099969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58831064733036052267399979 88246597099554078401099969)
  ·
    refine ⟨66184947824665558800824977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88246597099554078401099969 66184947824665558800824977)
    ·
      refine ⟨49638710868499169100618733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66184947824665558800824977 49638710868499169100618733)
      ·
        refine ⟨18614516575687188412732025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49638710868499169100618733 18614516575687188412732025)
        ·
          refine ⟨13960887431765391309549019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18614516575687188412732025 13960887431765391309549019)
          ·
            refine ⟨20941331147648086964323529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13960887431765391309549019 20941331147648086964323529)
            ·
              refine ⟨15705998360736065223242647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20941331147648086964323529 15705998360736065223242647)
              ·
                refine ⟨23558997541104097834863971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15705998360736065223242647 23558997541104097834863971)
                ·
                  refine ⟨35338496311656146752295957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23558997541104097834863971 35338496311656146752295957)
                  ·
                    refine ⟨1656492014608881879013873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 35338496311656146752295957 1656492014608881879013873)
                    ·
                      refine ⟨1242369010956661409260405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1656492014608881879013873 1242369010956661409260405)
                      ·
                        rfl

theorem cell23_2419505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_2419505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419505 prefixEnd_2419505 := by exact prefixLift 2419505
  have htrace : WordTrace (prefixWord ++ tailWord_2419505) baseStart_2419505 baseEnd_2419505 := by
    simpa [prefixWord, tailWord_2419505, baseEnd_2419505] using wordTrace_append hprefix tailTrace_2419505
  have hstable : (prefixWord ++ tailWord_2419505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419505).length < 2 ^ (prefixWord ++ tailWord_2419505).sum := by decide
  have hdescent : baseEnd_2419505 < baseStart_2419505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419545 : List Nat := [1, 2, 1, 2, 2, 5, 2, 2, 6]
def baseStart_2419545 : Nat := 118140960795 + 2419545 * 2 ^ 59
def prefixEnd_2419545 : Nat := 4983230072969 + 3 ^ 40 * 2419545 * 2
def baseEnd_2419545 : Nat := 138043283353649028084469

theorem tailTrace_2419545 : CollatzResearch.WordTrace tailWord_2419545 prefixEnd_2419545 138043283353649028084469 := by
  unfold tailWord_2419545
  simp only [CollatzResearch.WordTrace]
  refine ⟨88248056019409165232556089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58832037346272776821704059 88248056019409165232556089)
  ·
    refine ⟨66186042014556873924417067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88248056019409165232556089 66186042014556873924417067)
    ·
      refine ⟨99279063021835310886625601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66186042014556873924417067 99279063021835310886625601)
      ·
        refine ⟨74459297266376483164969201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99279063021835310886625601 74459297266376483164969201)
        ·
          refine ⟨55844472949782362373726901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74459297266376483164969201 55844472949782362373726901)
          ·
            refine ⟨5235419339042096472536897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55844472949782362373726901 5235419339042096472536897)
            ·
              refine ⟨3926564504281572354402673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5235419339042096472536897 3926564504281572354402673)
              ·
                refine ⟨2944923378211179265802005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3926564504281572354402673 2944923378211179265802005)
                ·
                  refine ⟨138043283353649028084469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2944923378211179265802005 138043283353649028084469)
                  ·
                    rfl

theorem cell23_2419545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 2, 2, 6].length) (baseStart_2419545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419545 prefixEnd_2419545 := by exact prefixLift 2419545
  have htrace : WordTrace (prefixWord ++ tailWord_2419545) baseStart_2419545 baseEnd_2419545 := by
    simpa [prefixWord, tailWord_2419545, baseEnd_2419545] using wordTrace_append hprefix tailTrace_2419545
  have hstable : (prefixWord ++ tailWord_2419545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419545).length < 2 ^ (prefixWord ++ tailWord_2419545).sum := by decide
  have hdescent : baseEnd_2419545 < baseStart_2419545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419589 : List Nat := [1, 3, 1, 1, 3, 3, 1, 5, 1, 1, 3]
def baseStart_2419589 : Nat := 118140960795 + 2419589 * 2 ^ 59
def prefixEnd_2419589 : Nat := 4983230072969 + 3 ^ 40 * 2419589 * 2
def baseEnd_2419589 : Nat := 1242412143331639080610019

theorem tailTrace_2419589 : CollatzResearch.WordTrace tailWord_2419589 prefixEnd_2419589 1242412143331639080610019 := by
  unfold tailWord_2419589
  simp only [CollatzResearch.WordTrace]
  refine ⟨88249660831249760747157821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58833107220833173831438547 88249660831249760747157821)
  ·
    refine ⟨33093622811718660280184183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88249660831249760747157821 33093622811718660280184183)
    ·
      refine ⟨49640434217577990420276275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33093622811718660280184183 49640434217577990420276275)
      ·
        refine ⟨74460651326366985630414413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49640434217577990420276275 74460651326366985630414413)
        ·
          refine ⟨27922744247387619611405405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74460651326366985630414413 27922744247387619611405405)
          ·
            refine ⟨10471029092770357354277027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27922744247387619611405405 10471029092770357354277027)
            ·
              refine ⟨15706543639155536031415541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10471029092770357354277027 15706543639155536031415541)
              ·
                refine ⟨1472488466170831502945207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15706543639155536031415541 1472488466170831502945207)
                ·
                  refine ⟨2208732699256247254417811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472488466170831502945207 2208732699256247254417811)
                  ·
                    refine ⟨3313099048884370881626717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2208732699256247254417811 3313099048884370881626717)
                    ·
                      refine ⟨1242412143331639080610019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3313099048884370881626717 1242412143331639080610019)
                      ·
                        rfl

theorem cell23_2419589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 5, 1, 1, 3].length) (baseStart_2419589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419589 prefixEnd_2419589 := by exact prefixLift 2419589
  have htrace : WordTrace (prefixWord ++ tailWord_2419589) baseStart_2419589 baseEnd_2419589 := by
    simpa [prefixWord, tailWord_2419589, baseEnd_2419589] using wordTrace_append hprefix tailTrace_2419589
  have hstable : (prefixWord ++ tailWord_2419589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419589).length < 2 ^ (prefixWord ++ tailWord_2419589).sum := by decide
  have hdescent : baseEnd_2419589 < baseStart_2419589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419592 : List Nat := [2, 1, 3, 3, 2, 2, 1, 3, 1, 5]
def baseStart_2419592 : Nat := 118140960795 + 2419592 * 2 ^ 59
def prefixEnd_2419592 : Nat := 4983230072969 + 3 ^ 40 * 2419592 * 2
def baseEnd_2419592 : Nat := 414137894591200856290835

theorem tailTrace_2419592 : CollatzResearch.WordTrace tailWord_2419592 prefixEnd_2419592 414137894591200856290835 := by
  unfold tailWord_2419592
  simp only [CollatzResearch.WordTrace]
  refine ⟨44124885125119446129758515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58833180166825928173011353 44124885125119446129758515)
  ·
    refine ⟨66187327687679169194637773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44124885125119446129758515 66187327687679169194637773)
    ·
      refine ⟨24820247882879688447989165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66187327687679169194637773 24820247882879688447989165)
      ·
        refine ⟨9307592956079883167995937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24820247882879688447989165 9307592956079883167995937)
        ·
          refine ⟨6980694717059912375996953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9307592956079883167995937 6980694717059912375996953)
          ·
            refine ⟨5235521037794934281997715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6980694717059912375996953 5235521037794934281997715)
            ·
              refine ⟨7853281556692401422996573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5235521037794934281997715 7853281556692401422996573)
              ·
                refine ⟨2944980583759650533623715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7853281556692401422996573 2944980583759650533623715)
                ·
                  refine ⟨4417470875639475800435573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2944980583759650533623715 4417470875639475800435573)
                  ·
                    refine ⟨414137894591200856290835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4417470875639475800435573 414137894591200856290835)
                    ·
                      rfl

theorem cell23_2419592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_2419592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419592 prefixEnd_2419592 := by exact prefixLift 2419592
  have htrace : WordTrace (prefixWord ++ tailWord_2419592) baseStart_2419592 baseEnd_2419592 := by
    simpa [prefixWord, tailWord_2419592, baseEnd_2419592] using wordTrace_append hprefix tailTrace_2419592
  have hstable : (prefixWord ++ tailWord_2419592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419592).length < 2 ^ (prefixWord ++ tailWord_2419592).sum := by decide
  have hdescent : baseEnd_2419592 < baseStart_2419592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419615 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2419615 : Nat := 118140960795 + 2419615 * 2 ^ 59
def prefixEnd_2419615 : Nat := 4983230072969 + 3 ^ 40 * 2419615 * 2
def baseEnd_2419615 : Nat := 1242425493828655978884899

theorem tailTrace_2419615 : CollatzResearch.WordTrace tailWord_2419615 prefixEnd_2419615 1242425493828655978884899 := by
  unfold tailWord_2419615
  simp only [CollatzResearch.WordTrace]
  refine ⟨88250609129155567187604299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58833739419437044791736199 88250609129155567187604299)
  ·
    refine ⟨132375913693733350781406449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88250609129155567187604299 132375913693733350781406449)
    ·
      refine ⟨99281935270300013086054837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132375913693733350781406449 99281935270300013086054837)
      ·
        refine ⟨9307681431590626226817641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 99281935270300013086054837 9307681431590626226817641)
        ·
          refine ⟨6980761073692969670113231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9307681431590626226817641 6980761073692969670113231)
          ·
            refine ⟨10471141610539454505169847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6980761073692969670113231 10471141610539454505169847)
            ·
              refine ⟨15706712415809181757754771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10471141610539454505169847 15706712415809181757754771)
              ·
                refine ⟨23560068623713772636632157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15706712415809181757754771 23560068623713772636632157)
                ·
                  refine ⟨8835025733892664738737059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23560068623713772636632157 8835025733892664738737059)
                  ·
                    refine ⟨13252538600838997108105589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8835025733892664738737059 13252538600838997108105589)
                    ·
                      refine ⟨1242425493828655978884899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13252538600838997108105589 1242425493828655978884899)
                      ·
                        rfl

theorem cell23_2419615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2419615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419615 prefixEnd_2419615 := by exact prefixLift 2419615
  have htrace : WordTrace (prefixWord ++ tailWord_2419615) baseStart_2419615 baseEnd_2419615 := by
    simpa [prefixWord, tailWord_2419615, baseEnd_2419615] using wordTrace_append hprefix tailTrace_2419615
  have hstable : (prefixWord ++ tailWord_2419615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419615).length < 2 ^ (prefixWord ++ tailWord_2419615).sum := by decide
  have hdescent : baseEnd_2419615 < baseStart_2419615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419628 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 7]
def baseStart_2419628 : Nat := 118140960795 + 2419628 * 2 ^ 59
def prefixEnd_2419628 : Nat := 4983230072969 + 3 ^ 40 * 2419628 * 2
def baseEnd_2419628 : Nat := 1242432169077164428022339

theorem tailTrace_2419628 : CollatzResearch.WordTrace tailWord_2419628 prefixEnd_2419628 1242432169077164428022339 := by
  unfold tailWord_2419628
  simp only [CollatzResearch.WordTrace]
  refine ⟨44125541639054235203913769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58834055518738980271885025 44125541639054235203913769)
  ·
    refine ⟨33094156229290676402935327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44125541639054235203913769 33094156229290676402935327)
    ·
      refine ⟨49641234343936014604402991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33094156229290676402935327 49641234343936014604402991)
      ·
        refine ⟨74461851515904021906604487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49641234343936014604402991 74461851515904021906604487)
        ·
          refine ⟨111692777273856032859906731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74461851515904021906604487 111692777273856032859906731)
          ·
            refine ⟨167539165910784049289860097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111692777273856032859906731 167539165910784049289860097)
            ·
              refine ⟨125654374433088036967395073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167539165910784049289860097 125654374433088036967395073)
              ·
                refine ⟨94240780824816027725546305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125654374433088036967395073 94240780824816027725546305)
                ·
                  refine ⟨70680585618612020794159729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94240780824816027725546305 70680585618612020794159729)
                  ·
                    refine ⟨53010439213959015595619797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70680585618612020794159729 53010439213959015595619797)
                    ·
                      refine ⟨1242432169077164428022339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53010439213959015595619797 1242432169077164428022339)
                      ·
                        rfl

theorem cell23_2419628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_2419628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419628 prefixEnd_2419628 := by exact prefixLift 2419628
  have htrace : WordTrace (prefixWord ++ tailWord_2419628) baseStart_2419628 baseEnd_2419628 := by
    simpa [prefixWord, tailWord_2419628, baseEnd_2419628] using wordTrace_append hprefix tailTrace_2419628
  have hstable : (prefixWord ++ tailWord_2419628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419628).length < 2 ^ (prefixWord ++ tailWord_2419628).sum := by decide
  have hdescent : baseEnd_2419628 < baseStart_2419628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419663 : List Nat := [1, 1, 2, 1, 1, 7, 3, 2, 1, 2, 2]
def baseStart_2419663 : Nat := 118140960795 + 2419663 * 2 ^ 59
def prefixEnd_2419663 : Nat := 4983230072969 + 3 ^ 40 * 2419663 * 2
def baseEnd_2419663 : Nat := 1242450140900071791084679

theorem tailTrace_2419663 : CollatzResearch.WordTrace tailWord_2419663 prefixEnd_2419663 1242450140900071791084679 := by
  unfold tailWord_2419663
  simp only [CollatzResearch.WordTrace]
  refine ⟨88252359832981671385351643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58834906555321114256901095 88252359832981671385351643)
  ·
    refine ⟨132378539749472507078027465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88252359832981671385351643 132378539749472507078027465)
    ·
      refine ⟨99283904812104380308520599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132378539749472507078027465 99283904812104380308520599)
      ·
        refine ⟨148925857218156570462780899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99283904812104380308520599 148925857218156570462780899)
        ·
          refine ⟨223388785827234855694171349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148925857218156570462780899 223388785827234855694171349)
          ·
            refine ⟨5235674667825816930332141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 223388785827234855694171349 5235674667825816930332141)
            ·
              refine ⟨1963378000434681348874553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5235674667825816930332141 1963378000434681348874553)
              ·
                refine ⟨1472533500326011011655915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963378000434681348874553 1472533500326011011655915)
                ·
                  refine ⟨2208800250489016517483873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472533500326011011655915 2208800250489016517483873)
                  ·
                    refine ⟨1656600187866762388112905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2208800250489016517483873 1656600187866762388112905)
                    ·
                      refine ⟨1242450140900071791084679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1656600187866762388112905 1242450140900071791084679)
                      ·
                        rfl

theorem cell23_2419663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 2, 1, 2, 2].length) (baseStart_2419663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419663 prefixEnd_2419663 := by exact prefixLift 2419663
  have htrace : WordTrace (prefixWord ++ tailWord_2419663) baseStart_2419663 baseEnd_2419663 := by
    simpa [prefixWord, tailWord_2419663, baseEnd_2419663] using wordTrace_append hprefix tailTrace_2419663
  have hstable : (prefixWord ++ tailWord_2419663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419663).length < 2 ^ (prefixWord ++ tailWord_2419663).sum := by decide
  have hdescent : baseEnd_2419663 < baseStart_2419663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419700 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_2419700 : Nat := 118140960795 + 2419700 * 2 ^ 59
def prefixEnd_2419700 : Nat := 4983230072969 + 3 ^ 40 * 2419700 * 2
def baseEnd_2419700 : Nat := 1242469139684288146322009

theorem tailTrace_2419700 : CollatzResearch.WordTrace tailWord_2419700 prefixEnd_2419700 1242469139684288146322009 := by
  unfold tailWord_2419700
  simp only [CollatzResearch.WordTrace]
  refine ⟨44126854666923813352224277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58835806222565084469632369 44126854666923813352224277)
  ·
    refine ⟨2068446312512053750885513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44126854666923813352224277 2068446312512053750885513)
    ·
      refine ⟨1551334734384040313164135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2068446312512053750885513 1551334734384040313164135)
      ·
        refine ⟨2327002101576060469746203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1551334734384040313164135 2327002101576060469746203)
        ·
          refine ⟨3490503152364090704619305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2327002101576060469746203 3490503152364090704619305)
          ·
            refine ⟨2617877364273068028464479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490503152364090704619305 2617877364273068028464479)
            ·
              refine ⟨3926816046409602042696719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2617877364273068028464479 3926816046409602042696719)
              ·
                refine ⟨5890224069614403064045079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3926816046409602042696719 5890224069614403064045079)
                ·
                  refine ⟨8835336104421604596067619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5890224069614403064045079 8835336104421604596067619)
                  ·
                    refine ⟨13253004156632406894101429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8835336104421604596067619 13253004156632406894101429)
                    ·
                      refine ⟨1242469139684288146322009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13253004156632406894101429 1242469139684288146322009)
                      ·
                        rfl

theorem cell23_2419700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_2419700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419700 prefixEnd_2419700 := by exact prefixLift 2419700
  have htrace : WordTrace (prefixWord ++ tailWord_2419700) baseStart_2419700 baseEnd_2419700 := by
    simpa [prefixWord, tailWord_2419700, baseEnd_2419700] using wordTrace_append hprefix tailTrace_2419700
  have hstable : (prefixWord ++ tailWord_2419700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419700).length < 2 ^ (prefixWord ++ tailWord_2419700).sum := by decide
  have hdescent : baseEnd_2419700 < baseStart_2419700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419705 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2419705 : Nat := 118140960795 + 2419705 * 2 ^ 59
def prefixEnd_2419705 : Nat := 4983230072969 + 3 ^ 40 * 2419705 * 2
def baseEnd_2419705 : Nat := 1242471707087560626759485

theorem tailTrace_2419705 : CollatzResearch.WordTrace tailWord_2419705 prefixEnd_2419705 1242471707087560626759485 := by
  unfold tailWord_2419705
  simp only [CollatzResearch.WordTrace]
  refine ⟨88253891698829512558380569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58835927799219675038920379 88253891698829512558380569)
  ·
    refine ⟨66190418774122134418785427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88253891698829512558380569 66190418774122134418785427)
    ·
      refine ⟨99285628161183201628178141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66190418774122134418785427 99285628161183201628178141)
      ·
        refine ⟨37232110560443700610566803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99285628161183201628178141 37232110560443700610566803)
        ·
          refine ⟨55848165840665550915850205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37232110560443700610566803 55848165840665550915850205)
          ·
            refine ⟨20943062190249581593443827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55848165840665550915850205 20943062190249581593443827)
            ·
              refine ⟨31414593285374372390165741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20943062190249581593443827 31414593285374372390165741)
              ·
                refine ⟨11780472482015389646312153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31414593285374372390165741 11780472482015389646312153)
                ·
                  refine ⟨8835354361511542234734115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11780472482015389646312153 8835354361511542234734115)
                  ·
                    refine ⟨13253031542267313352101173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8835354361511542234734115 13253031542267313352101173)
                    ·
                      refine ⟨1242471707087560626759485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13253031542267313352101173 1242471707087560626759485)
                      ·
                        rfl

theorem cell23_2419705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2419705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419705 prefixEnd_2419705 := by exact prefixLift 2419705
  have htrace : WordTrace (prefixWord ++ tailWord_2419705) baseStart_2419705 baseEnd_2419705 := by
    simpa [prefixWord, tailWord_2419705, baseEnd_2419705] using wordTrace_append hprefix tailTrace_2419705
  have hstable : (prefixWord ++ tailWord_2419705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419705).length < 2 ^ (prefixWord ++ tailWord_2419705).sum := by decide
  have hdescent : baseEnd_2419705 < baseStart_2419705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419714 : List Nat := [3, 4, 1, 3, 1, 2, 2, 2, 1, 2, 2]
def baseStart_2419714 : Nat := 118140960795 + 2419714 * 2 ^ 59
def prefixEnd_2419714 : Nat := 4983230072969 + 3 ^ 40 * 2419714 * 2
def baseEnd_2419714 : Nat := 1242476328413451091546945

theorem tailTrace_2419714 : CollatzResearch.WordTrace tailWord_2419714 prefixEnd_2419714 1242476328413451091546945 := by
  unfold tailWord_2419714
  simp only [CollatzResearch.WordTrace]
  refine ⟨22063554988949226773864549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58836146637197938063638797 22063554988949226773864549)
  ·
    refine ⟨4136916560427980020099603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22063554988949226773864549 4136916560427980020099603)
    ·
      refine ⟨6205374840641970030149405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4136916560427980020099603 6205374840641970030149405)
      ·
        refine ⟨2327015565240738761306027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6205374840641970030149405 2327015565240738761306027)
        ·
          refine ⟨3490523347861108141959041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2327015565240738761306027 3490523347861108141959041)
          ·
            refine ⟨2617892510895831106469281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3490523347861108141959041 2617892510895831106469281)
            ·
              refine ⟨1963419383171873329851961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2617892510895831106469281 1963419383171873329851961)
              ·
                refine ⟨1472564537378904997388971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963419383171873329851961 1472564537378904997388971)
                ·
                  refine ⟨2208846806068357496083457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472564537378904997388971 2208846806068357496083457)
                  ·
                    refine ⟨1656635104551268122062593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2208846806068357496083457 1656635104551268122062593)
                    ·
                      refine ⟨1242476328413451091546945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1656635104551268122062593 1242476328413451091546945)
                      ·
                        rfl

theorem cell23_2419714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_2419714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419714 prefixEnd_2419714 := by exact prefixLift 2419714
  have htrace : WordTrace (prefixWord ++ tailWord_2419714) baseStart_2419714 baseEnd_2419714 := by
    simpa [prefixWord, tailWord_2419714, baseEnd_2419714] using wordTrace_append hprefix tailTrace_2419714
  have hstable : (prefixWord ++ tailWord_2419714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419714).length < 2 ^ (prefixWord ++ tailWord_2419714).sum := by decide
  have hdescent : baseEnd_2419714 < baseStart_2419714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419722 : List Nat := [3, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2419722 : Nat := 118140960795 + 2419722 * 2 ^ 59
def prefixEnd_2419722 : Nat := 4983230072969 + 3 ^ 40 * 2419722 * 2
def baseEnd_2419722 : Nat := 1242480436258687060246907

theorem tailTrace_2419722 : CollatzResearch.WordTrace tailWord_2419722 prefixEnd_2419722 1242480436258687060246907 := by
  unfold tailWord_2419722
  simp only [CollatzResearch.WordTrace]
  refine ⟨22063627934941981115437355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58836341159845282974499613 22063627934941981115437355)
  ·
    refine ⟨33095441902412971673156033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22063627934941981115437355 33095441902412971673156033)
    ·
      refine ⟨24821581426809728754867025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33095441902412971673156033 24821581426809728754867025)
      ·
        refine ⟨18616186070107296566150269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24821581426809728754867025 18616186070107296566150269)
        ·
          refine ⟨6981069776290236212306351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18616186070107296566150269 6981069776290236212306351)
          ·
            refine ⟨10471604664435354318459527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6981069776290236212306351 10471604664435354318459527)
            ·
              refine ⟨15707406996653031477689291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10471604664435354318459527 15707406996653031477689291)
              ·
                refine ⟨23561110494979547216533937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15707406996653031477689291 23561110494979547216533937)
                ·
                  refine ⟨17670832871234660412400453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23561110494979547216533937 17670832871234660412400453)
                  ·
                    refine ⟨3313281163356498827325085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17670832871234660412400453 3313281163356498827325085)
                    ·
                      refine ⟨1242480436258687060246907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3313281163356498827325085 1242480436258687060246907)
                      ·
                        rfl

theorem cell23_2419722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2419722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419722 prefixEnd_2419722 := by exact prefixLift 2419722
  have htrace : WordTrace (prefixWord ++ tailWord_2419722) baseStart_2419722 baseEnd_2419722 := by
    simpa [prefixWord, tailWord_2419722, baseEnd_2419722] using wordTrace_append hprefix tailTrace_2419722
  have hstable : (prefixWord ++ tailWord_2419722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419722).length < 2 ^ (prefixWord ++ tailWord_2419722).sum := by decide
  have hdescent : baseEnd_2419722 < baseStart_2419722 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419736 : List Nat := [2, 1, 2, 3, 2, 2, 2, 3, 2, 2, 2]
def baseStart_2419736 : Nat := 118140960795 + 2419736 * 2 ^ 59
def prefixEnd_2419736 : Nat := 4983230072969 + 3 ^ 40 * 2419736 * 2
def baseEnd_2419736 : Nat := 1242487624987850005471843

theorem tailTrace_2419736 : CollatzResearch.WordTrace tailWord_2419736 prefixEnd_2419736 1242487624987850005471843 := by
  unfold tailWord_2419736
  simp only [CollatzResearch.WordTrace]
  refine ⟨44127511180858602426379531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58836681574478136568506041 44127511180858602426379531)
  ·
    refine ⟨66191266771287903639569297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44127511180858602426379531 66191266771287903639569297)
    ·
      refine ⟨49643450078465927729676973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66191266771287903639569297 49643450078465927729676973)
      ·
        refine ⟨18616293779424722898628865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49643450078465927729676973 18616293779424722898628865)
        ·
          refine ⟨13962220334568542173971649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18616293779424722898628865 13962220334568542173971649)
          ·
            refine ⟨10471665250926406630478737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13962220334568542173971649 10471665250926406630478737)
            ·
              refine ⟨7853748938194804972859053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10471665250926406630478737 7853748938194804972859053)
              ·
                refine ⟨2945155851823051864822145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7853748938194804972859053 2945155851823051864822145)
                ·
                  refine ⟨2208866888867288898616609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2945155851823051864822145 2208866888867288898616609)
                  ·
                    refine ⟨1656650166650466673962457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2208866888867288898616609 1656650166650466673962457)
                    ·
                      refine ⟨1242487624987850005471843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1656650166650466673962457 1242487624987850005471843)
                      ·
                        rfl

theorem cell23_2419736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_2419736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419736 prefixEnd_2419736 := by exact prefixLift 2419736
  have htrace : WordTrace (prefixWord ++ tailWord_2419736) baseStart_2419736 baseEnd_2419736 := by
    simpa [prefixWord, tailWord_2419736, baseEnd_2419736] using wordTrace_append hprefix tailTrace_2419736
  have hstable : (prefixWord ++ tailWord_2419736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419736).length < 2 ^ (prefixWord ++ tailWord_2419736).sum := by decide
  have hdescent : baseEnd_2419736 < baseStart_2419736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419755 : List Nat := [1, 1, 1, 1, 2, 1, 7, 1, 1, 7]
def baseStart_2419755 : Nat := 118140960795 + 2419755 * 2 ^ 59
def prefixEnd_2419755 : Nat := 4983230072969 + 3 ^ 40 * 2419755 * 2
def baseEnd_2419755 : Nat := 414165793706761810378085

theorem tailTrace_2419755 : CollatzResearch.WordTrace tailWord_2419755 prefixEnd_2419755 414165793706761810378085 := by
  unfold tailWord_2419755
  simp only [CollatzResearch.WordTrace]
  refine ⟨88255715348648371097700719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58837143565765580731800479 88255715348648371097700719)
  ·
    refine ⟨132383573022972556646551079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88255715348648371097700719 132383573022972556646551079)
    ·
      refine ⟨198575359534458834969826619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132383573022972556646551079 198575359534458834969826619)
      ·
        refine ⟨297863039301688252454739929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198575359534458834969826619 297863039301688252454739929)
        ·
          refine ⟨223397279476266189341054947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297863039301688252454739929 223397279476266189341054947)
          ·
            refine ⟨335095919214399284011582421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223397279476266189341054947 335095919214399284011582421)
            ·
              refine ⟨7853810606587483219021463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 335095919214399284011582421 7853810606587483219021463)
              ·
                refine ⟨11780715909881224828532195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853810606587483219021463 11780715909881224828532195)
                ·
                  refine ⟨17671073864821837242798293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11780715909881224828532195 17671073864821837242798293)
                  ·
                    refine ⟨414165793706761810378085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17671073864821837242798293 414165793706761810378085)
                    ·
                      rfl

theorem cell23_2419755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 7].length) (baseStart_2419755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419755 prefixEnd_2419755 := by exact prefixLift 2419755
  have htrace : WordTrace (prefixWord ++ tailWord_2419755) baseStart_2419755 baseEnd_2419755 := by
    simpa [prefixWord, tailWord_2419755, baseEnd_2419755] using wordTrace_append hprefix tailTrace_2419755
  have hstable : (prefixWord ++ tailWord_2419755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419755).length < 2 ^ (prefixWord ++ tailWord_2419755).sum := by decide
  have hdescent : baseEnd_2419755 < baseStart_2419755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419802 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 5, 4]
def baseStart_2419802 : Nat := 118140960795 + 2419802 * 2 ^ 59
def prefixEnd_2419802 : Nat := 4983230072969 + 3 ^ 40 * 2419802 * 2
def baseEnd_2419802 : Nat := 414173838237015582415513

theorem tailTrace_2419802 : CollatzResearch.WordTrace tailWord_2419802 prefixEnd_2419802 414173838237015582415513 := by
  unfold tailWord_2419802
  simp only [CollatzResearch.WordTrace]
  refine ⟨22064357394869524531165415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58838286386318732083107773 22064357394869524531165415)
  ·
    refine ⟨33096536092304286796748123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22064357394869524531165415 33096536092304286796748123)
    ·
      refine ⟨49644804138456430195122185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33096536092304286796748123 49644804138456430195122185)
      ·
        refine ⟨37233603103842322646341639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49644804138456430195122185 37233603103842322646341639)
        ·
          refine ⟨55850404655763483969512459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37233603103842322646341639 55850404655763483969512459)
          ·
            refine ⟨83775606983645225954268689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55850404655763483969512459 83775606983645225954268689)
            ·
              refine ⟨62831705237733919465701517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83775606983645225954268689 62831705237733919465701517)
              ·
                refine ⟨23561889464150219799638069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62831705237733919465701517 23561889464150219799638069)
                ·
                  refine ⟨2208927137264083106216069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23561889464150219799638069 2208927137264083106216069)
                  ·
                    refine ⟨414173838237015582415513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2208927137264083106216069 414173838237015582415513)
                    ·
                      rfl

theorem cell23_2419802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_2419802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419802 prefixEnd_2419802 := by exact prefixLift 2419802
  have htrace : WordTrace (prefixWord ++ tailWord_2419802) baseStart_2419802 baseEnd_2419802 := by
    simpa [prefixWord, tailWord_2419802, baseEnd_2419802] using wordTrace_append hprefix tailTrace_2419802
  have hstable : (prefixWord ++ tailWord_2419802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419802).length < 2 ^ (prefixWord ++ tailWord_2419802).sum := by decide
  have hdescent : baseEnd_2419802 < baseStart_2419802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419806 : List Nat := [4, 4, 1, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2419806 : Nat := 118140960795 + 2419806 * 2 ^ 59
def prefixEnd_2419806 : Nat := 4983230072969 + 3 ^ 40 * 2419806 * 2
def baseEnd_2419806 : Nat := 414174522877888243865507

theorem tailTrace_2419806 : CollatzResearch.WordTrace tailWord_2419806 prefixEnd_2419806 414174522877888243865507 := by
  unfold tailWord_2419806
  simp only [CollatzResearch.WordTrace]
  refine ⟨11032196933932950850975909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58838383647642404538538181 11032196933932950850975909)
  ·
    refine ⟨2068536925112428284557983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11032196933932950850975909 2068536925112428284557983)
    ·
      refine ⟨3102805387668642426836975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2068536925112428284557983 3102805387668642426836975)
      ·
        refine ⟨4654208081502963640255463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102805387668642426836975 4654208081502963640255463)
        ·
          refine ⟨6981312122254445460383195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654208081502963640255463 6981312122254445460383195)
          ·
            refine ⟨10471968183381668190574793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6981312122254445460383195 10471968183381668190574793)
            ·
              refine ⟨7853976137536251142931095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10471968183381668190574793 7853976137536251142931095)
              ·
                refine ⟨11780964206304376714396643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7853976137536251142931095 11780964206304376714396643)
                ·
                  refine ⟨17671446309456565071594965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11780964206304376714396643 17671446309456565071594965)
                  ·
                    refine ⟨414174522877888243865507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17671446309456565071594965 414174522877888243865507)
                    ·
                      rfl

theorem cell23_2419806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2419806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419806 prefixEnd_2419806 := by exact prefixLift 2419806
  have htrace : WordTrace (prefixWord ++ tailWord_2419806) baseStart_2419806 baseEnd_2419806 := by
    simpa [prefixWord, tailWord_2419806, baseEnd_2419806] using wordTrace_append hprefix tailTrace_2419806
  have hstable : (prefixWord ++ tailWord_2419806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419806).length < 2 ^ (prefixWord ++ tailWord_2419806).sum := by decide
  have hdescent : baseEnd_2419806 < baseStart_2419806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419835 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8]
def baseStart_2419835 : Nat := 118140960795 + 2419835 * 2 ^ 59
def prefixEnd_2419835 : Nat := 4983230072969 + 3 ^ 40 * 2419835 * 2
def baseEnd_2419835 : Nat := 1242538459572645118133887

theorem tailTrace_2419835 : CollatzResearch.WordTrace tailWord_2419835 prefixEnd_2419835 1242538459572645118133887 := by
  unfold tailWord_2419835
  simp only [CollatzResearch.WordTrace]
  refine ⟨88258633188358544760612959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58839088792239029840408639 88258633188358544760612959)
  ·
    refine ⟨132387949782537817140919439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88258633188358544760612959 132387949782537817140919439)
    ·
      refine ⟨198581924673806725711379159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132387949782537817140919439 198581924673806725711379159)
      ·
        refine ⟨297872887010710088567068739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198581924673806725711379159 297872887010710088567068739)
        ·
          refine ⟨446809330516065132850603109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297872887010710088567068739 446809330516065132850603109)
          ·
            refine ⟨83776749471762212409488083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 446809330516065132850603109 83776749471762212409488083)
            ·
              refine ⟨125665124207643318614232125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83776749471762212409488083 125665124207643318614232125)
              ·
                refine ⟨47124421577866244480337047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125665124207643318614232125 47124421577866244480337047)
                ·
                  refine ⟨70686632366799366720505571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47124421577866244480337047 70686632366799366720505571)
                  ·
                    refine ⟨106029948550199050080758357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70686632366799366720505571 106029948550199050080758357)
                    ·
                      refine ⟨1242538459572645118133887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106029948550199050080758357 1242538459572645118133887)
                      ·
                        rfl

theorem cell23_2419835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 8].length) (baseStart_2419835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419835 prefixEnd_2419835 := by exact prefixLift 2419835
  have htrace : WordTrace (prefixWord ++ tailWord_2419835) baseStart_2419835 baseEnd_2419835 := by
    simpa [prefixWord, tailWord_2419835, baseEnd_2419835] using wordTrace_append hprefix tailTrace_2419835
  have hstable : (prefixWord ++ tailWord_2419835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419835).length < 2 ^ (prefixWord ++ tailWord_2419835).sum := by decide
  have hdescent : baseEnd_2419835 < baseStart_2419835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419849 : List Nat := [1, 2, 1, 1, 4, 3, 4, 1, 6]
def baseStart_2419849 : Nat := 118140960795 + 2419849 * 2 ^ 59
def prefixEnd_2419849 : Nat := 4983230072969 + 3 ^ 40 * 2419849 * 2
def baseEnd_2419849 : Nat := 138060627589089784817647

theorem tailTrace_2419849 : CollatzResearch.WordTrace tailWord_2419849 prefixEnd_2419849 138060627589089784817647 := by
  unfold tailWord_2419849
  simp only [CollatzResearch.WordTrace]
  refine ⟨88259143810307825151622601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58839429206871883434415067 88259143810307825151622601)
  ·
    refine ⟨66194357857730868863716951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88259143810307825151622601 66194357857730868863716951)
    ·
      refine ⟨99291536786596303295575427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66194357857730868863716951 99291536786596303295575427)
      ·
        refine ⟨148937305179894454943363141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99291536786596303295575427 148937305179894454943363141)
        ·
          refine ⟨27925744721230210301880589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148937305179894454943363141 27925744721230210301880589)
          ·
            refine ⟨10472154270461328863205221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27925744721230210301880589 10472154270461328863205221)
            ·
              refine ⟨1963528925711499161850979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10472154270461328863205221 1963528925711499161850979)
              ·
                refine ⟨2945293388567248742776469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963528925711499161850979 2945293388567248742776469)
                ·
                  refine ⟨138060627589089784817647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2945293388567248742776469 138060627589089784817647)
                  ·
                    rfl

theorem cell23_2419849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 6].length) (baseStart_2419849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419849 prefixEnd_2419849 := by exact prefixLift 2419849
  have htrace : WordTrace (prefixWord ++ tailWord_2419849) baseStart_2419849 baseEnd_2419849 := by
    simpa [prefixWord, tailWord_2419849, baseEnd_2419849] using wordTrace_append hprefix tailTrace_2419849
  have hstable : (prefixWord ++ tailWord_2419849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419849).length < 2 ^ (prefixWord ++ tailWord_2419849).sum := by decide
  have hdescent : baseEnd_2419849 < baseStart_2419849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419859 : List Nat := [1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 3]
def baseStart_2419859 : Nat := 118140960795 + 2419859 * 2 ^ 59
def prefixEnd_2419859 : Nat := 4983230072969 + 3 ^ 40 * 2419859 * 2
def baseEnd_2419859 : Nat := 1242550783108353024233777

theorem tailTrace_2419859 : CollatzResearch.WordTrace tailWord_2419859 prefixEnd_2419859 1242550783108353024233777 := by
  unfold tailWord_2419859
  simp only [CollatzResearch.WordTrace]
  refine ⟨88259508540271596859486631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58839672360181064572991087 88259508540271596859486631)
  ·
    refine ⟨132389262810407395289229947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88259508540271596859486631 132389262810407395289229947)
    ·
      refine ⟨198583894215611092933844921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132389262810407395289229947 198583894215611092933844921)
      ·
        refine ⟨148937920661708319700383691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198583894215611092933844921 148937920661708319700383691)
        ·
          refine ⟨223406880992562479550575537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148937920661708319700383691 223406880992562479550575537)
          ·
            refine ⟨167555160744421859662931653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223406880992562479550575537 167555160744421859662931653)
            ·
              refine ⟨31416592639579098686799685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167555160744421859662931653 31416592639579098686799685)
              ·
                refine ⟨5890611119921081003774941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31416592639579098686799685 5890611119921081003774941)
                ·
                  refine ⟨2208979169970405376415603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5890611119921081003774941 2208979169970405376415603)
                  ·
                    refine ⟨3313468754955608064623405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2208979169970405376415603 3313468754955608064623405)
                    ·
                      refine ⟨1242550783108353024233777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3313468754955608064623405 1242550783108353024233777)
                      ·
                        rfl

theorem cell23_2419859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_2419859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419859 prefixEnd_2419859 := by exact prefixLift 2419859
  have htrace : WordTrace (prefixWord ++ tailWord_2419859) baseStart_2419859 baseEnd_2419859 := by
    simpa [prefixWord, tailWord_2419859, baseEnd_2419859] using wordTrace_append hprefix tailTrace_2419859
  have hstable : (prefixWord ++ tailWord_2419859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419859).length < 2 ^ (prefixWord ++ tailWord_2419859).sum := by decide
  have hdescent : baseEnd_2419859 < baseStart_2419859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419912 : List Nat := [2, 1, 3, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_2419912 : Nat := 118140960795 + 2419912 * 2 ^ 59
def prefixEnd_2419912 : Nat := 4983230072969 + 3 ^ 40 * 2419912 * 2
def baseEnd_2419912 : Nat := 1242577997583041316871033

theorem tailTrace_2419912 : CollatzResearch.WordTrace tailWord_2419912 prefixEnd_2419912 1242577997583041316871033 := by
  unfold tailWord_2419912
  simp only [CollatzResearch.WordTrace]
  refine ⟨44130720804539793455582995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58840961072719724607443993 44130720804539793455582995)
  ·
    refine ⟨66196081206809690183374493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44130720804539793455582995 66196081206809690183374493)
    ·
      refine ⟨24823530452553633818765435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66196081206809690183374493 24823530452553633818765435)
      ·
        refine ⟨37235295678830450728148153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24823530452553633818765435 37235295678830450728148153)
        ·
          refine ⟨27926471759122838046111115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37235295678830450728148153 27926471759122838046111115)
          ·
            refine ⟨41889707638684257069166673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27926471759122838046111115 41889707638684257069166673)
            ·
              refine ⟨31417280729013192801875005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41889707638684257069166673 31417280729013192801875005)
              ·
                refine ⟨11781480273379947300703127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31417280729013192801875005 11781480273379947300703127)
                ·
                  refine ⟨17672220410069920951054691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11781480273379947300703127 17672220410069920951054691)
                  ·
                    refine ⟨26508330615104881426582037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17672220410069920951054691 26508330615104881426582037)
                    ·
                      refine ⟨1242577997583041316871033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26508330615104881426582037 1242577997583041316871033)
                      ·
                        rfl

theorem cell23_2419912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_2419912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419912 prefixEnd_2419912 := by exact prefixLift 2419912
  have htrace : WordTrace (prefixWord ++ tailWord_2419912) baseStart_2419912 baseEnd_2419912 := by
    simpa [prefixWord, tailWord_2419912, baseEnd_2419912] using wordTrace_append hprefix tailTrace_2419912
  have hstable : (prefixWord ++ tailWord_2419912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419912).length < 2 ^ (prefixWord ++ tailWord_2419912).sum := by decide
  have hdescent : baseEnd_2419912 < baseStart_2419912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419933 : List Nat := [1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_2419933 : Nat := 118140960795 + 2419933 * 2 ^ 59
def prefixEnd_2419933 : Nat := 4983230072969 + 3 ^ 40 * 2419933 * 2
def baseEnd_2419933 : Nat := 1242588780676785734708437

theorem tailTrace_2419933 : CollatzResearch.WordTrace tailWord_2419933 prefixEnd_2419933 1242588780676785734708437 := by
  unfold tailWord_2419933
  simp only [CollatzResearch.WordTrace]
  refine ⟨88262207542003507497680453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58841471694669004998453635 88262207542003507497680453)
  ·
    refine ⟨16549163914125657655815085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88262207542003507497680453 16549163914125657655815085)
    ·
      refine ⟨6205936467797121620930657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16549163914125657655815085 6205936467797121620930657)
      ·
        refine ⟨4654452350847841215697993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6205936467797121620930657 4654452350847841215697993)
        ·
          refine ⟨3490839263135880911773495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4654452350847841215697993 3490839263135880911773495)
          ·
            refine ⟨5236258894703821367660243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3490839263135880911773495 5236258894703821367660243)
            ·
              refine ⟨7854388342055732051490365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236258894703821367660243 7854388342055732051490365)
              ·
                refine ⟨2945395628270899519308887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7854388342055732051490365 2945395628270899519308887)
                ·
                  refine ⟨4418093442406349278963331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945395628270899519308887 4418093442406349278963331)
                  ·
                    refine ⟨6627140163609523918444997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4418093442406349278963331 6627140163609523918444997)
                    ·
                      refine ⟨1242588780676785734708437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6627140163609523918444997 1242588780676785734708437)
                      ·
                        rfl

theorem cell23_2419933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_2419933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419933 prefixEnd_2419933 := by exact prefixLift 2419933
  have htrace : WordTrace (prefixWord ++ tailWord_2419933) baseStart_2419933 baseEnd_2419933 := by
    simpa [prefixWord, tailWord_2419933, baseEnd_2419933] using wordTrace_append hprefix tailTrace_2419933
  have hstable : (prefixWord ++ tailWord_2419933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419933).length < 2 ^ (prefixWord ++ tailWord_2419933).sum := by decide
  have hdescent : baseEnd_2419933 < baseStart_2419933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419936 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3]
def baseStart_2419936 : Nat := 118140960795 + 2419936 * 2 ^ 59
def prefixEnd_2419936 : Nat := 4983230072969 + 3 ^ 40 * 2419936 * 2
def baseEnd_2419936 : Nat := 1242590321118749222970923

theorem tailTrace_2419936 : CollatzResearch.WordTrace tailWord_2419936 prefixEnd_2419936 1242590321118749222970923 := by
  unfold tailWord_2419936
  simp only [CollatzResearch.WordTrace]
  refine ⟨44131158480496319505019831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58841544640661759340026441 44131158480496319505019831)
  ·
    refine ⟨66196737720744479257529747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44131158480496319505019831 66196737720744479257529747)
    ·
      refine ⟨99295106581116718886294621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66196737720744479257529747 99295106581116718886294621)
      ·
        refine ⟨37235664967918769582360483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99295106581116718886294621 37235664967918769582360483)
        ·
          refine ⟨55853497451878154373540725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37235664967918769582360483 55853497451878154373540725)
          ·
            refine ⟨5236265386113576972519443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55853497451878154373540725 5236265386113576972519443)
            ·
              refine ⟨7854398079170365458779165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236265386113576972519443 7854398079170365458779165)
              ·
                refine ⟨2945399279688887047042187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7854398079170365458779165 2945399279688887047042187)
                ·
                  refine ⟨4418098919533330570563281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945399279688887047042187 4418098919533330570563281)
                  ·
                    refine ⟨3313574189649997927922461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4418098919533330570563281 3313574189649997927922461)
                    ·
                      refine ⟨1242590321118749222970923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3313574189649997927922461 1242590321118749222970923)
                      ·
                        rfl

theorem cell23_2419936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_2419936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419936 prefixEnd_2419936 := by exact prefixLift 2419936
  have htrace : WordTrace (prefixWord ++ tailWord_2419936) baseStart_2419936 baseEnd_2419936 := by
    simpa [prefixWord, tailWord_2419936, baseEnd_2419936] using wordTrace_append hprefix tailTrace_2419936
  have hstable : (prefixWord ++ tailWord_2419936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419936).length < 2 ^ (prefixWord ++ tailWord_2419936).sum := by decide
  have hdescent : baseEnd_2419936 < baseStart_2419936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419950 : List Nat := [4, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2]
def baseStart_2419950 : Nat := 118140960795 + 2419950 * 2 ^ 59
def prefixEnd_2419950 : Nat := 4983230072969 + 3 ^ 40 * 2419950 * 2
def baseEnd_2419950 : Nat := 1242597509847912168195859

theorem tailTrace_2419950 : CollatzResearch.WordTrace tailWord_2419950 prefixEnd_2419950 1242597509847912168195859 := by
  unfold tailWord_2419950
  simp only [CollatzResearch.WordTrace]
  refine ⟨11032853447867739925131163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58841885055294612934032869 11032853447867739925131163)
  ·
    refine ⟨16549280171801609887696745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11032853447867739925131163 16549280171801609887696745)
    ·
      refine ⟨12411960128851207415772559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16549280171801609887696745 12411960128851207415772559)
      ·
        refine ⟨18617940193276811123658839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12411960128851207415772559 18617940193276811123658839)
        ·
          refine ⟨27926910289915216685488259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18617940193276811123658839 27926910289915216685488259)
          ·
            refine ⟨41890365434872825028232389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27926910289915216685488259 41890365434872825028232389)
            ·
              refine ⟨7854443519038654692793573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41890365434872825028232389 7854443519038654692793573)
              ·
                refine ⟨1472708159819747754898795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7854443519038654692793573 1472708159819747754898795)
                ·
                  refine ⟨2209062239729621632348193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1472708159819747754898795 2209062239729621632348193)
                  ·
                    refine ⟨1656796679797216224261145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2209062239729621632348193 1656796679797216224261145)
                    ·
                      refine ⟨1242597509847912168195859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1656796679797216224261145 1242597509847912168195859)
                      ·
                        rfl

theorem cell23_2419950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_2419950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419950 prefixEnd_2419950 := by exact prefixLift 2419950
  have htrace : WordTrace (prefixWord ++ tailWord_2419950) baseStart_2419950 baseEnd_2419950 := by
    simpa [prefixWord, tailWord_2419950, baseEnd_2419950] using wordTrace_append hprefix tailTrace_2419950
  have hstable : (prefixWord ++ tailWord_2419950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419950).length < 2 ^ (prefixWord ++ tailWord_2419950).sum := by decide
  have hdescent : baseEnd_2419950 < baseStart_2419950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2419970 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 1, 2, 3]
def baseStart_2419970 : Nat := 118140960795 + 2419970 * 2 ^ 59
def prefixEnd_2419970 : Nat := 4983230072969 + 3 ^ 40 * 2419970 * 2
def baseEnd_2419970 : Nat := 1242607779461002089945767

theorem tailTrace_2419970 : CollatzResearch.WordTrace tailWord_2419970 prefixEnd_2419970 1242607779461002089945767 := by
  unfold tailWord_2419970
  simp only [CollatzResearch.WordTrace]
  refine ⟨22065889260717365704194341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58842371361912975211184909 22065889260717365704194341)
  ·
    refine ⟨4137354236384506069536439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22065889260717365704194341 4137354236384506069536439)
    ·
      refine ⟨6206031354576759104304659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4137354236384506069536439 6206031354576759104304659)
      ·
        refine ⟨9309047031865138656456989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206031354576759104304659 9309047031865138656456989)
        ·
          refine ⟨3490892636949426996171371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9309047031865138656456989 3490892636949426996171371)
          ·
            refine ⟨5236338955424140494257057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3490892636949426996171371 5236338955424140494257057)
            ·
              refine ⟨3927254216568105370692793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5236338955424140494257057 3927254216568105370692793)
              ·
                refine ⟨2945440662426079028019595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927254216568105370692793 2945440662426079028019595)
                ·
                  refine ⟨4418160993639118542029393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2945440662426079028019595 4418160993639118542029393)
                  ·
                    refine ⟨3313620745229338906522045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4418160993639118542029393 3313620745229338906522045)
                    ·
                      refine ⟨1242607779461002089945767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3313620745229338906522045 1242607779461002089945767)
                      ·
                        rfl

theorem cell23_2419970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_2419970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2419970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2419970 prefixEnd_2419970 := by exact prefixLift 2419970
  have htrace : WordTrace (prefixWord ++ tailWord_2419970) baseStart_2419970 baseEnd_2419970 := by
    simpa [prefixWord, tailWord_2419970, baseEnd_2419970] using wordTrace_append hprefix tailTrace_2419970
  have hstable : (prefixWord ++ tailWord_2419970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2419970).length < 2 ^ (prefixWord ++ tailWord_2419970).sum := by decide
  have hdescent : baseEnd_2419970 < baseStart_2419970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2419970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420046 : List Nat := [4, 1, 1, 1, 1, 1, 4, 5, 5]
def baseStart_2420046 : Nat := 118140960795 + 2420046 * 2 ^ 59
def prefixEnd_2420046 : Nat := 4983230072969 + 3 ^ 40 * 2420046 * 2
def baseEnd_2420046 : Nat := 138071867110082643621713

theorem tailTrace_2420046 : CollatzResearch.WordTrace tailWord_2420046 prefixEnd_2420046 138071867110082643621713 := by
  unfold tailWord_2420046
  simp only [CollatzResearch.WordTrace]
  refine ⟨11033291123824265974567999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58844219327062751864362661 11033291123824265974567999)
  ·
    refine ⟨16549936685736398961851999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11033291123824265974567999 16549936685736398961851999)
    ·
      refine ⟨24824905028604598442777999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16549936685736398961851999 24824905028604598442777999)
      ·
        refine ⟨37237357542906897664166999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24824905028604598442777999 37237357542906897664166999)
        ·
          refine ⟨55856036314360346496250499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37237357542906897664166999 55856036314360346496250499)
          ·
            refine ⟨83784054471540519744375749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55856036314360346496250499 83784054471540519744375749)
            ·
              refine ⟨15709510213413847452070453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83784054471540519744375749 15709510213413847452070453)
              ·
                refine ⟨1472766582507548198631605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15709510213413847452070453 1472766582507548198631605)
                ·
                  refine ⟨138071867110082643621713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1472766582507548198631605 138071867110082643621713)
                  ·
                    rfl

theorem cell23_2420046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 5, 5].length) (baseStart_2420046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420046 prefixEnd_2420046 := by exact prefixLift 2420046
  have htrace : WordTrace (prefixWord ++ tailWord_2420046) baseStart_2420046 baseEnd_2420046 := by
    simpa [prefixWord, tailWord_2420046, baseEnd_2420046] using wordTrace_append hprefix tailTrace_2420046
  have hstable : (prefixWord ++ tailWord_2420046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420046).length < 2 ^ (prefixWord ++ tailWord_2420046).sum := by decide
  have hdescent : baseEnd_2420046 < baseStart_2420046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420069 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 5]
def baseStart_2420069 : Nat := 118140960795 + 2420069 * 2 ^ 59
def prefixEnd_2420069 : Nat := 4983230072969 + 3 ^ 40 * 2420069 * 2
def baseEnd_2420069 : Nat := 1242658614045797202607811

theorem tailTrace_2420069 : CollatzResearch.WordTrace tailWord_2420069 prefixEnd_2420069 1242658614045797202607811 := by
  unfold tailWord_2420069
  simp only [CollatzResearch.WordTrace]
  refine ⟨88267167869510802724631261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58844778579673868483087507 88267167869510802724631261)
  ·
    refine ⟨33100187951066551021736723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88267167869510802724631261 33100187951066551021736723)
    ·
      refine ⟨49650281926599826532605085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33100187951066551021736723 49650281926599826532605085)
      ·
        refine ⟨18618855722474934949726907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49650281926599826532605085 18618855722474934949726907)
        ·
          refine ⟨27928283583712402424590361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18618855722474934949726907 27928283583712402424590361)
          ·
            refine ⟨20946212687784301818442771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27928283583712402424590361 20946212687784301818442771)
            ·
              refine ⟨31419319031676452727664157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20946212687784301818442771 31419319031676452727664157)
              ·
                refine ⟨11782244636878669772874059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31419319031676452727664157 11782244636878669772874059)
                ·
                  refine ⟨17673366955318004659311089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11782244636878669772874059 17673366955318004659311089)
                  ·
                    refine ⟨13255025216488503494483317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17673366955318004659311089 13255025216488503494483317)
                    ·
                      refine ⟨1242658614045797202607811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13255025216488503494483317 1242658614045797202607811)
                      ·
                        rfl

theorem cell23_2420069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_2420069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420069 prefixEnd_2420069 := by exact prefixLift 2420069
  have htrace : WordTrace (prefixWord ++ tailWord_2420069) baseStart_2420069 baseEnd_2420069 := by
    simpa [prefixWord, tailWord_2420069, baseEnd_2420069] using wordTrace_append hprefix tailTrace_2420069
  have hstable : (prefixWord ++ tailWord_2420069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420069).length < 2 ^ (prefixWord ++ tailWord_2420069).sum := by decide
  have hdescent : baseEnd_2420069 < baseStart_2420069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420079 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 4]
def baseStart_2420079 : Nat := 118140960795 + 2420079 * 2 ^ 59
def prefixEnd_2420079 : Nat := 4983230072969 + 3 ^ 40 * 2420079 * 2
def baseEnd_2420079 : Nat := 1242663748852342163482765

theorem tailTrace_2420079 : CollatzResearch.WordTrace tailWord_2420079 prefixEnd_2420079 1242663748852342163482765 := by
  unfold tailWord_2420079
  simp only [CollatzResearch.WordTrace]
  refine ⟨88267532599474574432495291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58845021732983049621663527 88267532599474574432495291)
  ·
    refine ⟨132401298899211861648742937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88267532599474574432495291 132401298899211861648742937)
    ·
      refine ⟨99300974174408896236557203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132401298899211861648742937 99300974174408896236557203)
      ·
        refine ⟨148951461261613344354835805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99300974174408896236557203 148951461261613344354835805)
        ·
          refine ⟨55856797973105004133063427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148951461261613344354835805 55856797973105004133063427)
          ·
            refine ⟨83785196959657506199595141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55856797973105004133063427 83785196959657506199595141)
            ·
              refine ⟨15709724429935782412424089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83785196959657506199595141 15709724429935782412424089)
              ·
                refine ⟨11782293322451836809318067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15709724429935782412424089 11782293322451836809318067)
                ·
                  refine ⟨17673439983677755213977101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11782293322451836809318067 17673439983677755213977101)
                  ·
                    refine ⟨6627539993879158205241413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17673439983677755213977101 6627539993879158205241413)
                    ·
                      refine ⟨1242663748852342163482765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6627539993879158205241413 1242663748852342163482765)
                      ·
                        rfl

theorem cell23_2420079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 4].length) (baseStart_2420079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420079 prefixEnd_2420079 := by exact prefixLift 2420079
  have htrace : WordTrace (prefixWord ++ tailWord_2420079) baseStart_2420079 baseEnd_2420079 := by
    simpa [prefixWord, tailWord_2420079, baseEnd_2420079] using wordTrace_append hprefix tailTrace_2420079
  have hstable : (prefixWord ++ tailWord_2420079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420079).length < 2 ^ (prefixWord ++ tailWord_2420079).sum := by decide
  have hdescent : baseEnd_2420079 < baseStart_2420079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420213 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2420213 : Nat := 118140960795 + 2420213 * 2 ^ 59
def prefixEnd_2420213 : Nat := 4983230072969 + 3 ^ 40 * 2420213 * 2
def baseEnd_2420213 : Nat := 414244185086681546402383

theorem tailTrace_2420213 : CollatzResearch.WordTrace tailWord_2420213 prefixEnd_2420213 414244185086681546402383 := by
  unfold tailWord_2420213
  simp only [CollatzResearch.WordTrace]
  refine ⟨88272419980989115317873293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58848279987326076878582195 88272419980989115317873293)
  ·
    refine ⟨33102157492870918244202485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88272419980989115317873293 33102157492870918244202485)
    ·
      refine ⟨3103327264956648585393983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33102157492870918244202485 3103327264956648585393983)
      ·
        refine ⟨4654990897434972878090975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3103327264956648585393983 4654990897434972878090975)
        ·
          refine ⟨6982486346152459317136463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654990897434972878090975 6982486346152459317136463)
          ·
            refine ⟨10473729519228688975704695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6982486346152459317136463 10473729519228688975704695)
            ·
              refine ⟨15710594278843033463557043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10473729519228688975704695 15710594278843033463557043)
              ·
                refine ⟨23565891418264550195335565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15710594278843033463557043 23565891418264550195335565)
                ·
                  refine ⟨8837209281849206323250837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23565891418264550195335565 8837209281849206323250837)
                  ·
                    refine ⟨414244185086681546402383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8837209281849206323250837 414244185086681546402383)
                    ·
                      rfl

theorem cell23_2420213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2420213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420213 prefixEnd_2420213 := by exact prefixLift 2420213
  have htrace : WordTrace (prefixWord ++ tailWord_2420213) baseStart_2420213 baseEnd_2420213 := by
    simpa [prefixWord, tailWord_2420213, baseEnd_2420213] using wordTrace_append hprefix tailTrace_2420213
  have hstable : (prefixWord ++ tailWord_2420213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420213).length < 2 ^ (prefixWord ++ tailWord_2420213).sum := by decide
  have hdescent : baseEnd_2420213 < baseStart_2420213 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420216 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2420216 : Nat := 118140960795 + 2420216 * 2 ^ 59
def prefixEnd_2420216 : Nat := 4983230072969 + 3 ^ 40 * 2420216 * 2
def baseEnd_2420216 : Nat := 1242734095702008127469635

theorem tailTrace_2420216 : CollatzResearch.WordTrace tailWord_2420216 prefixEnd_2420216 1242734095702008127469635 := by
  unfold tailWord_2420216
  simp only [CollatzResearch.WordTrace]
  refine ⟨44136264699989123415116251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58848352933318831220155001 44136264699989123415116251)
  ·
    refine ⟨66204397049983685122674377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44136264699989123415116251 66204397049983685122674377)
    ·
      refine ⟨49653297787487763842005783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66204397049983685122674377 49653297787487763842005783)
      ·
        refine ⟨74479946681231645763008675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49653297787487763842005783 74479946681231645763008675)
        ·
          refine ⟨111719920021847468644513013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74479946681231645763008675 111719920021847468644513013)
          ·
            refine ⟨10473742502048200185423095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111719920021847468644513013 10473742502048200185423095)
            ·
              refine ⟨15710613753072300278134643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10473742502048200185423095 15710613753072300278134643)
              ·
                refine ⟨23565920629608450417201965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15710613753072300278134643 23565920629608450417201965)
                ·
                  refine ⟨8837220236103168906450737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23565920629608450417201965 8837220236103168906450737)
                  ·
                    refine ⟨6627915177077376679838053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8837220236103168906450737 6627915177077376679838053)
                    ·
                      refine ⟨1242734095702008127469635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6627915177077376679838053 1242734095702008127469635)
                      ·
                        rfl

theorem cell23_2420216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2420216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420216 prefixEnd_2420216 := by exact prefixLift 2420216
  have htrace : WordTrace (prefixWord ++ tailWord_2420216) baseStart_2420216 baseEnd_2420216 := by
    simpa [prefixWord, tailWord_2420216, baseEnd_2420216] using wordTrace_append hprefix tailTrace_2420216
  have hstable : (prefixWord ++ tailWord_2420216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420216).length < 2 ^ (prefixWord ++ tailWord_2420216).sum := by decide
  have hdescent : baseEnd_2420216 < baseStart_2420216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420270 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2420270 : Nat := 118140960795 + 2420270 * 2 ^ 59
def prefixEnd_2420270 : Nat := 4983230072969 + 3 ^ 40 * 2420270 * 2
def baseEnd_2420270 : Nat := 1242761823657350916194387

theorem tailTrace_2420270 : CollatzResearch.WordTrace tailWord_2420270 prefixEnd_2420270 1242761823657350916194387 := by
  unfold tailWord_2420270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11034312367722826756587283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58849665961188409368465509 11034312367722826756587283)
  ·
    refine ⟨16551468551584240134880925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11034312367722826756587283 16551468551584240134880925)
    ·
      refine ⟨6206800706844090050580347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16551468551584240134880925 6206800706844090050580347)
      ·
        refine ⟨9310201060266135075870521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6206800706844090050580347 9310201060266135075870521)
        ·
          refine ⟨6982650795199601306902891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9310201060266135075870521 6982650795199601306902891)
          ·
            refine ⟨10473976192799401960354337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6982650795199601306902891 10473976192799401960354337)
            ·
              refine ⟨7855482144599551470265753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10473976192799401960354337 7855482144599551470265753)
              ·
                refine ⟨5891611608449663602699315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7855482144599551470265753 5891611608449663602699315)
                ·
                  refine ⟨8837417412674495404048973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5891611608449663602699315 8837417412674495404048973)
                  ·
                    refine ⟨3314031529752935776518365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8837417412674495404048973 3314031529752935776518365)
                    ·
                      refine ⟨1242761823657350916194387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3314031529752935776518365 1242761823657350916194387)
                      ·
                        rfl

theorem cell23_2420270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2420270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420270 prefixEnd_2420270 := by exact prefixLift 2420270
  have htrace : WordTrace (prefixWord ++ tailWord_2420270) baseStart_2420270 baseEnd_2420270 := by
    simpa [prefixWord, tailWord_2420270, baseEnd_2420270] using wordTrace_append hprefix tailTrace_2420270
  have hstable : (prefixWord ++ tailWord_2420270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420270).length < 2 ^ (prefixWord ++ tailWord_2420270).sum := by decide
  have hdescent : baseEnd_2420270 < baseStart_2420270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420287 : List Nat := [1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 3]
def baseStart_2420287 : Nat := 118140960795 + 2420287 * 2 ^ 59
def prefixEnd_2420287 : Nat := 4983230072969 + 3 ^ 40 * 2420287 * 2
def baseEnd_2420287 : Nat := 1242770552828477349681809

theorem tailTrace_2420287 : CollatzResearch.WordTrace tailWord_2420287 prefixEnd_2420287 1242770552828477349681809 := by
  unfold tailWord_2420287
  simp only [CollatzResearch.WordTrace]
  refine ⟨88275118982721025956067115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58850079321814017304044743 88275118982721025956067115)
  ·
    refine ⟨132412678474081538934100673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88275118982721025956067115 132412678474081538934100673)
    ·
      refine ⟨99309508855561154200575505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132412678474081538934100673 99309508855561154200575505)
      ·
        refine ⟨74482131641670865650431629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99309508855561154200575505 74482131641670865650431629)
        ·
          refine ⟨27930799365626574618911861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74482131641670865650431629 27930799365626574618911861)
          ·
            refine ⟨2618512440527491370522987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27930799365626574618911861 2618512440527491370522987)
            ·
              refine ⟨3927768660791237055784481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618512440527491370522987 3927768660791237055784481)
              ·
                refine ⟨2945826495593427791838361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3927768660791237055784481 2945826495593427791838361)
                ·
                  refine ⟨2209369871695070843878771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2945826495593427791838361 2209369871695070843878771)
                  ·
                    refine ⟨3314054807542606265818157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2209369871695070843878771 3314054807542606265818157)
                    ·
                      refine ⟨1242770552828477349681809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3314054807542606265818157 1242770552828477349681809)
                      ·
                        rfl

theorem cell23_2420287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 2, 2, 1, 3].length) (baseStart_2420287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420287 prefixEnd_2420287 := by exact prefixLift 2420287
  have htrace : WordTrace (prefixWord ++ tailWord_2420287) baseStart_2420287 baseEnd_2420287 := by
    simpa [prefixWord, tailWord_2420287, baseEnd_2420287] using wordTrace_append hprefix tailTrace_2420287
  have hstable : (prefixWord ++ tailWord_2420287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420287).length < 2 ^ (prefixWord ++ tailWord_2420287).sum := by decide
  have hdescent : baseEnd_2420287 < baseStart_2420287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420296 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_2420296 : Nat := 118140960795 + 2420296 * 2 ^ 59
def prefixEnd_2420296 : Nat := 4983230072969 + 3 ^ 40 * 2420296 * 2
def baseEnd_2420296 : Nat := 1242775174154367814469267

theorem tailTrace_2420296 : CollatzResearch.WordTrace tailWord_2420296 prefixEnd_2420296 1242775174154367814469267 := by
  unfold tailWord_2420296
  simp only [CollatzResearch.WordTrace]
  refine ⟨44137723619844210246572371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58850298159792280328763161 44137723619844210246572371)
  ·
    refine ⟨66206585429766315369858557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44137723619844210246572371 66206585429766315369858557)
    ·
      refine ⟨24827469536162368263696959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66206585429766315369858557 24827469536162368263696959)
      ·
        refine ⟨37241204304243552395545439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24827469536162368263696959 37241204304243552395545439)
        ·
          refine ⟨55861806456365328593318159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37241204304243552395545439 55861806456365328593318159)
          ·
            refine ⟨83792709684547992889977239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55861806456365328593318159 83792709684547992889977239)
            ·
              refine ⟨125689064526821989334965859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83792709684547992889977239 125689064526821989334965859)
              ·
                refine ⟨188533596790232984002448789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125689064526821989334965859 188533596790232984002448789)
                ·
                  refine ⟨8837512349542171125114787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 188533596790232984002448789 8837512349542171125114787)
                  ·
                    refine ⟨13256268524313256687672181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8837512349542171125114787 13256268524313256687672181)
                    ·
                      refine ⟨1242775174154367814469267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13256268524313256687672181 1242775174154367814469267)
                      ·
                        rfl

theorem cell23_2420296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_2420296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420296 prefixEnd_2420296 := by exact prefixLift 2420296
  have htrace : WordTrace (prefixWord ++ tailWord_2420296) baseStart_2420296 baseEnd_2420296 := by
    simpa [prefixWord, tailWord_2420296, baseEnd_2420296] using wordTrace_append hprefix tailTrace_2420296
  have hstable : (prefixWord ++ tailWord_2420296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420296).length < 2 ^ (prefixWord ++ tailWord_2420296).sum := by decide
  have hdescent : baseEnd_2420296 < baseStart_2420296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420346 : List Nat := [3, 1, 1, 1, 1, 1, 1, 4, 3, 7]
def baseStart_2420346 : Nat := 118140960795 + 2420346 * 2 ^ 59
def prefixEnd_2420346 : Nat := 4983230072969 + 3 ^ 40 * 2420346 * 2
def baseEnd_2420346 : Nat := 414266949395697539614679

theorem tailTrace_2420346 : CollatzResearch.WordTrace tailWord_2420346 prefixEnd_2420346 414266949395697539614679 := by
  unfold tailWord_2420346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22069317722376819758116223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58851513926338186021643261 22069317722376819758116223)
  ·
    refine ⟨33103976583565229637174335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22069317722376819758116223 33103976583565229637174335)
    ·
      refine ⟨49655964875347844455761503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33103976583565229637174335 49655964875347844455761503)
      ·
        refine ⟨74483947313021766683642255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49655964875347844455761503 74483947313021766683642255)
        ·
          refine ⟨111725920969532650025463383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74483947313021766683642255 111725920969532650025463383)
          ·
            refine ⟨167588881454298975038195075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111725920969532650025463383 167588881454298975038195075)
            ·
              refine ⟨251383322181448462557292613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167588881454298975038195075 251383322181448462557292613)
              ·
                refine ⟨47134372909021586729492365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 251383322181448462557292613 47134372909021586729492365)
                ·
                  refine ⟨17675389840883095023559637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47134372909021586729492365 17675389840883095023559637)
                  ·
                    refine ⟨414266949395697539614679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17675389840883095023559637 414266949395697539614679)
                    ·
                      rfl

theorem cell23_2420346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 3, 7].length) (baseStart_2420346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420346 prefixEnd_2420346 := by exact prefixLift 2420346
  have htrace : WordTrace (prefixWord ++ tailWord_2420346) baseStart_2420346 baseEnd_2420346 := by
    simpa [prefixWord, tailWord_2420346, baseEnd_2420346] using wordTrace_append hprefix tailTrace_2420346
  have hstable : (prefixWord ++ tailWord_2420346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420346).length < 2 ^ (prefixWord ++ tailWord_2420346).sum := by decide
  have hdescent : baseEnd_2420346 < baseStart_2420346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420420 : List Nat := [2, 3, 3, 1, 1, 1, 2, 2, 1, 4, 3]
def baseStart_2420420 : Nat := 118140960795 + 2420420 * 2 ^ 59
def prefixEnd_2420420 : Nat := 4983230072969 + 3 ^ 40 * 2420420 * 2
def baseEnd_2420420 : Nat := 1242838845755525329318697

theorem tailTrace_2420420 : CollatzResearch.WordTrace tailWord_2420420 prefixEnd_2420420 1242838845755525329318697 := by
  unfold tailWord_2420420
  simp only [CollatzResearch.WordTrace]
  refine ⟨44139984945619594835329357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58853313260826126447105809 44139984945619594835329357)
  ·
    refine ⟨16552494354607348063248509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44139984945619594835329357 16552494354607348063248509)
    ·
      refine ⟨6207185382977755523718191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16552494354607348063248509 6207185382977755523718191)
      ·
        refine ⟨9310778074466633285577287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6207185382977755523718191 9310778074466633285577287)
        ·
          refine ⟨13966167111699949928365931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9310778074466633285577287 13966167111699949928365931)
          ·
            refine ⟨20949250667549924892548897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13966167111699949928365931 20949250667549924892548897)
            ·
              refine ⟨15711938000662443669411673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20949250667549924892548897 15711938000662443669411673)
              ·
                refine ⟨11783953500496832752058755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15711938000662443669411673 11783953500496832752058755)
                ·
                  refine ⟨17675930250745249128088133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11783953500496832752058755 17675930250745249128088133)
                  ·
                    refine ⟨3314236922014734211516525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17675930250745249128088133 3314236922014734211516525)
                    ·
                      refine ⟨1242838845755525329318697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3314236922014734211516525 1242838845755525329318697)
                      ·
                        rfl

theorem cell23_2420420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_2420420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420420 prefixEnd_2420420 := by exact prefixLift 2420420
  have htrace : WordTrace (prefixWord ++ tailWord_2420420) baseStart_2420420 baseEnd_2420420 := by
    simpa [prefixWord, tailWord_2420420, baseEnd_2420420] using wordTrace_append hprefix tailTrace_2420420
  have hstable : (prefixWord ++ tailWord_2420420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420420).length < 2 ^ (prefixWord ++ tailWord_2420420).sum := by decide
  have hdescent : baseEnd_2420420 < baseStart_2420420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420423 : List Nat := [1, 1, 4, 1, 1, 1, 3, 5, 6]
def baseStart_2420423 : Nat := 118140960795 + 2420423 * 2 ^ 59
def prefixEnd_2420423 : Nat := 4983230072969 + 3 ^ 40 * 2420423 * 2
def baseEnd_2420423 : Nat := 138093376244165424175687

theorem tailTrace_2420423 : CollatzResearch.WordTrace tailWord_2420423 prefixEnd_2420423 138093376244165424175687 := by
  unfold tailWord_2420423
  simp only [CollatzResearch.WordTrace]
  refine ⟨88280079310228321183017923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58853386206818880788678615 88280079310228321183017923)
  ·
    refine ⟨132420118965342481774526885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88280079310228321183017923 132420118965342481774526885)
    ·
      refine ⟨24828772306001715332723791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132420118965342481774526885 24828772306001715332723791)
      ·
        refine ⟨37243158459002572999085687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24828772306001715332723791 37243158459002572999085687)
        ·
          refine ⟨55864737688503859498628531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37243158459002572999085687 55864737688503859498628531)
          ·
            refine ⟨83797106532755789247942797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55864737688503859498628531 83797106532755789247942797)
            ·
              refine ⟨31423914949783420967978549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83797106532755789247942797 31423914949783420967978549)
              ·
                refine ⟨2945992026542195715747989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31423914949783420967978549 2945992026542195715747989)
                ·
                  refine ⟨138093376244165424175687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2945992026542195715747989 138093376244165424175687)
                  ·
                    rfl

theorem cell23_2420423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5, 6].length) (baseStart_2420423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420423 prefixEnd_2420423 := by exact prefixLift 2420423
  have htrace : WordTrace (prefixWord ++ tailWord_2420423) baseStart_2420423 baseEnd_2420423 := by
    simpa [prefixWord, tailWord_2420423, baseEnd_2420423] using wordTrace_append hprefix tailTrace_2420423
  have hstable : (prefixWord ++ tailWord_2420423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420423).length < 2 ^ (prefixWord ++ tailWord_2420423).sum := by decide
  have hdescent : baseEnd_2420423 < baseStart_2420423 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420501 : List Nat := [1, 3, 2, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_2420501 : Nat := 118140960795 + 2420501 * 2 ^ 59
def prefixEnd_2420501 : Nat := 4983230072969 + 3 ^ 40 * 2420501 * 2
def baseEnd_2420501 : Nat := 1242880437688539512405825

theorem tailTrace_2420501 : CollatzResearch.WordTrace tailWord_2420501 prefixEnd_2420501 1242880437688539512405825 := by
  unfold tailWord_2420501
  simp only [CollatzResearch.WordTrace]
  refine ⟨88282924203945740504357357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58855282802630493669571571 88282924203945740504357357)
  ·
    refine ⟨33106096576479652689134009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88282924203945740504357357 33106096576479652689134009)
    ·
      refine ⟨24829572432359739516850507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33106096576479652689134009 24829572432359739516850507)
      ·
        refine ⟨37244358648539609275275761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24829572432359739516850507 37244358648539609275275761)
        ·
          refine ⟨27933268986404706956456821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37244358648539609275275761 27933268986404706956456821)
          ·
            refine ⟨2618743967475441277167827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27933268986404706956456821 2618743967475441277167827)
            ·
              refine ⟨3928115951213161915751741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2618743967475441277167827 3928115951213161915751741)
              ·
                refine ⟨1473043481704935718406903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3928115951213161915751741 1473043481704935718406903)
                ·
                  refine ⟨2209565222557403577610355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473043481704935718406903 2209565222557403577610355)
                  ·
                    refine ⟨3314347833836105366415533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2209565222557403577610355 3314347833836105366415533)
                    ·
                      refine ⟨1242880437688539512405825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3314347833836105366415533 1242880437688539512405825)
                      ·
                        rfl

theorem cell23_2420501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_2420501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420501 prefixEnd_2420501 := by exact prefixLift 2420501
  have htrace : WordTrace (prefixWord ++ tailWord_2420501) baseStart_2420501 baseEnd_2420501 := by
    simpa [prefixWord, tailWord_2420501, baseEnd_2420501] using wordTrace_append hprefix tailTrace_2420501
  have hstable : (prefixWord ++ tailWord_2420501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420501).length < 2 ^ (prefixWord ++ tailWord_2420501).sum := by decide
  have hdescent : baseEnd_2420501 < baseStart_2420501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420513 : List Nat := [1, 2, 3, 2, 1, 3, 11]
def baseStart_2420513 : Nat := 118140960795 + 2420513 * 2 ^ 59
def prefixEnd_2420513 : Nat := 4983230072969 + 3 ^ 40 * 2420513 * 2
def baseEnd_2420513 : Nat := 15344279005634487227849

theorem tailTrace_2420513 : CollatzResearch.WordTrace tailWord_2420513 prefixEnd_2420513 15344279005634487227849 := by
  unfold tailWord_2420513
  simp only [CollatzResearch.WordTrace]
  refine ⟨88283361879902266553794193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58855574586601511035862795 88283361879902266553794193)
  ·
    refine ⟨66212521409926699915345645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88283361879902266553794193 66212521409926699915345645)
    ·
      refine ⟨24829695528722512468254617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66212521409926699915345645 24829695528722512468254617)
      ·
        refine ⟨18622271646541884351190963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24829695528722512468254617 18622271646541884351190963)
        ·
          refine ⟨27933407469812826526786445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18622271646541884351190963 27933407469812826526786445)
          ·
            refine ⟨10475027801179809947544917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27933407469812826526786445 10475027801179809947544917)
            ·
              refine ⟨15344279005634487227849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 10475027801179809947544917 15344279005634487227849)
              ·
                rfl

theorem cell23_2420513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 11].length) (baseStart_2420513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420513 prefixEnd_2420513 := by exact prefixLift 2420513
  have htrace : WordTrace (prefixWord ++ tailWord_2420513) baseStart_2420513 baseEnd_2420513 := by
    simpa [prefixWord, tailWord_2420513, baseEnd_2420513] using wordTrace_append hprefix tailTrace_2420513
  have hstable : (prefixWord ++ tailWord_2420513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420513).length < 2 ^ (prefixWord ++ tailWord_2420513).sum := by decide
  have hdescent : baseEnd_2420513 < baseStart_2420513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420520 : List Nat := [2, 1, 5, 1, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2420520 : Nat := 118140960795 + 2420520 * 2 ^ 59
def prefixEnd_2420520 : Nat := 4983230072969 + 3 ^ 40 * 2420520 * 2
def baseEnd_2420520 : Nat := 1242890193820974938068237

theorem tailTrace_2420520 : CollatzResearch.WordTrace tailWord_2420520 prefixEnd_2420520 1242890193820974938068237 := by
  unfold tailWord_2420520
  simp only [CollatzResearch.WordTrace]
  refine ⟨44141808595438453374649507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58855744793917937832866009 44141808595438453374649507)
  ·
    refine ⟨66212712893157680061974261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44141808595438453374649507 66212712893157680061974261)
    ·
      refine ⟨6207441833733532505810087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66212712893157680061974261 6207441833733532505810087)
      ·
        refine ⟨9311162750600298758715131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6207441833733532505810087 9311162750600298758715131)
        ·
          refine ⟨13966744125900448138072697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9311162750600298758715131 13966744125900448138072697)
          ·
            refine ⟨10475058094425336103554523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13966744125900448138072697 10475058094425336103554523)
            ·
              refine ⟨15712587141638004155331785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10475058094425336103554523 15712587141638004155331785)
              ·
                refine ⟨11784440356228503116498839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15712587141638004155331785 11784440356228503116498839)
                ·
                  refine ⟨17676660534342754674748259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11784440356228503116498839 17676660534342754674748259)
                  ·
                    refine ⟨26514990801514132012122389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17676660534342754674748259 26514990801514132012122389)
                    ·
                      refine ⟨1242890193820974938068237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26514990801514132012122389 1242890193820974938068237)
                      ·
                        rfl

theorem cell23_2420520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2420520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420520 prefixEnd_2420520 := by exact prefixLift 2420520
  have htrace : WordTrace (prefixWord ++ tailWord_2420520) baseStart_2420520 baseEnd_2420520 := by
    simpa [prefixWord, tailWord_2420520, baseEnd_2420520] using wordTrace_append hprefix tailTrace_2420520
  have hstable : (prefixWord ++ tailWord_2420520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420520).length < 2 ^ (prefixWord ++ tailWord_2420520).sum := by decide
  have hdescent : baseEnd_2420520 < baseStart_2420520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420524 : List Nat := [2, 2, 1, 1, 1, 5, 3, 1, 3, 2, 2]
def baseStart_2420524 : Nat := 118140960795 + 2420524 * 2 ^ 59
def prefixEnd_2420524 : Nat := 4983230072969 + 3 ^ 40 * 2420524 * 2
def baseEnd_2420524 : Nat := 1242892247743592922418219

theorem tailTrace_2420524 : CollatzResearch.WordTrace tailWord_2420524 prefixEnd_2420524 1242892247743592922418219 := by
  unfold tailWord_2420524
  simp only [CollatzResearch.WordTrace]
  refine ⟨44141881541431207716222313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58855842055241610288296417 44141881541431207716222313)
  ·
    refine ⟨33106411156073405787166735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44141881541431207716222313 33106411156073405787166735)
    ·
      refine ⟨49659616734110108680750103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33106411156073405787166735 49659616734110108680750103)
      ·
        refine ⟨74489425101165163021125155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49659616734110108680750103 74489425101165163021125155)
        ·
          refine ⟨111734137651747744531687733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74489425101165163021125155 111734137651747744531687733)
          ·
            refine ⟨10475075404851351049845725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111734137651747744531687733 10475075404851351049845725)
            ·
              refine ⟨3928153276819256643692147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10475075404851351049845725 3928153276819256643692147)
              ·
                refine ⟨5892229915228884965538221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928153276819256643692147 5892229915228884965538221)
                ·
                  refine ⟨2209586218210831862076833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5892229915228884965538221 2209586218210831862076833)
                  ·
                    refine ⟨1657189663658123896557625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2209586218210831862076833 1657189663658123896557625)
                    ·
                      refine ⟨1242892247743592922418219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657189663658123896557625 1242892247743592922418219)
                      ·
                        rfl

theorem cell23_2420524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_2420524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420524 prefixEnd_2420524 := by exact prefixLift 2420524
  have htrace : WordTrace (prefixWord ++ tailWord_2420524) baseStart_2420524 baseEnd_2420524 := by
    simpa [prefixWord, tailWord_2420524, baseEnd_2420524] using wordTrace_append hprefix tailTrace_2420524
  have hstable : (prefixWord ++ tailWord_2420524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420524).length < 2 ^ (prefixWord ++ tailWord_2420524).sum := by decide
  have hdescent : baseEnd_2420524 < baseStart_2420524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420530 : List Nat := [3, 2, 1, 1, 3, 3, 2, 8]
def baseStart_2420530 : Nat := 118140960795 + 2420530 * 2 ^ 59
def prefixEnd_2420530 : Nat := 4983230072969 + 3 ^ 40 * 2420530 * 2
def baseEnd_2420530 : Nat := 46033160319537774034933

theorem tailTrace_2420530 : CollatzResearch.WordTrace tailWord_2420530 prefixEnd_2420530 46033160319537774034933 := by
  unfold tailWord_2420530
  simp only [CollatzResearch.WordTrace]
  refine ⟨22070995480210169614290761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58855987947227118971442029 22070995480210169614290761)
  ·
    refine ⟨16553246610157627210718071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22070995480210169614290761 16553246610157627210718071)
    ·
      refine ⟨24829869915236440816077107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16553246610157627210718071 24829869915236440816077107)
      ·
        refine ⟨37244804872854661224115661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24829869915236440816077107 37244804872854661224115661)
        ·
          refine ⟨13966801827320497959043373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37244804872854661224115661 13966801827320497959043373)
          ·
            refine ⟨5237550685245186734641265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13966801827320497959043373 5237550685245186734641265)
            ·
              refine ⟨3928163013933890050980949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237550685245186734641265 3928163013933890050980949)
              ·
                refine ⟨46033160319537774034933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3928163013933890050980949 46033160319537774034933)
                ·
                  rfl

theorem cell23_2420530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 8].length) (baseStart_2420530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420530 prefixEnd_2420530 := by exact prefixLift 2420530
  have htrace : WordTrace (prefixWord ++ tailWord_2420530) baseStart_2420530 baseEnd_2420530 := by
    simpa [prefixWord, tailWord_2420530, baseEnd_2420530] using wordTrace_append hprefix tailTrace_2420530
  have hstable : (prefixWord ++ tailWord_2420530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420530).length < 2 ^ (prefixWord ++ tailWord_2420530).sum := by decide
  have hdescent : baseEnd_2420530 < baseStart_2420530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420631 : List Nat := [1, 1, 3, 3, 1, 3, 3, 2, 2, 2, 2]
def baseStart_2420631 : Nat := 118140960795 + 2420631 * 2 ^ 59
def prefixEnd_2420631 : Nat := 4983230072969 + 3 ^ 40 * 2420631 * 2
def baseEnd_2420631 : Nat := 1242947190173624003780227

theorem tailTrace_2420631 : CollatzResearch.WordTrace tailWord_2420631 prefixEnd_2420631 1242947190173624003780227 := by
  unfold tailWord_2420631
  simp only [CollatzResearch.WordTrace]
  refine ⟨88287665693474772706589747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58858443795649848471059831 88287665693474772706589747)
  ·
    refine ⟨132431498540212159059884621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88287665693474772706589747 132431498540212159059884621)
    ·
      refine ⟨49661811952579559647456733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132431498540212159059884621 49661811952579559647456733)
      ·
        refine ⟨18623179482217334867796275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49661811952579559647456733 18623179482217334867796275)
        ·
          refine ⟨27934769223326002301694413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18623179482217334867796275 27934769223326002301694413)
          ·
            refine ⟨10475538458747250863135405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27934769223326002301694413 10475538458747250863135405)
            ·
              refine ⟨3928326922030219073675777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10475538458747250863135405 3928326922030219073675777)
              ·
                refine ⟨2946245191522664305256833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3928326922030219073675777 2946245191522664305256833)
                ·
                  refine ⟨2209683893641998228942625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2946245191522664305256833 2209683893641998228942625)
                  ·
                    refine ⟨1657262920231498671706969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2209683893641998228942625 1657262920231498671706969)
                    ·
                      refine ⟨1242947190173624003780227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657262920231498671706969 1242947190173624003780227)
                      ·
                        rfl

theorem cell23_2420631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 2, 2, 2, 2].length) (baseStart_2420631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420631 prefixEnd_2420631 := by exact prefixLift 2420631
  have htrace : WordTrace (prefixWord ++ tailWord_2420631) baseStart_2420631 baseEnd_2420631 := by
    simpa [prefixWord, tailWord_2420631, baseEnd_2420631] using wordTrace_append hprefix tailTrace_2420631
  have hstable : (prefixWord ++ tailWord_2420631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420631).length < 2 ^ (prefixWord ++ tailWord_2420631).sum := by decide
  have hdescent : baseEnd_2420631 < baseStart_2420631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420637 : List Nat := [1, 4, 2, 1, 2, 3, 2, 1, 7]
def baseStart_2420637 : Nat := 118140960795 + 2420637 * 2 ^ 59
def prefixEnd_2420637 : Nat := 4983230072969 + 3 ^ 40 * 2420637 * 2
def baseEnd_2420637 : Nat := 138105585673061220033911

theorem tailTrace_2420637 : CollatzResearch.WordTrace tailWord_2420637 prefixEnd_2420637 138105585673061220033911 := by
  unfold tailWord_2420637
  simp only [CollatzResearch.WordTrace]
  refine ⟨88287884531453035731308165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58858589687635357154205443 88287884531453035731308165)
  ·
    refine ⟨16553978349647444199620281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88287884531453035731308165 16553978349647444199620281)
    ·
      refine ⟨12415483762235583149715211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16553978349647444199620281 12415483762235583149715211)
      ·
        refine ⟨18623225643353374724572817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12415483762235583149715211 18623225643353374724572817)
        ·
          refine ⟨13967419232515031043429613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18623225643353374724572817 13967419232515031043429613)
          ·
            refine ⟨5237782212193136641286105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13967419232515031043429613 5237782212193136641286105)
            ·
              refine ⟨3928336659144852480964579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5237782212193136641286105 3928336659144852480964579)
              ·
                refine ⟨5892504988717278721446869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928336659144852480964579 5892504988717278721446869)
                ·
                  refine ⟨138105585673061220033911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5892504988717278721446869 138105585673061220033911)
                  ·
                    rfl

theorem cell23_2420637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_2420637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420637 prefixEnd_2420637 := by exact prefixLift 2420637
  have htrace : WordTrace (prefixWord ++ tailWord_2420637) baseStart_2420637 baseEnd_2420637 := by
    simpa [prefixWord, tailWord_2420637, baseEnd_2420637] using wordTrace_append hprefix tailTrace_2420637
  have hstable : (prefixWord ++ tailWord_2420637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420637).length < 2 ^ (prefixWord ++ tailWord_2420637).sum := by decide
  have hdescent : baseEnd_2420637 < baseStart_2420637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420687 : List Nat := [1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 4]
def baseStart_2420687 : Nat := 118140960795 + 2420687 * 2 ^ 59
def prefixEnd_2420687 : Nat := 4983230072969 + 3 ^ 40 * 2420687 * 2
def baseEnd_2420687 : Nat := 1242975945090275784679969

theorem tailTrace_2420687 : CollatzResearch.WordTrace tailWord_2420687 prefixEnd_2420687 1242975945090275784679969 := by
  unfold tailWord_2420687
  simp only [CollatzResearch.WordTrace]
  refine ⟨88289708181271894270628315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58859805454181262847085543 88289708181271894270628315)
  ·
    refine ⟨132434562271907841405942473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88289708181271894270628315 132434562271907841405942473)
    ·
      refine ⟨99325921703930881054456855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132434562271907841405942473 99325921703930881054456855)
      ·
        refine ⟨148988882555896321581685283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99325921703930881054456855 148988882555896321581685283)
        ·
          refine ⟨223483323833844482372527925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148988882555896321581685283 223483323833844482372527925)
          ·
            refine ⟨20951561609422920222424493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223483323833844482372527925 20951561609422920222424493)
            ·
              refine ⟨7856835603533595083409185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20951561609422920222424493 7856835603533595083409185)
              ·
                refine ⟨5892626702650196312556889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7856835603533595083409185 5892626702650196312556889)
                ·
                  refine ⟨4419470026987647234417667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892626702650196312556889 4419470026987647234417667)
                  ·
                    refine ⟨6629205040481470851626501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4419470026987647234417667 6629205040481470851626501)
                    ·
                      refine ⟨1242975945090275784679969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6629205040481470851626501 1242975945090275784679969)
                      ·
                        rfl

theorem cell23_2420687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 4].length) (baseStart_2420687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420687 prefixEnd_2420687 := by exact prefixLift 2420687
  have htrace : WordTrace (prefixWord ++ tailWord_2420687) baseStart_2420687 baseEnd_2420687 := by
    simpa [prefixWord, tailWord_2420687, baseEnd_2420687] using wordTrace_append hprefix tailTrace_2420687
  have hstable : (prefixWord ++ tailWord_2420687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420687).length < 2 ^ (prefixWord ++ tailWord_2420687).sum := by decide
  have hdescent : baseEnd_2420687 < baseStart_2420687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420730 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8]
def baseStart_2420730 : Nat := 118140960795 + 2420730 * 2 ^ 59
def prefixEnd_2420730 : Nat := 4983230072969 + 3 ^ 40 * 2420730 * 2
def baseEnd_2420730 : Nat := 1242998024758419116442271

theorem tailTrace_2420730 : CollatzResearch.WordTrace tailWord_2420730 prefixEnd_2420730 1242998024758419116442271 := by
  unfold tailWord_2420730
  simp only [CollatzResearch.WordTrace]
  refine ⟨22072819130029028153610911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58860851013410741742962429 22072819130029028153610911)
  ·
    refine ⟨33109228695043542230416367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22072819130029028153610911 33109228695043542230416367)
    ·
      refine ⟨49663843042565313345624551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33109228695043542230416367 49663843042565313345624551)
      ·
        refine ⟨74495764563847970018436827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49663843042565313345624551 74495764563847970018436827)
        ·
          refine ⟨111743646845771955027655241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74495764563847970018436827 111743646845771955027655241)
          ·
            refine ⟨83807735134328966270741431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111743646845771955027655241 83807735134328966270741431)
            ·
              refine ⟨125711602701493449406112147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83807735134328966270741431 125711602701493449406112147)
              ·
                refine ⟨188567404052240174109168221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125711602701493449406112147 188567404052240174109168221)
                ·
                  refine ⟨70712776519590065290938083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 188567404052240174109168221 70712776519590065290938083)
                  ·
                    refine ⟨106069164779385097936407125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70712776519590065290938083 106069164779385097936407125)
                    ·
                      refine ⟨1242998024758419116442271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106069164779385097936407125 1242998024758419116442271)
                      ·
                        rfl

theorem cell23_2420730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_2420730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420730 prefixEnd_2420730 := by exact prefixLift 2420730
  have htrace : WordTrace (prefixWord ++ tailWord_2420730) baseStart_2420730 baseEnd_2420730 := by
    simpa [prefixWord, tailWord_2420730, baseEnd_2420730] using wordTrace_append hprefix tailTrace_2420730
  have hstable : (prefixWord ++ tailWord_2420730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420730).length < 2 ^ (prefixWord ++ tailWord_2420730).sum := by decide
  have hdescent : baseEnd_2420730 < baseStart_2420730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420775 : List Nat := [1, 1, 7, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2420775 : Nat := 118140960795 + 2420775 * 2 ^ 59
def prefixEnd_2420775 : Nat := 4983230072969 + 3 ^ 40 * 2420775 * 2
def baseEnd_2420775 : Nat := 1243021131387871440379565

theorem tailTrace_2420775 : CollatzResearch.WordTrace tailWord_2420775 prefixEnd_2420775 1243021131387871440379565 := by
  unfold tailWord_2420775
  simp only [CollatzResearch.WordTrace]
  refine ⟨88292917804953085299831779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58861945203302056866554519 88292917804953085299831779)
  ·
    refine ⟨132439376707429627949747669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88292917804953085299831779 132439376707429627949747669)
    ·
      refine ⟨3104047891580381905072211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 132439376707429627949747669 3104047891580381905072211)
      ·
        refine ⟨4656071837370572857608317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104047891580381905072211 4656071837370572857608317)
        ·
          refine ⟨1746026939013964821603119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4656071837370572857608317 1746026939013964821603119)
          ·
            refine ⟨2619040408520947232404679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746026939013964821603119 2619040408520947232404679)
            ·
              refine ⟨3928560612781420848607019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619040408520947232404679 3928560612781420848607019)
              ·
                refine ⟨5892840919172131272910529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928560612781420848607019 5892840919172131272910529)
                ·
                  refine ⟨4419630689379098454682897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5892840919172131272910529 4419630689379098454682897)
                  ·
                    refine ⟨3314723017034323841012173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4419630689379098454682897 3314723017034323841012173)
                    ·
                      refine ⟨1243021131387871440379565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3314723017034323841012173 1243021131387871440379565)
                      ·
                        rfl

theorem cell23_2420775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2420775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420775 prefixEnd_2420775 := by exact prefixLift 2420775
  have htrace : WordTrace (prefixWord ++ tailWord_2420775) baseStart_2420775 baseEnd_2420775 := by
    simpa [prefixWord, tailWord_2420775, baseEnd_2420775] using wordTrace_append hprefix tailTrace_2420775
  have hstable : (prefixWord ++ tailWord_2420775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420775).length < 2 ^ (prefixWord ++ tailWord_2420775).sum := by decide
  have hdescent : baseEnd_2420775 < baseStart_2420775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420787 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 1, 6]
def baseStart_2420787 : Nat := 118140960795 + 2420787 * 2 ^ 59
def prefixEnd_2420787 : Nat := 4983230072969 + 3 ^ 40 * 2420787 * 2
def baseEnd_2420787 : Nat := 414342431051908464476503

theorem tailTrace_2420787 : CollatzResearch.WordTrace tailWord_2420787 prefixEnd_2420787 414342431051908464476503 := by
  unfold tailWord_2420787
  simp only [CollatzResearch.WordTrace]
  refine ⟨88293355480909611349268615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58862236987273074232845743 88293355480909611349268615)
  ·
    refine ⟨132440033221364417023902923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88293355480909611349268615 132440033221364417023902923)
    ·
      refine ⟨198660049832046625535854385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132440033221364417023902923 198660049832046625535854385)
      ·
        refine ⟨148995037374034969151890789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198660049832046625535854385 148995037374034969151890789)
        ·
          refine ⟨27936569507631556715979523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 148995037374034969151890789 27936569507631556715979523)
          ·
            refine ⟨41904854261447335073969285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27936569507631556715979523 41904854261447335073969285)
            ·
              refine ⟨7857160174021375326369241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41904854261447335073969285 7857160174021375326369241)
              ·
                refine ⟨5892870130516031494776931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857160174021375326369241 5892870130516031494776931)
                ·
                  refine ⟨8839305195774047242165397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892870130516031494776931 8839305195774047242165397)
                  ·
                    refine ⟨414342431051908464476503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8839305195774047242165397 414342431051908464476503)
                    ·
                      rfl

theorem cell23_2420787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 1, 6].length) (baseStart_2420787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420787 prefixEnd_2420787 := by exact prefixLift 2420787
  have htrace : WordTrace (prefixWord ++ tailWord_2420787) baseStart_2420787 baseEnd_2420787 := by
    simpa [prefixWord, tailWord_2420787, baseEnd_2420787] using wordTrace_append hprefix tailTrace_2420787
  have hstable : (prefixWord ++ tailWord_2420787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420787).length < 2 ^ (prefixWord ++ tailWord_2420787).sum := by decide
  have hdescent : baseEnd_2420787 < baseStart_2420787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420807 : List Nat := [1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_2420807 : Nat := 118140960795 + 2420807 * 2 ^ 59
def prefixEnd_2420807 : Nat := 4983230072969 + 3 ^ 40 * 2420807 * 2
def baseEnd_2420807 : Nat := 1243037562768815315179417

theorem tailTrace_2420807 : CollatzResearch.WordTrace tailWord_2420807 prefixEnd_2420807 1243037562768815315179417 := by
  unfold tailWord_2420807
  simp only [CollatzResearch.WordTrace]
  refine ⟨88294084940837154764996675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58862723293891436509997783 88294084940837154764996675)
  ·
    refine ⟨132441127411255732147495013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88294084940837154764996675 132441127411255732147495013)
    ·
      refine ⟨24832711389610449777655315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132441127411255732147495013 24832711389610449777655315)
      ·
        refine ⟨37249067084415674666482973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24832711389610449777655315 37249067084415674666482973)
        ·
          refine ⟨13968400156655877999931115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37249067084415674666482973 13968400156655877999931115)
          ·
            refine ⟨20952600234983816999896673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13968400156655877999931115 20952600234983816999896673)
            ·
              refine ⟨15714450176237862749922505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20952600234983816999896673 15714450176237862749922505)
              ·
                refine ⟨11785837632178397062441879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15714450176237862749922505 11785837632178397062441879)
                ·
                  refine ⟨17678756448267595593662819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11785837632178397062441879 17678756448267595593662819)
                  ·
                    refine ⟨26518134672401393390494229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17678756448267595593662819 26518134672401393390494229)
                    ·
                      refine ⟨1243037562768815315179417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26518134672401393390494229 1243037562768815315179417)
                      ·
                        rfl

theorem cell23_2420807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_2420807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420807 prefixEnd_2420807 := by exact prefixLift 2420807
  have htrace : WordTrace (prefixWord ++ tailWord_2420807) baseStart_2420807 baseEnd_2420807 := by
    simpa [prefixWord, tailWord_2420807, baseEnd_2420807] using wordTrace_append hprefix tailTrace_2420807
  have hstable : (prefixWord ++ tailWord_2420807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420807).length < 2 ^ (prefixWord ++ tailWord_2420807).sum := by decide
  have hdescent : baseEnd_2420807 < baseStart_2420807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420814 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_2420814 : Nat := 118140960795 + 2420814 * 2 ^ 59
def prefixEnd_2420814 : Nat := 4983230072969 + 3 ^ 40 * 2420814 * 2
def baseEnd_2420814 : Nat := 1243041157133396787791885

theorem tailTrace_2420814 : CollatzResearch.WordTrace tailWord_2420814 prefixEnd_2420814 1243041157133396787791885 := by
  unfold tailWord_2420814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11036792531476474370062687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58862893501207863307000997 11036792531476474370062687)
  ·
    refine ⟨16555188797214711555094031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11036792531476474370062687 16555188797214711555094031)
    ·
      refine ⟨24832783195822067332641047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555188797214711555094031 24832783195822067332641047)
      ·
        refine ⟨37249174793733100998961571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24832783195822067332641047 37249174793733100998961571)
        ·
          refine ⟨55873762190599651498442357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37249174793733100998961571 55873762190599651498442357)
          ·
            refine ⟨5238165205368717327978971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55873762190599651498442357 5238165205368717327978971)
            ·
              refine ⟨7857247808053075991968457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238165205368717327978971 7857247808053075991968457)
              ·
                refine ⟨5892935856039806993976343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857247808053075991968457 5892935856039806993976343)
                ·
                  refine ⟨8839403784059710490964515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892935856039806993976343 8839403784059710490964515)
                  ·
                    refine ⟨13259105676089565736446773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8839403784059710490964515 13259105676089565736446773)
                    ·
                      refine ⟨1243041157133396787791885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13259105676089565736446773 1243041157133396787791885)
                      ·
                        rfl

theorem cell23_2420814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_2420814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420814 prefixEnd_2420814 := by exact prefixLift 2420814
  have htrace : WordTrace (prefixWord ++ tailWord_2420814) baseStart_2420814 baseEnd_2420814 := by
    simpa [prefixWord, tailWord_2420814, baseEnd_2420814] using wordTrace_append hprefix tailTrace_2420814
  have hstable : (prefixWord ++ tailWord_2420814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420814).length < 2 ^ (prefixWord ++ tailWord_2420814).sum := by decide
  have hdescent : baseEnd_2420814 < baseStart_2420814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420824 : List Nat := [2, 1, 2, 2, 1, 4, 3, 1, 1, 2, 4]
def baseStart_2420824 : Nat := 118140960795 + 2420824 * 2 ^ 59
def prefixEnd_2420824 : Nat := 4983230072969 + 3 ^ 40 * 2420824 * 2
def baseEnd_2420824 : Nat := 1243046291939941748666839

theorem tailTrace_2420824 : CollatzResearch.WordTrace tailWord_2420824 prefixEnd_2420824 1243046291939941748666839 := by
  unfold tailWord_2420824
  simp only [CollatzResearch.WordTrace]
  refine ⟨44147352490887783334182763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58863136654517044445577017 44147352490887783334182763)
  ·
    refine ⟨66221028736331675001274145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44147352490887783334182763 66221028736331675001274145)
    ·
      refine ⟨49665771552248756250955609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66221028736331675001274145 49665771552248756250955609)
      ·
        refine ⟨37249328664186567188216707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49665771552248756250955609 37249328664186567188216707)
        ·
          refine ⟨55873992996279850782325061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37249328664186567188216707 55873992996279850782325061)
          ·
            refine ⟨10476373686802472021685949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55873992996279850782325061 10476373686802472021685949)
            ·
              refine ⟨3928640132550927008132231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10476373686802472021685949 3928640132550927008132231)
              ·
                refine ⟨5892960198826390512198347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3928640132550927008132231 5892960198826390512198347)
                ·
                  refine ⟨8839440298239585768297521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5892960198826390512198347 8839440298239585768297521)
                  ·
                    refine ⟨6629580223679689326223141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8839440298239585768297521 6629580223679689326223141)
                    ·
                      refine ⟨1243046291939941748666839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6629580223679689326223141 1243046291939941748666839)
                      ·
                        rfl

theorem cell23_2420824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_2420824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420824 prefixEnd_2420824 := by exact prefixLift 2420824
  have htrace : WordTrace (prefixWord ++ tailWord_2420824) baseStart_2420824 baseEnd_2420824 := by
    simpa [prefixWord, tailWord_2420824, baseEnd_2420824] using wordTrace_append hprefix tailTrace_2420824
  have hstable : (prefixWord ++ tailWord_2420824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420824).length < 2 ^ (prefixWord ++ tailWord_2420824).sum := by decide
  have hdescent : baseEnd_2420824 < baseStart_2420824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420828 : List Nat := [2, 2, 4, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_2420828 : Nat := 118140960795 + 2420828 * 2 ^ 59
def prefixEnd_2420828 : Nat := 4983230072969 + 3 ^ 40 * 2420828 * 2
def baseEnd_2420828 : Nat := 1243048345862559733016821

theorem tailTrace_2420828 : CollatzResearch.WordTrace tailWord_2420828 prefixEnd_2420828 1243048345862559733016821 := by
  unfold tailWord_2420828
  simp only [CollatzResearch.WordTrace]
  refine ⟨44147425436880537675755569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58863233915840716901007425 44147425436880537675755569)
  ·
    refine ⟨33110569077660403256816677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44147425436880537675755569 33110569077660403256816677)
    ·
      refine ⟨6208231702061325610653127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33110569077660403256816677 6208231702061325610653127)
      ·
        refine ⟨9312347553091988415979691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208231702061325610653127 9312347553091988415979691)
        ·
          refine ⟨13968521329637982623969537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312347553091988415979691 13968521329637982623969537)
          ·
            refine ⟨10476390997228486967977153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13968521329637982623969537 10476390997228486967977153)
            ·
              refine ⟨7857293247921365225982865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10476390997228486967977153 7857293247921365225982865)
              ·
                refine ⟨5892969935941023919487149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857293247921365225982865 5892969935941023919487149)
                ·
                  refine ⟨2209863725977883969807681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5892969935941023919487149 2209863725977883969807681)
                  ·
                    refine ⟨1657397794483412977355761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2209863725977883969807681 1657397794483412977355761)
                    ·
                      refine ⟨1243048345862559733016821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657397794483412977355761 1243048345862559733016821)
                      ·
                        rfl

theorem cell23_2420828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_2420828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420828 prefixEnd_2420828 := by exact prefixLift 2420828
  have htrace : WordTrace (prefixWord ++ tailWord_2420828) baseStart_2420828 baseEnd_2420828 := by
    simpa [prefixWord, tailWord_2420828, baseEnd_2420828] using wordTrace_append hprefix tailTrace_2420828
  have hstable : (prefixWord ++ tailWord_2420828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420828).length < 2 ^ (prefixWord ++ tailWord_2420828).sum := by decide
  have hdescent : baseEnd_2420828 < baseStart_2420828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420861 : List Nat := [1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_2420861 : Nat := 118140960795 + 2420861 * 2 ^ 59
def prefixEnd_2420861 : Nat := 4983230072969 + 3 ^ 40 * 2420861 * 2
def baseEnd_2420861 : Nat := 1243065290724158103904169

theorem tailTrace_2420861 : CollatzResearch.WordTrace tailWord_2420861 prefixEnd_2420861 1243065290724158103904169 := by
  unfold tailWord_2420861
  simp only [CollatzResearch.WordTrace]
  refine ⟨88296054482641521987462437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58864036321761014658308291 88296054482641521987462437)
  ·
    refine ⟨16555510215495285372649207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88296054482641521987462437 16555510215495285372649207)
    ·
      refine ⟨24833265323242928058973811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555510215495285372649207 24833265323242928058973811)
      ·
        refine ⟨37249897984864392088460717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24833265323242928058973811 37249897984864392088460717)
        ·
          refine ⟨13968711744324147033172769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37249897984864392088460717 13968711744324147033172769)
          ·
            refine ⟨10476533808243110274879577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13968711744324147033172769 10476533808243110274879577)
            ·
              refine ⟨7857400356182332706159683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10476533808243110274879577 7857400356182332706159683)
              ·
                refine ⟨11786100534273499059239525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7857400356182332706159683 11786100534273499059239525)
                ·
                  refine ⟨2209893850176281073607411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11786100534273499059239525 2209893850176281073607411)
                  ·
                    refine ⟨3314840775264421610411117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2209893850176281073607411 3314840775264421610411117)
                    ·
                      refine ⟨1243065290724158103904169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3314840775264421610411117 1243065290724158103904169)
                      ·
                        rfl

theorem cell23_2420861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_2420861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420861 prefixEnd_2420861 := by exact prefixLift 2420861
  have htrace : WordTrace (prefixWord ++ tailWord_2420861) baseStart_2420861 baseEnd_2420861 := by
    simpa [prefixWord, tailWord_2420861, baseEnd_2420861] using wordTrace_append hprefix tailTrace_2420861
  have hstable : (prefixWord ++ tailWord_2420861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420861).length < 2 ^ (prefixWord ++ tailWord_2420861).sum := by decide
  have hdescent : baseEnd_2420861 < baseStart_2420861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420888 : List Nat := [2, 1, 2, 4, 3, 1, 1, 1, 3, 3, 2]
def baseStart_2420888 : Nat := 118140960795 + 2420888 * 2 ^ 59
def prefixEnd_2420888 : Nat := 4983230072969 + 3 ^ 40 * 2420888 * 2
def baseEnd_2420888 : Nat := 1243079154701829498266545

theorem tailTrace_2420888 : CollatzResearch.WordTrace tailWord_2420888 prefixEnd_2420888 1243079154701829498266545 := by
  unfold tailWord_2420888
  simp only [CollatzResearch.WordTrace]
  refine ⟨44148519626771852799347659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58864692835695803732463545 44148519626771852799347659)
  ·
    refine ⟨66222779440157779199021489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44148519626771852799347659 66222779440157779199021489)
    ·
      refine ⟨49667084580118334399266117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66222779440157779199021489 49667084580118334399266117)
      ·
        refine ⟨9312578358772187699862397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49667084580118334399266117 9312578358772187699862397)
        ·
          refine ⟨3492216884539570387448399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9312578358772187699862397 3492216884539570387448399)
          ·
            refine ⟨5238325326809355581172599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492216884539570387448399 5238325326809355581172599)
            ·
              refine ⟨7857487990214033371758899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238325326809355581172599 7857487990214033371758899)
              ·
                refine ⟨11786231985321050057638349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7857487990214033371758899 11786231985321050057638349)
                ·
                  refine ⟨4419836994495393771614381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11786231985321050057638349 4419836994495393771614381)
                  ·
                    refine ⟨1657438872935772664355393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4419836994495393771614381 1657438872935772664355393)
                    ·
                      refine ⟨1243079154701829498266545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657438872935772664355393 1243079154701829498266545)
                      ·
                        rfl

theorem cell23_2420888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_2420888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420888 prefixEnd_2420888 := by exact prefixLift 2420888
  have htrace : WordTrace (prefixWord ++ tailWord_2420888) baseStart_2420888 baseEnd_2420888 := by
    simpa [prefixWord, tailWord_2420888, baseEnd_2420888] using wordTrace_append hprefix tailTrace_2420888
  have hstable : (prefixWord ++ tailWord_2420888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420888).length < 2 ^ (prefixWord ++ tailWord_2420888).sum := by decide
  have hdescent : baseEnd_2420888 < baseStart_2420888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420901 : List Nat := [1, 3, 1, 2, 1, 3, 3, 2, 1, 4, 2]
def baseStart_2420901 : Nat := 118140960795 + 2420901 * 2 ^ 59
def prefixEnd_2420901 : Nat := 4983230072969 + 3 ^ 40 * 2420901 * 2
def baseEnd_2420901 : Nat := 1243085829950337947403985

theorem tailTrace_2420901 : CollatzResearch.WordTrace tailWord_2420901 prefixEnd_2420901 1243085829950337947403985 := by
  unfold tailWord_2420901
  simp only [CollatzResearch.WordTrace]
  refine ⟨88297513402496608818918557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58865008934997739212612371 88297513402496608818918557)
  ·
    refine ⟨33111567525936228307094459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88297513402496608818918557 33111567525936228307094459)
    ·
      refine ⟨49667351288904342460641689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33111567525936228307094459 49667351288904342460641689)
      ·
        refine ⟨37250513466678256845481267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49667351288904342460641689 37250513466678256845481267)
        ·
          refine ⟨55875770200017385268221901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37250513466678256845481267 55875770200017385268221901)
          ·
            refine ⟨20953413825006519475583213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55875770200017385268221901 20953413825006519475583213)
            ·
              refine ⟨7857530184377444803343705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20953413825006519475583213 7857530184377444803343705)
              ·
                refine ⟨5893147638283083602507779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857530184377444803343705 5893147638283083602507779)
                ·
                  refine ⟨8839721457424625403761669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5893147638283083602507779 8839721457424625403761669)
                  ·
                    refine ⟨1657447773267117263205313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8839721457424625403761669 1657447773267117263205313)
                    ·
                      refine ⟨1243085829950337947403985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657447773267117263205313 1243085829950337947403985)
                      ·
                        rfl

theorem cell23_2420901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 1, 4, 2].length) (baseStart_2420901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420901 prefixEnd_2420901 := by exact prefixLift 2420901
  have htrace : WordTrace (prefixWord ++ tailWord_2420901) baseStart_2420901 baseEnd_2420901 := by
    simpa [prefixWord, tailWord_2420901, baseEnd_2420901] using wordTrace_append hprefix tailTrace_2420901
  have hstable : (prefixWord ++ tailWord_2420901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420901).length < 2 ^ (prefixWord ++ tailWord_2420901).sum := by decide
  have hdescent : baseEnd_2420901 < baseStart_2420901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420914 : List Nat := [3, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4]
def baseStart_2420914 : Nat := 118140960795 + 2420914 * 2 ^ 59
def prefixEnd_2420914 : Nat := 4983230072969 + 3 ^ 40 * 2420914 * 2
def baseEnd_2420914 : Nat := 1243092505198846396541425

theorem tailTrace_2420914 : CollatzResearch.WordTrace tailWord_2420914 prefixEnd_2420914 1243092505198846396541425 := by
  unfold tailWord_2420914
  simp only [CollatzResearch.WordTrace]
  refine ⟨22074496887862378009785449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58865325034299674692761197 22074496887862378009785449)
  ·
    refine ⟨16555872665896783507339087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22074496887862378009785449 16555872665896783507339087)
    ·
      refine ⟨24833808998845175261008631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16555872665896783507339087 24833808998845175261008631)
      ·
        refine ⟨37250713498267762891512947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24833808998845175261008631 37250713498267762891512947)
        ·
          refine ⟨55876070247401644337269421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37250713498267762891512947 55876070247401644337269421)
          ·
            refine ⟨20953526342775616626476033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55876070247401644337269421 20953526342775616626476033)
            ·
              refine ⟨15715144757081712469857025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20953526342775616626476033 15715144757081712469857025)
              ·
                refine ⟨11786358567811284352392769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15715144757081712469857025 11786358567811284352392769)
                ·
                  refine ⟨8839768925858463264294577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11786358567811284352392769 8839768925858463264294577)
                  ·
                    refine ⟨6629826694393847448220933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8839768925858463264294577 6629826694393847448220933)
                    ·
                      refine ⟨1243092505198846396541425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6629826694393847448220933 1243092505198846396541425)
                      ·
                        rfl

theorem cell23_2420914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_2420914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420914 prefixEnd_2420914 := by exact prefixLift 2420914
  have htrace : WordTrace (prefixWord ++ tailWord_2420914) baseStart_2420914 baseEnd_2420914 := by
    simpa [prefixWord, tailWord_2420914, baseEnd_2420914] using wordTrace_append hprefix tailTrace_2420914
  have hstable : (prefixWord ++ tailWord_2420914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420914).length < 2 ^ (prefixWord ++ tailWord_2420914).sum := by decide
  have hdescent : baseEnd_2420914 < baseStart_2420914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420927 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 8]
def baseStart_2420927 : Nat := 118140960795 + 2420927 * 2 ^ 59
def prefixEnd_2420927 : Nat := 4983230072969 + 3 ^ 40 * 2420927 * 2
def baseEnd_2420927 : Nat := 1243099180447354845678865

theorem tailTrace_2420927 : CollatzResearch.WordTrace tailWord_2420927 prefixEnd_2420927 1243099180447354845678865 := by
  unfold tailWord_2420927
  simp only [CollatzResearch.WordTrace]
  refine ⟨88298461700402415259365035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58865641133601610172910023 88298461700402415259365035)
  ·
    refine ⟨132447692550603622889047553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88298461700402415259365035 132447692550603622889047553)
    ·
      refine ⟨99335769412952717166785665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132447692550603622889047553 99335769412952717166785665)
      ·
        refine ⟨74501827059714537875089249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99335769412952717166785665 74501827059714537875089249)
        ·
          refine ⟨55876370294785903406316937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74501827059714537875089249 55876370294785903406316937)
          ·
            refine ⟨41907277721089427554737703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55876370294785903406316937 41907277721089427554737703)
            ·
              refine ⟨62860916581634141332106555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41907277721089427554737703 62860916581634141332106555)
              ·
                refine ⟨94291374872451211998159833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62860916581634141332106555 94291374872451211998159833)
                ·
                  refine ⟨70718531154338408998619875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94291374872451211998159833 70718531154338408998619875)
                  ·
                    refine ⟨106077796731507613497929813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 70718531154338408998619875 106077796731507613497929813)
                    ·
                      refine ⟨1243099180447354845678865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 106077796731507613497929813 1243099180447354845678865)
                      ·
                        rfl

theorem cell23_2420927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_2420927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420927 prefixEnd_2420927 := by exact prefixLift 2420927
  have htrace : WordTrace (prefixWord ++ tailWord_2420927) baseStart_2420927 baseEnd_2420927 := by
    simpa [prefixWord, tailWord_2420927, baseEnd_2420927] using wordTrace_append hprefix tailTrace_2420927
  have hstable : (prefixWord ++ tailWord_2420927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420927).length < 2 ^ (prefixWord ++ tailWord_2420927).sum := by decide
  have hdescent : baseEnd_2420927 < baseStart_2420927 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420956 : List Nat := [2, 2, 5, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2420956 : Nat := 118140960795 + 2420956 * 2 ^ 59
def prefixEnd_2420956 : Nat := 4983230072969 + 3 ^ 40 * 2420956 * 2
def baseEnd_2420956 : Nat := 1243114071386335232216233

theorem tailTrace_2420956 : CollatzResearch.WordTrace tailWord_2420956 prefixEnd_2420956 1243114071386335232216233 := by
  unfold tailWord_2420956
  simp only [CollatzResearch.WordTrace]
  refine ⟨44149759708648676606085361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58866346278198235474780481 44149759708648676606085361)
  ·
    refine ⟨33112319781486507454564021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44149759708648676606085361 33112319781486507454564021)
    ·
      refine ⟨3104279979514360073865377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33112319781486507454564021 3104279979514360073865377)
      ·
        refine ⟨2328209984635770055399033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3104279979514360073865377 2328209984635770055399033)
        ·
          refine ⟨1746157488476827541549275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328209984635770055399033 1746157488476827541549275)
          ·
            refine ⟨2619236232715241312323913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746157488476827541549275 2619236232715241312323913)
            ·
              refine ⟨1964427174536430984242935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619236232715241312323913 1964427174536430984242935)
              ·
                refine ⟨2946640761804646476364403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964427174536430984242935 2946640761804646476364403)
                ·
                  refine ⟨4419961142706969714546605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946640761804646476364403 4419961142706969714546605)
                  ·
                    refine ⟨1657485428515113642954977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4419961142706969714546605 1657485428515113642954977)
                    ·
                      refine ⟨1243114071386335232216233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657485428515113642954977 1243114071386335232216233)
                      ·
                        rfl

theorem cell23_2420956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2420956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420956 prefixEnd_2420956 := by exact prefixLift 2420956
  have htrace : WordTrace (prefixWord ++ tailWord_2420956) baseStart_2420956 baseEnd_2420956 := by
    simpa [prefixWord, tailWord_2420956, baseEnd_2420956] using wordTrace_append hprefix tailTrace_2420956
  have hstable : (prefixWord ++ tailWord_2420956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420956).length < 2 ^ (prefixWord ++ tailWord_2420956).sum := by decide
  have hdescent : baseEnd_2420956 < baseStart_2420956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2420991 : List Nat := [1, 1, 2, 2, 1, 4, 1, 3, 2, 4, 2]
def baseStart_2420991 : Nat := 118140960795 + 2420991 * 2 ^ 59
def prefixEnd_2420991 : Nat := 4983230072969 + 3 ^ 40 * 2420991 * 2
def baseEnd_2420991 : Nat := 1243132043209242595278571

theorem tailTrace_2420991 : CollatzResearch.WordTrace tailWord_2420991 prefixEnd_2420991 1243132043209242595278571 := by
  unfold tailWord_2420991
  simp only [CollatzResearch.WordTrace]
  refine ⟨88300795972170554189694827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58867197314780369459796551 88300795972170554189694827)
  ·
    refine ⟨132451193958255831284542241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88300795972170554189694827 132451193958255831284542241)
    ·
      refine ⟨99338395468691873463406681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132451193958255831284542241 99338395468691873463406681)
      ·
        refine ⟨74503796601518905097555011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99338395468691873463406681 74503796601518905097555011)
        ·
          refine ⟨111755694902278357646332517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74503796601518905097555011 111755694902278357646332517)
          ·
            refine ⟨20954192794177192058687347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111755694902278357646332517 20954192794177192058687347)
            ·
              refine ⟨31431289191265788088031021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20954192794177192058687347 31431289191265788088031021)
              ·
                refine ⟨11786733446724670533011633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31431289191265788088031021 11786733446724670533011633)
                ·
                  refine ⟨8840050085043502899758725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11786733446724670533011633 8840050085043502899758725)
                  ·
                    refine ⟨1657509390945656793704761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8840050085043502899758725 1657509390945656793704761)
                    ·
                      refine ⟨1243132043209242595278571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657509390945656793704761 1243132043209242595278571)
                      ·
                        rfl

theorem cell23_2420991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 2, 4, 2].length) (baseStart_2420991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2420991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2420991 prefixEnd_2420991 := by exact prefixLift 2420991
  have htrace : WordTrace (prefixWord ++ tailWord_2420991) baseStart_2420991 baseEnd_2420991 := by
    simpa [prefixWord, tailWord_2420991, baseEnd_2420991] using wordTrace_append hprefix tailTrace_2420991
  have hstable : (prefixWord ++ tailWord_2420991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2420991).length < 2 ^ (prefixWord ++ tailWord_2420991).sum := by decide
  have hdescent : baseEnd_2420991 < baseStart_2420991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2420991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421001 : List Nat := [1, 2, 1, 1, 3, 4, 2, 2, 3, 4]
def baseStart_2421001 : Nat := 118140960795 + 2421001 * 2 ^ 59
def prefixEnd_2421001 : Nat := 4983230072969 + 3 ^ 40 * 2421001 * 2
def baseEnd_2421001 : Nat := 414379059338595852051175

theorem tailTrace_2421001 : CollatzResearch.WordTrace tailWord_2421001 prefixEnd_2421001 414379059338595852051175 := by
  unfold tailWord_2421001
  simp only [CollatzResearch.WordTrace]
  refine ⟨88301160702134325897558857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58867440468089550598372571 88301160702134325897558857)
  ·
    refine ⟨66225870526600744423169143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88301160702134325897558857 66225870526600744423169143)
    ·
      refine ⟨99338805789901116634753715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66225870526600744423169143 99338805789901116634753715)
      ·
        refine ⟨149008208684851674952130573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99338805789901116634753715 149008208684851674952130573)
        ·
          refine ⟨55878078256819378107048965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 149008208684851674952130573 55878078256819378107048965)
          ·
            refine ⟨10477139673153633395071681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55878078256819378107048965 10477139673153633395071681)
            ·
              refine ⟨7857854754865225046303761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10477139673153633395071681 7857854754865225046303761)
              ·
                refine ⟨5893391066148918784727821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857854754865225046303761 5893391066148918784727821)
                ·
                  refine ⟨2210021649805844544272933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5893391066148918784727821 2210021649805844544272933)
                  ·
                    refine ⟨414379059338595852051175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210021649805844544272933 414379059338595852051175)
                    ·
                      rfl

theorem cell23_2421001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2, 3, 4].length) (baseStart_2421001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421001 prefixEnd_2421001 := by exact prefixLift 2421001
  have htrace : WordTrace (prefixWord ++ tailWord_2421001) baseStart_2421001 baseEnd_2421001 := by
    simpa [prefixWord, tailWord_2421001, baseEnd_2421001] using wordTrace_append hprefix tailTrace_2421001
  have hstable : (prefixWord ++ tailWord_2421001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421001).length < 2 ^ (prefixWord ++ tailWord_2421001).sum := by decide
  have hdescent : baseEnd_2421001 < baseStart_2421001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421004 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 2, 4, 4]
def baseStart_2421004 : Nat := 118140960795 + 2421004 * 2 ^ 59
def prefixEnd_2421004 : Nat := 4983230072969 + 3 ^ 40 * 2421004 * 2
def baseEnd_2421004 : Nat := 1243138718457751044416011

theorem tailTrace_2421004 : CollatzResearch.WordTrace tailWord_2421004 prefixEnd_2421004 1243138718457751044416011 := by
  unfold tailWord_2421004
  simp only [CollatzResearch.WordTrace]
  refine ⟨44150635060561728704959033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58867513414082304939945377 44150635060561728704959033)
  ·
    refine ⟨33112976295421296528719275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44150635060561728704959033 33112976295421296528719275)
    ·
      refine ⟨49669464443131944793078913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33112976295421296528719275 49669464443131944793078913)
      ·
        refine ⟨37252098332348958594809185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49669464443131944793078913 37252098332348958594809185)
        ·
          refine ⟨27939073749261718946106889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37252098332348958594809185 27939073749261718946106889)
          ·
            refine ⟨20954305311946289209580167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27939073749261718946106889 20954305311946289209580167)
            ·
              refine ⟨31431457967919433814370251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20954305311946289209580167 31431457967919433814370251)
              ·
                refine ⟨47147186951879150721555377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31431457967919433814370251 47147186951879150721555377)
                ·
                  refine ⟨35360390213909363041166533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47147186951879150721555377 35360390213909363041166533)
                  ·
                    refine ⟨6630073165108005570218725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35360390213909363041166533 6630073165108005570218725)
                    ·
                      refine ⟨1243138718457751044416011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6630073165108005570218725 1243138718457751044416011)
                      ·
                        rfl

theorem cell23_2421004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_2421004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421004 prefixEnd_2421004 := by exact prefixLift 2421004
  have htrace : WordTrace (prefixWord ++ tailWord_2421004) baseStart_2421004 baseEnd_2421004 := by
    simpa [prefixWord, tailWord_2421004, baseEnd_2421004] using wordTrace_append hprefix tailTrace_2421004
  have hstable : (prefixWord ++ tailWord_2421004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421004).length < 2 ^ (prefixWord ++ tailWord_2421004).sum := by decide
  have hdescent : baseEnd_2421004 < baseStart_2421004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421028 : List Nat := [2, 3, 1, 3, 1, 3, 1, 2, 2, 2, 3]
def baseStart_2421028 : Nat := 118140960795 + 2421028 * 2 ^ 59
def prefixEnd_2421028 : Nat := 4983230072969 + 3 ^ 40 * 2421028 * 2
def baseEnd_2421028 : Nat := 1243151041993458950515901

theorem tailTrace_2421028 : CollatzResearch.WordTrace tailWord_2421028 prefixEnd_2421028 1243151041993458950515901 := by
  unfold tailWord_2421028
  simp only [CollatzResearch.WordTrace]
  refine ⟨44151072736518254754395869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58868096982024339672527825 44151072736518254754395869)
  ·
    refine ⟨16556652276194345532898451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44151072736518254754395869 16556652276194345532898451)
    ·
      refine ⟨24834978414291518299347677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16556652276194345532898451 24834978414291518299347677)
      ·
        refine ⟨9313116905359319362255379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24834978414291518299347677 9313116905359319362255379)
        ·
          refine ⟨13969675358038979043383069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9313116905359319362255379 13969675358038979043383069)
          ·
            refine ⟨5238628259264617141268651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13969675358038979043383069 5238628259264617141268651)
            ·
              refine ⟨7857942388896925711902977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238628259264617141268651 7857942388896925711902977)
              ·
                refine ⟨5893456791672694283927233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7857942388896925711902977 5893456791672694283927233)
                ·
                  refine ⟨4420092593754520712945425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5893456791672694283927233 4420092593754520712945425)
                  ·
                    refine ⟨3315069445315890534709069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4420092593754520712945425 3315069445315890534709069)
                    ·
                      refine ⟨1243151041993458950515901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3315069445315890534709069 1243151041993458950515901)
                      ·
                        rfl

theorem cell23_2421028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_2421028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421028 prefixEnd_2421028 := by exact prefixLift 2421028
  have htrace : WordTrace (prefixWord ++ tailWord_2421028) baseStart_2421028 baseEnd_2421028 := by
    simpa [prefixWord, tailWord_2421028, baseEnd_2421028] using wordTrace_append hprefix tailTrace_2421028
  have hstable : (prefixWord ++ tailWord_2421028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421028).length < 2 ^ (prefixWord ++ tailWord_2421028).sum := by decide
  have hdescent : baseEnd_2421028 < baseStart_2421028 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421098 : List Nat := [3, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2421098 : Nat := 118140960795 + 2421098 * 2 ^ 59
def prefixEnd_2421098 : Nat := 4983230072969 + 3 ^ 40 * 2421098 * 2
def baseEnd_2421098 : Nat := 1243186985639273676640579

theorem tailTrace_2421098 : CollatzResearch.WordTrace tailWord_2421098 prefixEnd_2421098 1243186985639273676640579 := by
  unfold tailWord_2421098
  simp only [CollatzResearch.WordTrace]
  refine ⟨22076174645695727865959987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58869799055188607642559965 22076174645695727865959987)
  ·
    refine ⟨33114261968543591798939981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22076174645695727865959987 33114261968543591798939981)
    ·
      refine ⟨12417848238203846924602493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33114261968543591798939981 12417848238203846924602493)
      ·
        refine ⟨4656693089326442596725935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12417848238203846924602493 4656693089326442596725935)
        ·
          refine ⟨6985039633989663895088903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4656693089326442596725935 6985039633989663895088903)
          ·
            refine ⟨10477559450984495842633355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985039633989663895088903 10477559450984495842633355)
            ·
              refine ⟨15716339176476743763950033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10477559450984495842633355 15716339176476743763950033)
              ·
                refine ⟨11787254382357557822962525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15716339176476743763950033 11787254382357557822962525)
                ·
                  refine ⟨4420220393384084183610947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11787254382357557822962525 4420220393384084183610947)
                  ·
                    refine ⟨6630330590076126275416421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4420220393384084183610947 6630330590076126275416421)
                    ·
                      refine ⟨1243186985639273676640579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6630330590076126275416421 1243186985639273676640579)
                      ·
                        rfl

theorem cell23_2421098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2421098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421098 prefixEnd_2421098 := by exact prefixLift 2421098
  have htrace : WordTrace (prefixWord ++ tailWord_2421098) baseStart_2421098 baseEnd_2421098 := by
    simpa [prefixWord, tailWord_2421098, baseEnd_2421098] using wordTrace_append hprefix tailTrace_2421098
  have hstable : (prefixWord ++ tailWord_2421098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421098).length < 2 ^ (prefixWord ++ tailWord_2421098).sum := by decide
  have hdescent : baseEnd_2421098 < baseStart_2421098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421101 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2421101 : Nat := 118140960795 + 2421101 * 2 ^ 59
def prefixEnd_2421101 : Nat := 4983230072969 + 3 ^ 40 * 2421101 * 2
def baseEnd_2421101 : Nat := 1243188526081237164903065

theorem tailTrace_2421101 : CollatzResearch.WordTrace tailWord_2421101 prefixEnd_2421101 1243188526081237164903065 := by
  unfold tailWord_2421101
  simp only [CollatzResearch.WordTrace]
  refine ⟨88304808001772042976199157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58869872001181361984132771 88304808001772042976199157)
  ·
    refine ⟨8278575750166129029018671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88304808001772042976199157 8278575750166129029018671)
    ·
      refine ⟨12417863625249193543528007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8278575750166129029018671 12417863625249193543528007)
      ·
        refine ⟨18626795437873790315292011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12417863625249193543528007 18626795437873790315292011)
        ·
          refine ⟨27940193156810685472938017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18626795437873790315292011 27940193156810685472938017)
          ·
            refine ⟨20955144867608014104703513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27940193156810685472938017 20955144867608014104703513)
            ·
              refine ⟨15716358650706010578527635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20955144867608014104703513 15716358650706010578527635)
              ·
                refine ⟨23574537976059015867791453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15716358650706010578527635 23574537976059015867791453)
                ·
                  refine ⟨8840451741022130950421795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23574537976059015867791453 8840451741022130950421795)
                  ·
                    refine ⟨13260677611533196425632693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8840451741022130950421795 13260677611533196425632693)
                    ·
                      refine ⟨1243188526081237164903065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13260677611533196425632693 1243188526081237164903065)
                      ·
                        rfl

theorem cell23_2421101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2421101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421101 prefixEnd_2421101 := by exact prefixLift 2421101
  have htrace : WordTrace (prefixWord ++ tailWord_2421101) baseStart_2421101 baseEnd_2421101 := by
    simpa [prefixWord, tailWord_2421101, baseEnd_2421101] using wordTrace_append hprefix tailTrace_2421101
  have hstable : (prefixWord ++ tailWord_2421101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421101).length < 2 ^ (prefixWord ++ tailWord_2421101).sum := by decide
  have hdescent : baseEnd_2421101 < baseStart_2421101 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421115 : List Nat := [1, 1, 1, 1, 1, 8, 1, 2, 3, 2, 2]
def baseStart_2421115 : Nat := 118140960795 + 2421115 * 2 ^ 59
def prefixEnd_2421115 : Nat := 4983230072969 + 3 ^ 40 * 2421115 * 2
def baseEnd_2421115 : Nat := 1243195714810400110128001

theorem tailTrace_2421115 : CollatzResearch.WordTrace tailWord_2421115 prefixEnd_2421115 1243195714810400110128001 := by
  unfold tailWord_2421115
  simp only [CollatzResearch.WordTrace]
  refine ⟨88305318623721323367208799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58870212415814215578139199 88305318623721323367208799)
  ·
    refine ⟨132457977935581985050813199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88305318623721323367208799 132457977935581985050813199)
    ·
      refine ⟨198686966903372977576219799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132457977935581985050813199 198686966903372977576219799)
      ·
        refine ⟨298030450355059466364329699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198686966903372977576219799 298030450355059466364329699)
        ·
          refine ⟨447045675532589199546494549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298030450355059466364329699 447045675532589199546494549)
          ·
            refine ⟨5238816510147529682185483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 447045675532589199546494549 5238816510147529682185483)
            ·
              refine ⟨7858224765221294523278225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238816510147529682185483 7858224765221294523278225)
              ·
                refine ⟨5893668573915970892458669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7858224765221294523278225 5893668573915970892458669)
                ·
                  refine ⟨2210125715218489084672001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5893668573915970892458669 2210125715218489084672001)
                  ·
                    refine ⟨1657594286413866813504001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2210125715218489084672001 1657594286413866813504001)
                    ·
                      refine ⟨1243195714810400110128001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657594286413866813504001 1243195714810400110128001)
                      ·
                        rfl

theorem cell23_2421115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 2, 3, 2, 2].length) (baseStart_2421115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421115 prefixEnd_2421115 := by exact prefixLift 2421115
  have htrace : WordTrace (prefixWord ++ tailWord_2421115) baseStart_2421115 baseEnd_2421115 := by
    simpa [prefixWord, tailWord_2421115, baseEnd_2421115] using wordTrace_append hprefix tailTrace_2421115
  have hstable : (prefixWord ++ tailWord_2421115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421115).length < 2 ^ (prefixWord ++ tailWord_2421115).sum := by decide
  have hdescent : baseEnd_2421115 < baseStart_2421115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421132 : List Nat := [2, 2, 1, 2, 1, 4, 1, 5, 1, 2, 2]
def baseStart_2421132 : Nat := 118140960795 + 2421132 * 2 ^ 59
def prefixEnd_2421132 : Nat := 4983230072969 + 3 ^ 40 * 2421132 * 2
def baseEnd_2421132 : Nat := 1243204443981526543615423

theorem tailTrace_2421132 : CollatzResearch.WordTrace tailWord_2421132 prefixEnd_2421132 1243204443981526543615423 := by
  unfold tailWord_2421132
  simp only [CollatzResearch.WordTrace]
  refine ⟨44152969332329867635288825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58870625776439823513718433 44152969332329867635288825)
  ·
    refine ⟨33114726999247400726466619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44152969332329867635288825 33114726999247400726466619)
    ·
      refine ⟨49672090498871101089699929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33114726999247400726466619 49672090498871101089699929)
      ·
        refine ⟨37254067874153325817274947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49672090498871101089699929 37254067874153325817274947)
        ·
          refine ⟨55881101811229988725912421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37254067874153325817274947 55881101811229988725912421)
          ·
            refine ⟨10477706589605622886108579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55881101811229988725912421 10477706589605622886108579)
            ·
              refine ⟨15716559884408434329162869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10477706589605622886108579 15716559884408434329162869)
              ·
                refine ⟨1473427489163290718359019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15716559884408434329162869 1473427489163290718359019)
                ·
                  refine ⟨2210141233744936077538529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473427489163290718359019 2210141233744936077538529)
                  ·
                    refine ⟨1657605925308702058153897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2210141233744936077538529 1657605925308702058153897)
                    ·
                      refine ⟨1243204443981526543615423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657605925308702058153897 1243204443981526543615423)
                      ·
                        rfl

theorem cell23_2421132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 5, 1, 2, 2].length) (baseStart_2421132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421132 prefixEnd_2421132 := by exact prefixLift 2421132
  have htrace : WordTrace (prefixWord ++ tailWord_2421132) baseStart_2421132 baseEnd_2421132 := by
    simpa [prefixWord, tailWord_2421132, baseEnd_2421132] using wordTrace_append hprefix tailTrace_2421132
  have hstable : (prefixWord ++ tailWord_2421132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421132).length < 2 ^ (prefixWord ++ tailWord_2421132).sum := by decide
  have hdescent : baseEnd_2421132 < baseStart_2421132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421162 : List Nat := [3, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2421162 : Nat := 118140960795 + 2421162 * 2 ^ 59
def prefixEnd_2421162 : Nat := 4983230072969 + 3 ^ 40 * 2421162 * 2
def baseEnd_2421162 : Nat := 1243219848401161426240285

theorem tailTrace_2421162 : CollatzResearch.WordTrace tailWord_2421162 prefixEnd_2421162 1243219848401161426240285 := by
  unfold tailWord_2421162
  simp only [CollatzResearch.WordTrace]
  refine ⟨22076758213637762598542435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58871355236367366929446493 22076758213637762598542435)
  ·
    refine ⟨33115137320456643897813653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22076758213637762598542435 33115137320456643897813653)
    ·
      refine ⟨1552272061896405182710015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 33115137320456643897813653 1552272061896405182710015)
      ·
        refine ⟨2328408092844607774065023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552272061896405182710015 2328408092844607774065023)
        ·
          refine ⟨3492612139266911661097535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328408092844607774065023 3492612139266911661097535)
          ·
            refine ⟨5238918208900367491646303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492612139266911661097535 5238918208900367491646303)
            ·
              refine ⟨7858377313350551237469455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5238918208900367491646303 7858377313350551237469455)
              ·
                refine ⟨11787565970025826856204183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7858377313350551237469455 11787565970025826856204183)
                ·
                  refine ⟨17681348955038740284306275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11787565970025826856204183 17681348955038740284306275)
                  ·
                    refine ⟨26522023432558110426459413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17681348955038740284306275 26522023432558110426459413)
                    ·
                      refine ⟨1243219848401161426240285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26522023432558110426459413 1243219848401161426240285)
                      ·
                        rfl

theorem cell23_2421162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2421162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421162 prefixEnd_2421162 := by exact prefixLift 2421162
  have htrace : WordTrace (prefixWord ++ tailWord_2421162) baseStart_2421162 baseEnd_2421162 := by
    simpa [prefixWord, tailWord_2421162, baseEnd_2421162] using wordTrace_append hprefix tailTrace_2421162
  have hstable : (prefixWord ++ tailWord_2421162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421162).length < 2 ^ (prefixWord ++ tailWord_2421162).sum := by decide
  have hdescent : baseEnd_2421162 < baseStart_2421162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421175 : List Nat := [1, 1, 3, 1, 3, 3, 1, 4, 1, 3, 2]
def baseStart_2421175 : Nat := 118140960795 + 2421175 * 2 ^ 59
def prefixEnd_2421175 : Nat := 4983230072969 + 3 ^ 40 * 2421175 * 2
def baseEnd_2421175 : Nat := 1243226523649669875377725

theorem tailTrace_2421175 : CollatzResearch.WordTrace tailWord_2421175 prefixEnd_2421175 1243226523649669875377725 := by
  unfold tailWord_2421175
  simp only [CollatzResearch.WordTrace]
  refine ⟨88307507003503953614392979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58871671335669302409595319 88307507003503953614392979)
  ·
    refine ⟨132461260505255930421589469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88307507003503953614392979 132461260505255930421589469)
    ·
      refine ⟨49672972689470973908096051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132461260505255930421589469 49672972689470973908096051)
      ·
        refine ⟨74509459034206460862144077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49672972689470973908096051 74509459034206460862144077)
        ·
          refine ⟨27941047137827422823304029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74509459034206460862144077 27941047137827422823304029)
          ·
            refine ⟨10477892676685283558739011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27941047137827422823304029 10477892676685283558739011)
            ·
              refine ⟨15716839015027925338108517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10477892676685283558739011 15716839015027925338108517)
              ·
                refine ⟨2946907315317736000895347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15716839015027925338108517 2946907315317736000895347)
                ·
                  refine ⟨4420360972976604001343021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2946907315317736000895347 4420360972976604001343021)
                  ·
                    refine ⟨1657635364866226500503633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4420360972976604001343021 1657635364866226500503633)
                    ·
                      refine ⟨1243226523649669875377725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657635364866226500503633 1243226523649669875377725)
                      ·
                        rfl

theorem cell23_2421175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 1, 3, 2].length) (baseStart_2421175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421175 prefixEnd_2421175 := by exact prefixLift 2421175
  have htrace : WordTrace (prefixWord ++ tailWord_2421175) baseStart_2421175 baseEnd_2421175 := by
    simpa [prefixWord, tailWord_2421175, baseEnd_2421175] using wordTrace_append hprefix tailTrace_2421175
  have hstable : (prefixWord ++ tailWord_2421175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421175).length < 2 ^ (prefixWord ++ tailWord_2421175).sum := by decide
  have hdescent : baseEnd_2421175 < baseStart_2421175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421191 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_2421191 : Nat := 118140960795 + 2421191 * 2 ^ 59
def prefixEnd_2421191 : Nat := 4983230072969 + 3 ^ 40 * 2421191 * 2
def baseEnd_2421191 : Nat := 1243234739340141812777651

theorem tailTrace_2421191 : CollatzResearch.WordTrace tailWord_2421191 prefixEnd_2421191 1243234739340141812777651 := by
  unfold tailWord_2421191
  simp only [CollatzResearch.WordTrace]
  refine ⟨88308090571445988346975427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58872060380963992231316951 88308090571445988346975427)
  ·
    refine ⟨132462135857168982520463141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88308090571445988346975427 132462135857168982520463141)
    ·
      refine ⟨24836650473219184222586839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132462135857168982520463141 24836650473219184222586839)
      ·
        refine ⟨37254975709828776333880259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24836650473219184222586839 37254975709828776333880259)
        ·
          refine ⟨55882463564743164500820389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37254975709828776333880259 55882463564743164500820389)
          ·
            refine ⟨10477961918389343343903823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55882463564743164500820389 10477961918389343343903823)
            ·
              refine ⟨15716942877584015015855735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10477961918389343343903823 15716942877584015015855735)
              ·
                refine ⟨23575414316376022523783603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15716942877584015015855735 23575414316376022523783603)
                ·
                  refine ⟨35363121474564033785675405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23575414316376022523783603 35363121474564033785675405)
                  ·
                    refine ⟨13261170552961512669628277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35363121474564033785675405 13261170552961512669628277)
                    ·
                      refine ⟨1243234739340141812777651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13261170552961512669628277 1243234739340141812777651)
                      ·
                        rfl

theorem cell23_2421191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_2421191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421191 prefixEnd_2421191 := by exact prefixLift 2421191
  have htrace : WordTrace (prefixWord ++ tailWord_2421191) baseStart_2421191 baseEnd_2421191 := by
    simpa [prefixWord, tailWord_2421191, baseEnd_2421191] using wordTrace_append hprefix tailTrace_2421191
  have hstable : (prefixWord ++ tailWord_2421191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421191).length < 2 ^ (prefixWord ++ tailWord_2421191).sum := by decide
  have hdescent : baseEnd_2421191 < baseStart_2421191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421201 : List Nat := [1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_2421201 : Nat := 118140960795 + 2421201 * 2 ^ 59
def prefixEnd_2421201 : Nat := 4983230072969 + 3 ^ 40 * 2421201 * 2
def baseEnd_2421201 : Nat := 1243239874146686773652605

theorem tailTrace_2421201 : CollatzResearch.WordTrace tailWord_2421201 prefixEnd_2421201 1243239874146686773652605 := by
  unfold tailWord_2421201
  simp only [CollatzResearch.WordTrace]
  refine ⟨88308455301409760054839457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58872303534273173369892971 88308455301409760054839457)
  ·
    refine ⟨66231341476057320041129593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88308455301409760054839457 66231341476057320041129593)
    ·
      refine ⟨49673506107042990030847195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66231341476057320041129593 49673506107042990030847195)
      ·
        refine ⟨74510259160564485046270793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49673506107042990030847195 74510259160564485046270793)
        ·
          refine ⟨55882694370423363784703095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74510259160564485046270793 55882694370423363784703095)
          ·
            refine ⟨83824041555635045677054643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55882694370423363784703095 83824041555635045677054643)
            ·
              refine ⟨125736062333452568515581965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83824041555635045677054643 125736062333452568515581965)
              ·
                refine ⟨47151023375044713193343237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125736062333452568515581965 47151023375044713193343237)
                ·
                  refine ⟨8840816882820883723751857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47151023375044713193343237 8840816882820883723751857)
                  ·
                    refine ⟨6630612662115662792813893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8840816882820883723751857 6630612662115662792813893)
                    ·
                      refine ⟨1243239874146686773652605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6630612662115662792813893 1243239874146686773652605)
                      ·
                        rfl

theorem cell23_2421201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_2421201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421201 prefixEnd_2421201 := by exact prefixLift 2421201
  have htrace : WordTrace (prefixWord ++ tailWord_2421201) baseStart_2421201 baseEnd_2421201 := by
    simpa [prefixWord, tailWord_2421201, baseEnd_2421201] using wordTrace_append hprefix tailTrace_2421201
  have hstable : (prefixWord ++ tailWord_2421201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421201).length < 2 ^ (prefixWord ++ tailWord_2421201).sum := by decide
  have hdescent : baseEnd_2421201 < baseStart_2421201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421241 : List Nat := [1, 2, 1, 3, 1, 2, 2, 3, 1, 7]
def baseStart_2421241 : Nat := 118140960795 + 2421241 * 2 ^ 59
def prefixEnd_2421241 : Nat := 4983230072969 + 3 ^ 40 * 2421241 * 2
def baseEnd_2421241 : Nat := 414420137790955539050807

theorem tailTrace_2421241 : CollatzResearch.WordTrace tailWord_2421241 prefixEnd_2421241 414420137790955539050807 := by
  unfold tailWord_2421241
  simp only [CollatzResearch.WordTrace]
  refine ⟨88309914221264846886295577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58873276147509897924197051 88309914221264846886295577)
  ·
    refine ⟨66232435665948635164721683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88309914221264846886295577 66232435665948635164721683)
    ·
      refine ⟨99348653498922952747082525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66232435665948635164721683 99348653498922952747082525)
      ·
        refine ⟨37255745062096107280155947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99348653498922952747082525 37255745062096107280155947)
        ·
          refine ⟨55883617593144160920233921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37255745062096107280155947 55883617593144160920233921)
          ·
            refine ⟨41912713194858120690175441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55883617593144160920233921 41912713194858120690175441)
            ·
              refine ⟨31434534896143590517631581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41912713194858120690175441 31434534896143590517631581)
              ·
                refine ⟨11787950586053846444111843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31434534896143590517631581 11787950586053846444111843)
                ·
                  refine ⟨17681925879080769666167765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11787950586053846444111843 17681925879080769666167765)
                  ·
                    refine ⟨414420137790955539050807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17681925879080769666167765 414420137790955539050807)
                    ·
                      rfl

theorem cell23_2421241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 3, 1, 7].length) (baseStart_2421241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421241 prefixEnd_2421241 := by exact prefixLift 2421241
  have htrace : WordTrace (prefixWord ++ tailWord_2421241) baseStart_2421241 baseEnd_2421241 := by
    simpa [prefixWord, tailWord_2421241, baseEnd_2421241] using wordTrace_append hprefix tailTrace_2421241
  have hstable : (prefixWord ++ tailWord_2421241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421241).length < 2 ^ (prefixWord ++ tailWord_2421241).sum := by decide
  have hdescent : baseEnd_2421241 < baseStart_2421241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421248 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 6, 5, 2]
def baseStart_2421248 : Nat := 118140960795 + 2421248 * 2 ^ 59
def prefixEnd_2421248 : Nat := 4983230072969 + 3 ^ 40 * 2421248 * 2
def baseEnd_2421248 : Nat := 1243264007737448089764889

theorem tailTrace_2421248 : CollatzResearch.WordTrace tailWord_2421248 prefixEnd_2421248 1243264007737448089764889 := by
  unfold tailWord_2421248
  simp only [CollatzResearch.WordTrace]
  refine ⟨44155084766119743540900199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58873446354826324721200265 44155084766119743540900199)
  ·
    refine ⟨66232627149179615311350299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44155084766119743540900199 66232627149179615311350299)
    ·
      refine ⟨99348940723769422967025449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66232627149179615311350299 99348940723769422967025449)
      ·
        refine ⟨74511705542827067225269087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99348940723769422967025449 74511705542827067225269087)
        ·
          refine ⟨111767558314240600837903631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74511705542827067225269087 111767558314240600837903631)
          ·
            refine ⟨167651337471360901256855447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111767558314240600837903631 167651337471360901256855447)
            ·
              refine ⟨251477006207041351885283171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167651337471360901256855447 251477006207041351885283171)
              ·
                refine ⟨377215509310562027827924757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251477006207041351885283171 377215509310562027827924757)
                ·
                  refine ⟨17681976998932595054433973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 377215509310562027827924757 17681976998932595054433973)
                  ·
                    refine ⟨1657685343649930786353185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17681976998932595054433973 1657685343649930786353185)
                    ·
                      refine ⟨1243264007737448089764889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657685343649930786353185 1243264007737448089764889)
                      ·
                        rfl

theorem cell23_2421248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 6, 5, 2].length) (baseStart_2421248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421248 prefixEnd_2421248 := by exact prefixLift 2421248
  have htrace : WordTrace (prefixWord ++ tailWord_2421248) baseStart_2421248 baseEnd_2421248 := by
    simpa [prefixWord, tailWord_2421248, baseEnd_2421248] using wordTrace_append hprefix tailTrace_2421248
  have hstable : (prefixWord ++ tailWord_2421248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421248).length < 2 ^ (prefixWord ++ tailWord_2421248).sum := by decide
  have hdescent : baseEnd_2421248 < baseStart_2421248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421251 : List Nat := [1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5]
def baseStart_2421251 : Nat := 118140960795 + 2421251 * 2 ^ 59
def prefixEnd_2421251 : Nat := 4983230072969 + 3 ^ 40 * 2421251 * 2
def baseEnd_2421251 : Nat := 1243265548179411578027375

theorem tailTrace_2421251 : CollatzResearch.WordTrace tailWord_2421251 prefixEnd_2421251 1243265548179411578027375 := by
  unfold tailWord_2421251
  simp only [CollatzResearch.WordTrace]
  refine ⟨88310278951228618594159607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58873519300819079062773071 88310278951228618594159607)
  ·
    refine ⟨132465418426842927891239411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88310278951228618594159607 132465418426842927891239411)
    ·
      refine ⟨198698127640264391836859117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132465418426842927891239411 198698127640264391836859117)
      ·
        refine ⟨74511797865099146938822169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198698127640264391836859117 74511797865099146938822169)
        ·
          refine ⟨55883848398824360204116627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74511797865099146938822169 55883848398824360204116627)
          ·
            refine ⟨83825772598236540306174941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55883848398824360204116627 83825772598236540306174941)
            ·
              refine ⟨31434664724338702614815603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83825772598236540306174941 31434664724338702614815603)
              ·
                refine ⟨47151997086508053922223405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31434664724338702614815603 47151997086508053922223405)
                ·
                  refine ⟨17681998907440520220833777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47151997086508053922223405 17681998907440520220833777)
                  ·
                    refine ⟨13261499180580390165625333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17681998907440520220833777 13261499180580390165625333)
                    ·
                      refine ⟨1243265548179411578027375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13261499180580390165625333 1243265548179411578027375)
                      ·
                        rfl

theorem cell23_2421251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_2421251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421251 prefixEnd_2421251 := by exact prefixLift 2421251
  have htrace : WordTrace (prefixWord ++ tailWord_2421251) baseStart_2421251 baseEnd_2421251 := by
    simpa [prefixWord, tailWord_2421251, baseEnd_2421251] using wordTrace_append hprefix tailTrace_2421251
  have hstable : (prefixWord ++ tailWord_2421251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421251).length < 2 ^ (prefixWord ++ tailWord_2421251).sum := by decide
  have hdescent : baseEnd_2421251 < baseStart_2421251 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421258 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 2, 5]
def baseStart_2421258 : Nat := 118140960795 + 2421258 * 2 ^ 59
def prefixEnd_2421258 : Nat := 4983230072969 + 3 ^ 40 * 2421258 * 2
def baseEnd_2421258 : Nat := 414423047514664350213281

theorem tailTrace_2421258 : CollatzResearch.WordTrace tailWord_2421258 prefixEnd_2421258 414423047514664350213281 := by
  unfold tailWord_2421258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22077633565550814697416107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58873689508135505859776285 22077633565550814697416107)
  ·
    refine ⟨33116450348326222046124161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22077633565550814697416107 33116450348326222046124161)
    ·
      refine ⟨24837337761244666534593121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33116450348326222046124161 24837337761244666534593121)
      ·
        refine ⟨18628003320933499900944841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24837337761244666534593121 18628003320933499900944841)
        ·
          refine ⟨13971002490700124925708631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18628003320933499900944841 13971002490700124925708631)
          ·
            refine ⟨20956503736050187388562947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13971002490700124925708631 20956503736050187388562947)
            ·
              refine ⟨31434755604075281082844421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20956503736050187388562947 31434755604075281082844421)
              ·
                refine ⟨5894016675764115203033329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31434755604075281082844421 5894016675764115203033329)
                ·
                  refine ⟨4420512506823086402274997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5894016675764115203033329 4420512506823086402274997)
                  ·
                    refine ⟨414423047514664350213281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4420512506823086402274997 414423047514664350213281)
                    ·
                      rfl

theorem cell23_2421258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_2421258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421258 prefixEnd_2421258 := by exact prefixLift 2421258
  have htrace : WordTrace (prefixWord ++ tailWord_2421258) baseStart_2421258 baseEnd_2421258 := by
    simpa [prefixWord, tailWord_2421258, baseEnd_2421258] using wordTrace_append hprefix tailTrace_2421258
  have hstable : (prefixWord ++ tailWord_2421258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421258).length < 2 ^ (prefixWord ++ tailWord_2421258).sum := by decide
  have hdescent : baseEnd_2421258 < baseStart_2421258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421262 : List Nat := [4, 1, 1, 2, 3, 1, 4, 2, 5]
def baseStart_2421262 : Nat := 118140960795 + 2421262 * 2 ^ 59
def prefixEnd_2421262 : Nat := 4983230072969 + 3 ^ 40 * 2421262 * 2
def baseEnd_2421262 : Nat := 138141244051845670554425

theorem tailTrace_2421262 : CollatzResearch.WordTrace tailWord_2421262 prefixEnd_2421262 138141244051845670554425 := by
  unfold tailWord_2421262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038835019273595934101255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58873786769459178315206693 11038835019273595934101255)
  ·
    refine ⟨16558252528910393901151883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11038835019273595934101255 16558252528910393901151883)
    ·
      refine ⟨24837378793365590851727825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16558252528910393901151883 24837378793365590851727825)
      ·
        refine ⟨18628034095024193138795869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24837378793365590851727825 18628034095024193138795869)
        ·
          refine ⟨6985512785634072427048451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18628034095024193138795869 6985512785634072427048451)
          ·
            refine ⟨10478269178451108640572677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985512785634072427048451 10478269178451108640572677)
            ·
              refine ⟨1964675470959582870107377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10478269178451108640572677 1964675470959582870107377)
              ·
                refine ⟨1473506603219687152580533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1964675470959582870107377 1473506603219687152580533)
                ·
                  refine ⟨138141244051845670554425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1473506603219687152580533 138141244051845670554425)
                  ·
                    rfl

theorem cell23_2421262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 2, 5].length) (baseStart_2421262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421262 prefixEnd_2421262 := by exact prefixLift 2421262
  have htrace : WordTrace (prefixWord ++ tailWord_2421262) baseStart_2421262 baseEnd_2421262 := by
    simpa [prefixWord, tailWord_2421262, baseEnd_2421262] using wordTrace_append hprefix tailTrace_2421262
  have hstable : (prefixWord ++ tailWord_2421262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421262).length < 2 ^ (prefixWord ++ tailWord_2421262).sum := by decide
  have hdescent : baseEnd_2421262 < baseStart_2421262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421291 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6]
def baseStart_2421291 : Nat := 118140960795 + 2421291 * 2 ^ 59
def prefixEnd_2421291 : Nat := 4983230072969 + 3 ^ 40 * 2421291 * 2
def baseEnd_2421291 : Nat := 1243286087405591421527191

theorem tailTrace_2421291 : CollatzResearch.WordTrace tailWord_2421291 prefixEnd_2421291 1243286087405591421527191 := by
  unfold tailWord_2421291
  simp only [CollatzResearch.WordTrace]
  refine ⟨88311737871083705425615727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58874491914055803617077151 88311737871083705425615727)
  ·
    refine ⟨132467606806625558138423591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88311737871083705425615727 132467606806625558138423591)
    ·
      refine ⟨198701410209938337207635387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132467606806625558138423591 198701410209938337207635387)
      ·
        refine ⟨298052115314907505811453081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198701410209938337207635387 298052115314907505811453081)
        ·
          refine ⟨223539086486180629358589811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298052115314907505811453081 223539086486180629358589811)
          ·
            refine ⟨335308629729270944037884717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223539086486180629358589811 335308629729270944037884717)
            ·
              refine ⟨125740736148476604014206769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335308629729270944037884717 125740736148476604014206769)
              ·
                refine ⟨94305552111357453010655077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125740736148476604014206769 94305552111357453010655077)
                ·
                  refine ⟨17682291020879522439497827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94305552111357453010655077 17682291020879522439497827)
                  ·
                    refine ⟨26523436531319283659246741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17682291020879522439497827 26523436531319283659246741)
                    ·
                      refine ⟨1243286087405591421527191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26523436531319283659246741 1243286087405591421527191)
                      ·
                        rfl

theorem cell23_2421291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 6].length) (baseStart_2421291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421291 prefixEnd_2421291 := by exact prefixLift 2421291
  have htrace : WordTrace (prefixWord ++ tailWord_2421291) baseStart_2421291 baseEnd_2421291 := by
    simpa [prefixWord, tailWord_2421291, baseEnd_2421291] using wordTrace_append hprefix tailTrace_2421291
  have hstable : (prefixWord ++ tailWord_2421291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421291).length < 2 ^ (prefixWord ++ tailWord_2421291).sum := by decide
  have hdescent : baseEnd_2421291 < baseStart_2421291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421308 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2421308 : Nat := 118140960795 + 2421308 * 2 ^ 59
def prefixEnd_2421308 : Nat := 4983230072969 + 3 ^ 40 * 2421308 * 2
def baseEnd_2421308 : Nat := 1243294816576717855014613

theorem tailTrace_2421308 : CollatzResearch.WordTrace tailWord_2421308 prefixEnd_2421308 1243294816576717855014613 := by
  unfold tailWord_2421308
  simp only [CollatzResearch.WordTrace]
  refine ⟨44156178956011058664492289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58874905274681411552656385 44156178956011058664492289)
  ·
    refine ⟨33117134217008293998369217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44156178956011058664492289 33117134217008293998369217)
    ·
      refine ⟨24837850662756220498776913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33117134217008293998369217 24837850662756220498776913)
      ·
        refine ⟨18628387997067165374082685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24837850662756220498776913 18628387997067165374082685)
        ·
          refine ⟨6985645498900187015281007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18628387997067165374082685 6985645498900187015281007)
          ·
            refine ⟨10478468248350280522921511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6985645498900187015281007 10478468248350280522921511)
            ·
              refine ⟨15717702372525420784382267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10478468248350280522921511 15717702372525420784382267)
              ·
                refine ⟨23576553558788131176573401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15717702372525420784382267 23576553558788131176573401)
                ·
                  refine ⟨17682415169091098382430051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23576553558788131176573401 17682415169091098382430051)
                  ·
                    refine ⟨26523622753636647573645077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17682415169091098382430051 26523622753636647573645077)
                    ·
                      refine ⟨1243294816576717855014613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26523622753636647573645077 1243294816576717855014613)
                      ·
                        rfl

theorem cell23_2421308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2421308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421308 prefixEnd_2421308 := by exact prefixLift 2421308
  have htrace : WordTrace (prefixWord ++ tailWord_2421308) baseStart_2421308 baseEnd_2421308 := by
    simpa [prefixWord, tailWord_2421308, baseEnd_2421308] using wordTrace_append hprefix tailTrace_2421308
  have hstable : (prefixWord ++ tailWord_2421308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421308).length < 2 ^ (prefixWord ++ tailWord_2421308).sum := by decide
  have hdescent : baseEnd_2421308 < baseStart_2421308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421322 : List Nat := [3, 1, 2, 1, 1, 4, 2, 4, 1, 4]
def baseStart_2421322 : Nat := 118140960795 + 2421322 * 2 ^ 59
def prefixEnd_2421322 : Nat := 4983230072969 + 3 ^ 40 * 2421322 * 2
def baseEnd_2421322 : Nat := 414434001768626933413183

theorem tailTrace_2421322 : CollatzResearch.WordTrace tailWord_2421322 prefixEnd_2421322 414434001768626933413183 := by
  unfold tailWord_2421322
  simp only [CollatzResearch.WordTrace]
  refine ⟨22078217133492849429998555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58875245689314265146662813 22078217133492849429998555)
  ·
    refine ⟨33117325700239274144997833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22078217133492849429998555 33117325700239274144997833)
    ·
      refine ⟨24837994275179455608748375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33117325700239274144997833 24837994275179455608748375)
      ·
        refine ⟨37256991412769183413122563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24837994275179455608748375 37256991412769183413122563)
        ·
          refine ⟨55885487119153775119683845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37256991412769183413122563 55885487119153775119683845)
          ·
            refine ⟨10478528834841332834940721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55885487119153775119683845 10478528834841332834940721)
            ·
              refine ⟨7858896626130999626205541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10478528834841332834940721 7858896626130999626205541)
              ·
                refine ⟨1473543117399562429913539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7858896626130999626205541 1473543117399562429913539)
                ·
                  refine ⟨2210314676099343644870309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473543117399562429913539 2210314676099343644870309)
                  ·
                    refine ⟨414434001768626933413183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210314676099343644870309 414434001768626933413183)
                    ·
                      rfl

theorem cell23_2421322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_2421322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421322 prefixEnd_2421322 := by exact prefixLift 2421322
  have htrace : WordTrace (prefixWord ++ tailWord_2421322) baseStart_2421322 baseEnd_2421322 := by
    simpa [prefixWord, tailWord_2421322, baseEnd_2421322] using wordTrace_append hprefix tailTrace_2421322
  have hstable : (prefixWord ++ tailWord_2421322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421322).length < 2 ^ (prefixWord ++ tailWord_2421322).sum := by decide
  have hdescent : baseEnd_2421322 < baseStart_2421322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421335 : List Nat := [1, 1, 3, 2, 2, 2, 5, 1, 6]
def baseStart_2421335 : Nat := 118140960795 + 2421335 * 2 ^ 59
def prefixEnd_2421335 : Nat := 4983230072969 + 3 ^ 40 * 2421335 * 2
def baseEnd_2421335 : Nat := 138145408950487694375221

theorem tailTrace_2421335 : CollatzResearch.WordTrace tailWord_2421335 prefixEnd_2421335 138145408950487694375221 := by
  unfold tailWord_2421335
  simp only [CollatzResearch.WordTrace]
  refine ⟨88313342682924300940217459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58875561788616200626811639 88313342682924300940217459)
  ·
    refine ⟨132470014024386451410326189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88313342682924300940217459 132470014024386451410326189)
    ·
      refine ⟨49676255259144919278872321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132470014024386451410326189 49676255259144919278872321)
      ·
        refine ⟨37257191444358689459154241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49676255259144919278872321 37257191444358689459154241)
        ·
          refine ⟨27942893583269017094365681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37257191444358689459154241 27942893583269017094365681)
          ·
            refine ⟨20957170187451762820774261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27942893583269017094365681 20957170187451762820774261)
            ·
              refine ⟨1964734705073602764447587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20957170187451762820774261 1964734705073602764447587)
              ·
                refine ⟨2947102057610404146671381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964734705073602764447587 2947102057610404146671381)
                ·
                  refine ⟨138145408950487694375221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2947102057610404146671381 138145408950487694375221)
                  ·
                    rfl

theorem cell23_2421335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 5, 1, 6].length) (baseStart_2421335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421335 prefixEnd_2421335 := by exact prefixLift 2421335
  have htrace : WordTrace (prefixWord ++ tailWord_2421335) baseStart_2421335 baseEnd_2421335 := by
    simpa [prefixWord, tailWord_2421335, baseEnd_2421335] using wordTrace_append hprefix tailTrace_2421335
  have hstable : (prefixWord ++ tailWord_2421335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421335).length < 2 ^ (prefixWord ++ tailWord_2421335).sum := by decide
  have hdescent : baseEnd_2421335 < baseStart_2421335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421388 : List Nat := [2, 2, 1, 2, 1, 1, 2, 3, 3, 1, 5]
def baseStart_2421388 : Nat := 118140960795 + 2421388 * 2 ^ 59
def prefixEnd_2421388 : Nat := 4983230072969 + 3 ^ 40 * 2421388 * 2
def baseEnd_2421388 : Nat := 1243335895029077542014245

theorem tailTrace_2421388 : CollatzResearch.WordTrace tailWord_2421388 prefixEnd_2421388 1243335895029077542014245 := by
  unfold tailWord_2421388
  simp only [CollatzResearch.WordTrace]
  refine ⟨44157637875866145495948409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58876850501154860661264545 44157637875866145495948409)
  ·
    refine ⟨33118228406899609121961307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44157637875866145495948409 33118228406899609121961307)
    ·
      refine ⟨49677342610349413682941961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33118228406899609121961307 49677342610349413682941961)
      ·
        refine ⟨37258006957762060262206471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49677342610349413682941961 37258006957762060262206471)
        ·
          refine ⟨55887010436643090393309707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37258006957762060262206471 55887010436643090393309707)
          ·
            refine ⟨83830515654964635589964561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55887010436643090393309707 83830515654964635589964561)
            ·
              refine ⟨62872886741223476692473421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83830515654964635589964561 62872886741223476692473421)
              ·
                refine ⟨23577332527958803759677533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62872886741223476692473421 23577332527958803759677533)
                ·
                  refine ⟨8841499697984551409879075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23577332527958803759677533 8841499697984551409879075)
                  ·
                    refine ⟨13262249546976827114818613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8841499697984551409879075 13262249546976827114818613)
                    ·
                      refine ⟨1243335895029077542014245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13262249546976827114818613 1243335895029077542014245)
                      ·
                        rfl

theorem cell23_2421388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_2421388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421388 prefixEnd_2421388 := by exact prefixLift 2421388
  have htrace : WordTrace (prefixWord ++ tailWord_2421388) baseStart_2421388 baseEnd_2421388 := by
    simpa [prefixWord, tailWord_2421388, baseEnd_2421388] using wordTrace_append hprefix tailTrace_2421388
  have hstable : (prefixWord ++ tailWord_2421388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421388).length < 2 ^ (prefixWord ++ tailWord_2421388).sum := by decide
  have hdescent : baseEnd_2421388 < baseStart_2421388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421395 : List Nat := [1, 1, 1, 2, 1, 2, 2, 7, 2, 4]
def baseStart_2421395 : Nat := 118140960795 + 2421395 * 2 ^ 59
def prefixEnd_2421395 : Nat := 4983230072969 + 3 ^ 40 * 2421395 * 2
def baseEnd_2421395 : Nat := 414446496464553004875571

theorem tailTrace_2421395 : CollatzResearch.WordTrace tailWord_2421395 prefixEnd_2421395 414446496464553004875571 := by
  unfold tailWord_2421395
  simp only [CollatzResearch.WordTrace]
  refine ⟨88315531062706931187401639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58877020708471287458267759 88315531062706931187401639)
  ·
    refine ⟨132473296594060396781102459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88315531062706931187401639 132473296594060396781102459)
    ·
      refine ⟨198709944891090595171653689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132473296594060396781102459 198709944891090595171653689)
      ·
        refine ⟨149032458668317946378740267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198709944891090595171653689 149032458668317946378740267)
        ·
          refine ⟨223548688002476919568110401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149032458668317946378740267 223548688002476919568110401)
          ·
            refine ⟨167661516001857689676082801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223548688002476919568110401 167661516001857689676082801)
            ·
              refine ⟨125746137001393267257062101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167661516001857689676082801 125746137001393267257062101)
              ·
                refine ⟨2947175085970154701337393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125746137001393267257062101 2947175085970154701337393)
                ·
                  refine ⟨2210381314477616026003045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947175085970154701337393 2210381314477616026003045)
                  ·
                    refine ⟨414446496464553004875571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210381314477616026003045 414446496464553004875571)
                    ·
                      rfl

theorem cell23_2421395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7, 2, 4].length) (baseStart_2421395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421395 prefixEnd_2421395 := by exact prefixLift 2421395
  have htrace : WordTrace (prefixWord ++ tailWord_2421395) baseStart_2421395 baseEnd_2421395 := by
    simpa [prefixWord, tailWord_2421395, baseEnd_2421395] using wordTrace_append hprefix tailTrace_2421395
  have hstable : (prefixWord ++ tailWord_2421395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421395).length < 2 ^ (prefixWord ++ tailWord_2421395).sum := by decide
  have hdescent : baseEnd_2421395 < baseStart_2421395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421425 : List Nat := [1, 2, 2, 6, 1, 11]
def baseStart_2421425 : Nat := 118140960795 + 2421425 * 2 ^ 59
def prefixEnd_2421425 : Nat := 4983230072969 + 3 ^ 40 * 2421425 * 2
def baseEnd_2421425 : Nat := 5116686805816024268525

theorem tailTrace_2421425 : CollatzResearch.WordTrace tailWord_2421425 prefixEnd_2421425 5116686805816024268525 := by
  unfold tailWord_2421425
  simp only [CollatzResearch.WordTrace]
  refine ⟨88316625252598246310993729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58877750168398830873995819 88316625252598246310993729)
  ·
    refine ⟨66237468939448684733245297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88316625252598246310993729 66237468939448684733245297)
    ·
      refine ⟨49678101704586513549933973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66237468939448684733245297 49678101704586513549933973)
      ·
        refine ⟨2328661017402492822653155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49678101704586513549933973 2328661017402492822653155)
        ·
          refine ⟨3492991526103739233979733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328661017402492822653155 3492991526103739233979733)
          ·
            refine ⟨5116686805816024268525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 3492991526103739233979733 5116686805816024268525)
            ·
              rfl

theorem cell23_2421425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 11].length) (baseStart_2421425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421425 prefixEnd_2421425 := by exact prefixLift 2421425
  have htrace : WordTrace (prefixWord ++ tailWord_2421425) baseStart_2421425 baseEnd_2421425 := by
    simpa [prefixWord, tailWord_2421425, baseEnd_2421425] using wordTrace_append hprefix tailTrace_2421425
  have hstable : (prefixWord ++ tailWord_2421425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421425).length < 2 ^ (prefixWord ++ tailWord_2421425).sum := by decide
  have hdescent : baseEnd_2421425 < baseStart_2421425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421429 : List Nat := [1, 3, 3, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2421429 : Nat := 118140960795 + 2421429 * 2 ^ 59
def prefixEnd_2421429 : Nat := 4983230072969 + 3 ^ 40 * 2421429 * 2
def baseEnd_2421429 : Nat := 414452315911970627200519

theorem tailTrace_2421429 : CollatzResearch.WordTrace tailWord_2421429 prefixEnd_2421429 414452315911970627200519 := by
  unfold tailWord_2421429
  simp only [CollatzResearch.WordTrace]
  refine ⟨88316771144583754994139341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58877847429722503329426227 88316771144583754994139341)
  ·
    refine ⟨33118789179218908122802253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88316771144583754994139341 33118789179218908122802253)
    ·
      refine ⟨12419545942207090546050845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33118789179218908122802253 12419545942207090546050845)
      ·
        refine ⟨4657329728327658954769067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12419545942207090546050845 4657329728327658954769067)
        ·
          refine ⟨6985994592491488432153601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657329728327658954769067 6985994592491488432153601)
          ·
            refine ⟨5239495944368616324115201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6985994592491488432153601 5239495944368616324115201)
            ·
              refine ⟨3929621958276462243086401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5239495944368616324115201 3929621958276462243086401)
              ·
                refine ⟨2947216468707346682314801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929621958276462243086401 2947216468707346682314801)
                ·
                  refine ⟨2210412351530510011736101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947216468707346682314801 2210412351530510011736101)
                  ·
                    refine ⟨414452315911970627200519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210412351530510011736101 414452315911970627200519)
                    ·
                      rfl

theorem cell23_2421429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2421429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421429 prefixEnd_2421429 := by exact prefixLift 2421429
  have htrace : WordTrace (prefixWord ++ tailWord_2421429) baseStart_2421429 baseEnd_2421429 := by
    simpa [prefixWord, tailWord_2421429, baseEnd_2421429] using wordTrace_append hprefix tailTrace_2421429
  have hstable : (prefixWord ++ tailWord_2421429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421429).length < 2 ^ (prefixWord ++ tailWord_2421429).sum := by decide
  have hdescent : baseEnd_2421429 < baseStart_2421429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421436 : List Nat := [2, 2, 2, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_2421436 : Nat := 118140960795 + 2421436 * 2 ^ 59
def prefixEnd_2421436 : Nat := 4983230072969 + 3 ^ 40 * 2421436 * 2
def baseEnd_2421436 : Nat := 1243360542100493354214025

theorem tailTrace_2421436 : CollatzResearch.WordTrace tailWord_2421436 prefixEnd_2421436 1243360542100493354214025 := by
  unfold tailWord_2421436
  simp only [CollatzResearch.WordTrace]
  refine ⟨44158513227779197594822081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58878017637038930126429441 44158513227779197594822081)
  ·
    refine ⟨33118884920834398196116561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44158513227779197594822081 33118884920834398196116561)
    ·
      refine ⟨24839163690625798647087421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33118884920834398196116561 24839163690625798647087421)
      ·
        refine ⟨9314686383984674492657783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24839163690625798647087421 9314686383984674492657783)
        ·
          refine ⟨13972029575977011738986675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9314686383984674492657783 13972029575977011738986675)
          ·
            refine ⟨20958044363965517608480013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13972029575977011738986675 20958044363965517608480013)
            ·
              refine ⟨7859266636487069103180005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20958044363965517608480013 7859266636487069103180005)
              ·
                refine ⟨1473612494341325456846251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7859266636487069103180005 1473612494341325456846251)
                ·
                  refine ⟨2210418741511988185269377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1473612494341325456846251 2210418741511988185269377)
                  ·
                    refine ⟨1657814056133991138952033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2210418741511988185269377 1657814056133991138952033)
                    ·
                      refine ⟨1243360542100493354214025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657814056133991138952033 1243360542100493354214025)
                      ·
                        rfl

theorem cell23_2421436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_2421436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421436 prefixEnd_2421436 := by exact prefixLift 2421436
  have htrace : WordTrace (prefixWord ++ tailWord_2421436) baseStart_2421436 baseEnd_2421436 := by
    simpa [prefixWord, tailWord_2421436, baseEnd_2421436] using wordTrace_append hprefix tailTrace_2421436
  have hstable : (prefixWord ++ tailWord_2421436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421436).length < 2 ^ (prefixWord ++ tailWord_2421436).sum := by decide
  have hdescent : baseEnd_2421436 < baseStart_2421436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421445 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 1, 9, 2]
def baseStart_2421445 : Nat := 118140960795 + 2421445 * 2 ^ 59
def prefixEnd_2421445 : Nat := 4983230072969 + 3 ^ 40 * 2421445 * 2
def baseEnd_2421445 : Nat := 1243365163426383819001483

theorem tailTrace_2421445 : CollatzResearch.WordTrace tailWord_2421445 prefixEnd_2421445 1243365163426383819001483 := by
  unfold tailWord_2421445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88317354712525789726721789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58878236475017193151147859 88317354712525789726721789)
  ·
    refine ⟨33119008017197171147520671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88317354712525789726721789 33119008017197171147520671)
    ·
      refine ⟨49678512025795756721281007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33119008017197171147520671 49678512025795756721281007)
      ·
        refine ⟨74517768038693635081921511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49678512025795756721281007 74517768038693635081921511)
        ·
          refine ⟨111776652058040452622882267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74517768038693635081921511 111776652058040452622882267)
          ·
            refine ⟨167664978087060678934323401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111776652058040452622882267 167664978087060678934323401)
            ·
              refine ⟨125748733565295509200742551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167664978087060678934323401 125748733565295509200742551)
              ·
                refine ⟨188623100347943263801113827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125748733565295509200742551 188623100347943263801113827)
                ·
                  refine ⟨282934650521914895701670741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188623100347943263801113827 282934650521914895701670741)
                  ·
                    refine ⟨1657820217901845092001977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 282934650521914895701670741 1657820217901845092001977)
                    ·
                      refine ⟨1243365163426383819001483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657820217901845092001977 1243365163426383819001483)
                      ·
                        rfl

theorem cell23_2421445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 9, 2].length) (baseStart_2421445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421445 prefixEnd_2421445 := by exact prefixLift 2421445
  have htrace : WordTrace (prefixWord ++ tailWord_2421445) baseStart_2421445 baseEnd_2421445 := by
    simpa [prefixWord, tailWord_2421445, baseEnd_2421445] using wordTrace_append hprefix tailTrace_2421445
  have hstable : (prefixWord ++ tailWord_2421445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421445).length < 2 ^ (prefixWord ++ tailWord_2421445).sum := by decide
  have hdescent : baseEnd_2421445 < baseStart_2421445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421446 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2421446 : Nat := 118140960795 + 2421446 * 2 ^ 59
def prefixEnd_2421446 : Nat := 4983230072969 + 3 ^ 40 * 2421446 * 2
def baseEnd_2421446 : Nat := 414455225635679438362993

theorem tailTrace_2421446 : CollatzResearch.WordTrace tailWord_2421446 prefixEnd_2421446 414455225635679438362993 := by
  unfold tailWord_2421446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2759918474547567715547131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58878260790348111265005461 2759918474547567715547131)
  ·
    refine ⟨4139877711821351573320697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2759918474547567715547131 4139877711821351573320697)
    ·
      refine ⟨3104908283866013679990523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4139877711821351573320697 3104908283866013679990523)
      ·
        refine ⟨4657362425799020519985785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104908283866013679990523 4657362425799020519985785)
        ·
          refine ⟨3493021819349265389989339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657362425799020519985785 3493021819349265389989339)
          ·
            refine ⟨5239532729023898084984009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493021819349265389989339 5239532729023898084984009)
            ·
              refine ⟨3929649546767923563738007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5239532729023898084984009 3929649546767923563738007)
              ·
                refine ⟨5894474320151885345607011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3929649546767923563738007 5894474320151885345607011)
                ·
                  refine ⟨8841711480227828018410517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5894474320151885345607011 8841711480227828018410517)
                  ·
                    refine ⟨414455225635679438362993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8841711480227828018410517 414455225635679438362993)
                    ·
                      rfl

theorem cell23_2421446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2421446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421446 prefixEnd_2421446 := by exact prefixLift 2421446
  have htrace : WordTrace (prefixWord ++ tailWord_2421446) baseStart_2421446 baseEnd_2421446 := by
    simpa [prefixWord, tailWord_2421446, baseEnd_2421446] using wordTrace_append hprefix tailTrace_2421446
  have hstable : (prefixWord ++ tailWord_2421446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421446).length < 2 ^ (prefixWord ++ tailWord_2421446).sum := by decide
  have hdescent : baseEnd_2421446 < baseStart_2421446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421452 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 1, 3, 3]
def baseStart_2421452 : Nat := 118140960795 + 2421452 * 2 ^ 59
def prefixEnd_2421452 : Nat := 4983230072969 + 3 ^ 40 * 2421452 * 2
def baseEnd_2421452 : Nat := 1243368757790965291613951

theorem tailTrace_2421452 : CollatzResearch.WordTrace tailWord_2421452 prefixEnd_2421452 1243368757790965291613951 := by
  unfold tailWord_2421452
  simp only [CollatzResearch.WordTrace]
  refine ⟨44158805011750214961113305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58878406682333619948151073 44158805011750214961113305)
  ·
    refine ⟨33119103758812661220834979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44158805011750214961113305 33119103758812661220834979)
    ·
      refine ⟨49678655638218991831252469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33119103758812661220834979 49678655638218991831252469)
      ·
        refine ⟨4657373966083030484179919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49678655638218991831252469 4657373966083030484179919)
        ·
          refine ⟨6986060949124545726269879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4657373966083030484179919 6986060949124545726269879)
          ·
            refine ⟨10479091423686818589404819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986060949124545726269879 10479091423686818589404819)
            ·
              refine ⟨15718637135530227884107229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10479091423686818589404819 15718637135530227884107229)
              ·
                refine ⟨5894488925823835456540211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15718637135530227884107229 5894488925823835456540211)
                ·
                  refine ⟨8841733388735753184810317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5894488925823835456540211 8841733388735753184810317)
                  ·
                    refine ⟨3315650020775907444303869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8841733388735753184810317 3315650020775907444303869)
                    ·
                      refine ⟨1243368757790965291613951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3315650020775907444303869 1243368757790965291613951)
                      ·
                        rfl

theorem cell23_2421452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_2421452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421452 prefixEnd_2421452 := by exact prefixLift 2421452
  have htrace : WordTrace (prefixWord ++ tailWord_2421452) baseStart_2421452 baseEnd_2421452 := by
    simpa [prefixWord, tailWord_2421452, baseEnd_2421452] using wordTrace_append hprefix tailTrace_2421452
  have hstable : (prefixWord ++ tailWord_2421452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421452).length < 2 ^ (prefixWord ++ tailWord_2421452).sum := by decide
  have hdescent : baseEnd_2421452 < baseStart_2421452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421453 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 3, 2, 2]
def baseStart_2421453 : Nat := 118140960795 + 2421453 * 2 ^ 59
def prefixEnd_2421453 : Nat := 4983230072969 + 3 ^ 40 * 2421453 * 2
def baseEnd_2421453 : Nat := 1243369271271619787701447

theorem tailTrace_2421453 : CollatzResearch.WordTrace tailWord_2421453 prefixEnd_2421453 1243369271271619787701447 := by
  unfold tailWord_2421453
  simp only [CollatzResearch.WordTrace]
  refine ⟨88317646496496807093013013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58878430997664538062008675 88317646496496807093013013)
  ·
    refine ⟨4139889679523287832484985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 88317646496496807093013013 4139889679523287832484985)
    ·
      refine ⟨3104917259642465874363739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4139889679523287832484985 3104917259642465874363739)
      ·
        refine ⟨4657375889463698811545609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104917259642465874363739 4657375889463698811545609)
        ·
          refine ⟨3493031917097774108659207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657375889463698811545609 3493031917097774108659207)
          ·
            refine ⟨5239547875646661162988811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493031917097774108659207 5239547875646661162988811)
            ·
              refine ⟨7859321813469991744483217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5239547875646661162988811 7859321813469991744483217)
              ·
                refine ⟨5894491360102493808362413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7859321813469991744483217 5894491360102493808362413)
                ·
                  refine ⟨2210434260038435178135905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5894491360102493808362413 2210434260038435178135905)
                  ·
                    refine ⟨1657825695028826383601929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2210434260038435178135905 1657825695028826383601929)
                    ·
                      refine ⟨1243369271271619787701447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657825695028826383601929 1243369271271619787701447)
                      ·
                        rfl

theorem cell23_2421453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_2421453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421453 prefixEnd_2421453 := by exact prefixLift 2421453
  have htrace : WordTrace (prefixWord ++ tailWord_2421453) baseStart_2421453 baseEnd_2421453 := by
    simpa [prefixWord, tailWord_2421453, baseEnd_2421453] using wordTrace_append hprefix tailTrace_2421453
  have hstable : (prefixWord ++ tailWord_2421453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421453).length < 2 ^ (prefixWord ++ tailWord_2421453).sum := by decide
  have hdescent : baseEnd_2421453 < baseStart_2421453 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421485 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2421485 : Nat := 118140960795 + 2421485 * 2 ^ 59
def prefixEnd_2421485 : Nat := 4983230072969 + 3 ^ 40 * 2421485 * 2
def baseEnd_2421485 : Nat := 414461900884187887500433

theorem tailTrace_2421485 : CollatzResearch.WordTrace tailWord_2421485 prefixEnd_2421485 414461900884187887500433 := by
  unfold tailWord_2421485
  simp only [CollatzResearch.WordTrace]
  refine ⟨88318813632380876558177909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58879209088253917705451939 88318813632380876558177909)
  ·
    refine ⟨8279888778035707177329179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88318813632380876558177909 8279888778035707177329179)
    ·
      refine ⟨12419833167053560765993769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8279888778035707177329179 12419833167053560765993769)
      ·
        refine ⟨9314874875290170574495327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12419833167053560765993769 9314874875290170574495327)
        ·
          refine ⟨13972312312935255861742991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9314874875290170574495327 13972312312935255861742991)
          ·
            refine ⟨20958468469402883792614487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13972312312935255861742991 20958468469402883792614487)
            ·
              refine ⟨31437702704104325688921731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20958468469402883792614487 31437702704104325688921731)
              ·
                refine ⟨47156554056156488533382597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31437702704104325688921731 47156554056156488533382597)
                ·
                  refine ⟨8841853885529341600009237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47156554056156488533382597 8841853885529341600009237)
                  ·
                    refine ⟨414461900884187887500433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8841853885529341600009237 414461900884187887500433)
                    ·
                      rfl

theorem cell23_2421485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2421485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421485 prefixEnd_2421485 := by exact prefixLift 2421485
  have htrace : WordTrace (prefixWord ++ tailWord_2421485) baseStart_2421485 baseEnd_2421485 := by
    simpa [prefixWord, tailWord_2421485, baseEnd_2421485] using wordTrace_append hprefix tailTrace_2421485
  have hstable : (prefixWord ++ tailWord_2421485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421485).length < 2 ^ (prefixWord ++ tailWord_2421485).sum := by decide
  have hdescent : baseEnd_2421485 < baseStart_2421485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421486 : List Nat := [4, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3]
def baseStart_2421486 : Nat := 118140960795 + 2421486 * 2 ^ 59
def prefixEnd_2421486 : Nat := 4983230072969 + 3 ^ 40 * 2421486 * 2
def baseEnd_2421486 : Nat := 1243386216133218158588795

theorem tailTrace_2421486 : CollatzResearch.WordTrace tailWord_2421486 prefixEnd_2421486 1243386216133218158588795 := by
  unfold tailWord_2421486
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039856263172156716120539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58879233403584835819309541 11039856263172156716120539)
  ·
    refine ⟨16559784394758235074180809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11039856263172156716120539 16559784394758235074180809)
    ·
      refine ⟨12419838296068676305635607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16559784394758235074180809 12419838296068676305635607)
      ·
        refine ⟨18629757444103014458453411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12419838296068676305635607 18629757444103014458453411)
        ·
          refine ⟨27944636166154521687680117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18629757444103014458453411 27944636166154521687680117)
          ·
            refine ⟨2619809640576986408220011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27944636166154521687680117 2619809640576986408220011)
            ·
              refine ⟨3929714460865479612330017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2619809640576986408220011 3929714460865479612330017)
              ·
                refine ⟨2947285845649109709247513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3929714460865479612330017 2947285845649109709247513)
                ·
                  refine ⟨2210464384236832281935635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947285845649109709247513 2210464384236832281935635)
                  ·
                    refine ⟨3315696576355248422903453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2210464384236832281935635 3315696576355248422903453)
                    ·
                      refine ⟨1243386216133218158588795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3315696576355248422903453 1243386216133218158588795)
                      ·
                        rfl

theorem cell23_2421486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_2421486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421486 prefixEnd_2421486 := by exact prefixLift 2421486
  have htrace : WordTrace (prefixWord ++ tailWord_2421486) baseStart_2421486 baseEnd_2421486 := by
    simpa [prefixWord, tailWord_2421486, baseEnd_2421486] using wordTrace_append hprefix tailTrace_2421486
  have hstable : (prefixWord ++ tailWord_2421486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421486).length < 2 ^ (prefixWord ++ tailWord_2421486).sum := by decide
  have hdescent : baseEnd_2421486 < baseStart_2421486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421502 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2421502 : Nat := 118140960795 + 2421502 * 2 ^ 59
def prefixEnd_2421502 : Nat := 4983230072969 + 3 ^ 40 * 2421502 * 2
def baseEnd_2421502 : Nat := 414464810607896698662907

theorem tailTrace_2421502 : CollatzResearch.WordTrace tailWord_2421502 prefixEnd_2421502 414464810607896698662907 := by
  unfold tailWord_2421502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11039929209164911057693345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58879622448879525641031173 11039929209164911057693345)
  ·
    refine ⟨8279946906873683293270009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11039929209164911057693345 8279946906873683293270009)
    ·
      refine ⟨6209960180155262469952507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8279946906873683293270009 6209960180155262469952507)
      ·
        refine ⟨9314940270232893704928761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209960180155262469952507 9314940270232893704928761)
        ·
          refine ⟨6986205202674670278696571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9314940270232893704928761 6986205202674670278696571)
          ·
            refine ⟨10479307804012005418044857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986205202674670278696571 10479307804012005418044857)
            ·
              refine ⟨7859480853009004063533643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10479307804012005418044857 7859480853009004063533643)
              ·
                refine ⟨11789221279513506095300465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7859480853009004063533643 11789221279513506095300465)
                ·
                  refine ⟨8841915959635129571475349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11789221279513506095300465 8841915959635129571475349)
                  ·
                    refine ⟨414464810607896698662907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8841915959635129571475349 414464810607896698662907)
                    ·
                      rfl

theorem cell23_2421502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2421502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421502 prefixEnd_2421502 := by exact prefixLift 2421502
  have htrace : WordTrace (prefixWord ++ tailWord_2421502) baseStart_2421502 baseEnd_2421502 := by
    simpa [prefixWord, tailWord_2421502, baseEnd_2421502] using wordTrace_append hprefix tailTrace_2421502
  have hstable : (prefixWord ++ tailWord_2421502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421502).length < 2 ^ (prefixWord ++ tailWord_2421502).sum := by decide
  have hdescent : baseEnd_2421502 < baseStart_2421502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421509 : List Nat := [1, 3, 1, 1, 2, 1, 1, 7, 2, 2, 2]
def baseStart_2421509 : Nat := 118140960795 + 2421509 * 2 ^ 59
def prefixEnd_2421509 : Nat := 4983230072969 + 3 ^ 40 * 2421509 * 2
def baseEnd_2421509 : Nat := 1243398026188271568601189

theorem tailTrace_2421509 : CollatzResearch.WordTrace tailWord_2421509 prefixEnd_2421509 1243398026188271568601189 := by
  unfold tailWord_2421509
  simp only [CollatzResearch.WordTrace]
  refine ⟨88319688984293928657051581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58879792656195952438034387 88319688984293928657051581)
  ·
    refine ⟨33119883369110223246394343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88319688984293928657051581 33119883369110223246394343)
    ·
      refine ⟨49679825053665334869591515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33119883369110223246394343 49679825053665334869591515)
      ·
        refine ⟨74519737580498002304387273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49679825053665334869591515 74519737580498002304387273)
        ·
          refine ⟨55889803185373501728290455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74519737580498002304387273 55889803185373501728290455)
          ·
            refine ⟨83834704778060252592435683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55889803185373501728290455 83834704778060252592435683)
            ·
              refine ⟨125752057167090378888653525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83834704778060252592435683 125752057167090378888653525)
              ·
                refine ⟨2947313839853680755202817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 125752057167090378888653525 2947313839853680755202817)
                ·
                  refine ⟨2210485379890260566402113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947313839853680755202817 2210485379890260566402113)
                  ·
                    refine ⟨1657864034917695424801585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2210485379890260566402113 1657864034917695424801585)
                    ·
                      refine ⟨1243398026188271568601189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1657864034917695424801585 1243398026188271568601189)
                      ·
                        rfl

theorem cell23_2421509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 7, 2, 2, 2].length) (baseStart_2421509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421509 prefixEnd_2421509 := by exact prefixLift 2421509
  have htrace : WordTrace (prefixWord ++ tailWord_2421509) baseStart_2421509 baseEnd_2421509 := by
    simpa [prefixWord, tailWord_2421509, baseEnd_2421509] using wordTrace_append hprefix tailTrace_2421509
  have hstable : (prefixWord ++ tailWord_2421509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421509).length < 2 ^ (prefixWord ++ tailWord_2421509).sum := by decide
  have hdescent : baseEnd_2421509 < baseStart_2421509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421545 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 2, 5]
def baseStart_2421545 : Nat := 118140960795 + 2421545 * 2 ^ 59
def prefixEnd_2421545 : Nat := 4983230072969 + 3 ^ 40 * 2421545 * 2
def baseEnd_2421545 : Nat := 414472170497277809250341

theorem tailTrace_2421545 : CollatzResearch.WordTrace tailWord_2421545 prefixEnd_2421545 414472170497277809250341 := by
  unfold tailWord_2421545
  simp only [CollatzResearch.WordTrace]
  refine ⟨88321002012163506805362089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58880668008109004536908059 88321002012163506805362089)
  ·
    refine ⟨66240751509122630104021567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88321002012163506805362089 66240751509122630104021567)
    ·
      refine ⟨99361127263683945156032351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66240751509122630104021567 99361127263683945156032351)
      ·
        refine ⟨149041690895525917734048527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99361127263683945156032351 149041690895525917734048527)
        ·
          refine ⟨223562536343288876601072791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149041690895525917734048527 223562536343288876601072791)
          ·
            refine ⟨335343804514933314901609187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223562536343288876601072791 335343804514933314901609187)
            ·
              refine ⟨503015706772399972352413781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335343804514933314901609187 503015706772399972352413781)
              ·
                refine ⟨5894715313739062176004849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 503015706772399972352413781 5894715313739062176004849)
                ·
                  refine ⟨4421036485304296632003637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5894715313739062176004849 4421036485304296632003637)
                  ·
                    refine ⟨414472170497277809250341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4421036485304296632003637 414472170497277809250341)
                    ·
                      rfl

theorem cell23_2421545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 5].length) (baseStart_2421545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421545 prefixEnd_2421545 := by exact prefixLift 2421545
  have htrace : WordTrace (prefixWord ++ tailWord_2421545) baseStart_2421545 baseEnd_2421545 := by
    simpa [prefixWord, tailWord_2421545, baseEnd_2421545] using wordTrace_append hprefix tailTrace_2421545
  have hstable : (prefixWord ++ tailWord_2421545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421545).length < 2 ^ (prefixWord ++ tailWord_2421545).sum := by decide
  have hdescent : baseEnd_2421545 < baseStart_2421545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421555 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7]
def baseStart_2421555 : Nat := 118140960795 + 2421555 * 2 ^ 59
def prefixEnd_2421555 : Nat := 4983230072969 + 3 ^ 40 * 2421555 * 2
def baseEnd_2421555 : Nat := 1243421646298378388625977

theorem tailTrace_2421555 : CollatzResearch.WordTrace tailWord_2421555 prefixEnd_2421555 1243421646298378388625977 := by
  unfold tailWord_2421555
  simp only [CollatzResearch.WordTrace]
  refine ⟨88321366742127278513226119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58880911161418185675484079 88321366742127278513226119)
  ·
    refine ⟨132482050113190917769839179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88321366742127278513226119 132482050113190917769839179)
    ·
      refine ⟨198723075169786376654758769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132482050113190917769839179 198723075169786376654758769)
      ·
        refine ⟨149042306377339782491069077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198723075169786376654758769 149042306377339782491069077)
        ·
          refine ⟨6986358111437802304268863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 149042306377339782491069077 6986358111437802304268863)
          ·
            refine ⟨10479537167156703456403295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986358111437802304268863 10479537167156703456403295)
            ·
              refine ⟨15719305750735055184604943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10479537167156703456403295 15719305750735055184604943)
              ·
                refine ⟨23578958626102582776907415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15719305750735055184604943 23578958626102582776907415)
                ·
                  refine ⟨35368437939153874165361123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23578958626102582776907415 35368437939153874165361123)
                  ·
                    refine ⟨53052656908730811248041685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35368437939153874165361123 53052656908730811248041685)
                    ·
                      refine ⟨1243421646298378388625977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53052656908730811248041685 1243421646298378388625977)
                      ·
                        rfl

theorem cell23_2421555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 7].length) (baseStart_2421555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421555 prefixEnd_2421555 := by exact prefixLift 2421555
  have htrace : WordTrace (prefixWord ++ tailWord_2421555) baseStart_2421555 baseEnd_2421555 := by
    simpa [prefixWord, tailWord_2421555, baseEnd_2421555] using wordTrace_append hprefix tailTrace_2421555
  have hstable : (prefixWord ++ tailWord_2421555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421555).length < 2 ^ (prefixWord ++ tailWord_2421555).sum := by decide
  have hdescent : baseEnd_2421555 < baseStart_2421555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421605 : List Nat := [1, 3, 1, 3, 1, 1, 2, 3, 8]
def baseStart_2421605 : Nat := 118140960795 + 2421605 * 2 ^ 59
def prefixEnd_2421605 : Nat := 4983230072969 + 3 ^ 40 * 2421605 * 2
def baseEnd_2421605 : Nat := 138160813370122577000083

theorem tailTrace_2421605 : CollatzResearch.WordTrace tailWord_2421605 prefixEnd_2421605 138160813370122577000083 := by
  unfold tailWord_2421605
  simp only [CollatzResearch.WordTrace]
  refine ⟨88323190391946137052546269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58882126927964091368364179 88323190391946137052546269)
  ·
    refine ⟨33121196396979801394704851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88323190391946137052546269 33121196396979801394704851)
    ·
      refine ⟨49681794595469702092057277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33121196396979801394704851 49681794595469702092057277)
      ·
        refine ⟨18630672973301138284521479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49681794595469702092057277 18630672973301138284521479)
        ·
          refine ⟨27946009459951707426782219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18630672973301138284521479 27946009459951707426782219)
          ·
            refine ⟨41919014189927561140173329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27946009459951707426782219 41919014189927561140173329)
            ·
              refine ⟨31439260642445670855129997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41919014189927561140173329 31439260642445670855129997)
              ·
                refine ⟨11789722740917126570673749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31439260642445670855129997 11789722740917126570673749)
                ·
                  refine ⟨138160813370122577000083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11789722740917126570673749 138160813370122577000083)
                  ·
                    rfl

theorem cell23_2421605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 3, 8].length) (baseStart_2421605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421605 prefixEnd_2421605 := by exact prefixLift 2421605
  have htrace : WordTrace (prefixWord ++ tailWord_2421605) baseStart_2421605 baseEnd_2421605 := by
    simpa [prefixWord, tailWord_2421605, baseEnd_2421605] using wordTrace_append hprefix tailTrace_2421605
  have hstable : (prefixWord ++ tailWord_2421605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421605).length < 2 ^ (prefixWord ++ tailWord_2421605).sum := by decide
  have hdescent : baseEnd_2421605 < baseStart_2421605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421666 : List Nat := [3, 3, 1, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2421666 : Nat := 118140960795 + 2421666 * 2 ^ 59
def prefixEnd_2421666 : Nat := 4983230072969 + 3 ^ 40 * 2421666 * 2
def baseEnd_2421666 : Nat := 1243478642651027454337967

theorem tailTrace_2421666 : CollatzResearch.WordTrace tailWord_2421666 prefixEnd_2421666 1243478642651027454337967 := by
  unfold tailWord_2421666
  simp only [CollatzResearch.WordTrace]
  refine ⟨22081353811181286117629213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58883610163150096313677901 22081353811181286117629213)
  ·
    refine ⟨8280507679192982294110955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22081353811181286117629213 8280507679192982294110955)
    ·
      refine ⟨12420761518789473441166433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280507679192982294110955 12420761518789473441166433)
      ·
        refine ⟨9315571139092105080874825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12420761518789473441166433 9315571139092105080874825)
        ·
          refine ⟨6986678354319078810656119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9315571139092105080874825 6986678354319078810656119)
          ·
            refine ⟨10480017531478618215984179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6986678354319078810656119 10480017531478618215984179)
            ·
              refine ⟨15720026297217927323976269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10480017531478618215984179 15720026297217927323976269)
              ·
                refine ⟨5895009861456722746491101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15720026297217927323976269 5895009861456722746491101)
                ·
                  refine ⟨2210628698046271029934163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5895009861456722746491101 2210628698046271029934163)
                  ·
                    refine ⟨3315943047069406544901245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2210628698046271029934163 3315943047069406544901245)
                    ·
                      refine ⟨1243478642651027454337967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3315943047069406544901245 1243478642651027454337967)
                      ·
                        rfl

theorem cell23_2421666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2421666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421666 prefixEnd_2421666 := by exact prefixLift 2421666
  have htrace : WordTrace (prefixWord ++ tailWord_2421666) baseStart_2421666 baseEnd_2421666 := by
    simpa [prefixWord, tailWord_2421666, baseEnd_2421666] using wordTrace_append hprefix tailTrace_2421666
  have hstable : (prefixWord ++ tailWord_2421666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421666).length < 2 ^ (prefixWord ++ tailWord_2421666).sum := by decide
  have hdescent : baseEnd_2421666 < baseStart_2421666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421689 : List Nat := [1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2421689 : Nat := 118140960795 + 2421689 * 2 ^ 59
def prefixEnd_2421689 : Nat := 4983230072969 + 3 ^ 40 * 2421689 * 2
def baseEnd_2421689 : Nat := 1243490452706080864350361

theorem tailTrace_2421689 : CollatzResearch.WordTrace tailWord_2421689 prefixEnd_2421689 1243490452706080864350361 := by
  unfold tailWord_2421689
  simp only [CollatzResearch.WordTrace]
  refine ⟨88326254123641819398604121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58884169415761212932402747 88326254123641819398604121)
  ·
    refine ⟨66244690592731364548953091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88326254123641819398604121 66244690592731364548953091)
    ·
      refine ⟨99367035889097046823429637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66244690592731364548953091 99367035889097046823429637)
      ·
        refine ⟨18631319229205696279393057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99367035889097046823429637 18631319229205696279393057)
        ·
          refine ⟨13973489421904272209544793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18631319229205696279393057 13973489421904272209544793)
          ·
            refine ⟨10480117066428204157158595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13973489421904272209544793 10480117066428204157158595)
            ·
              refine ⟨15720175599642306235737893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10480117066428204157158595 15720175599642306235737893)
              ·
                refine ⟨2947532924932932419200855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15720175599642306235737893 2947532924932932419200855)
                ·
                  refine ⟨4421299387399398628801283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947532924932932419200855 4421299387399398628801283)
                  ·
                    refine ⟨6631949081099097943201925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4421299387399398628801283 6631949081099097943201925)
                    ·
                      refine ⟨1243490452706080864350361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6631949081099097943201925 1243490452706080864350361)
                      ·
                        rfl

theorem cell23_2421689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2421689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421689 prefixEnd_2421689 := by exact prefixLift 2421689
  have htrace : WordTrace (prefixWord ++ tailWord_2421689) baseStart_2421689 baseEnd_2421689 := by
    simpa [prefixWord, tailWord_2421689, baseEnd_2421689] using wordTrace_append hprefix tailTrace_2421689
  have hstable : (prefixWord ++ tailWord_2421689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421689).length < 2 ^ (prefixWord ++ tailWord_2421689).sum := by decide
  have hdescent : baseEnd_2421689 < baseStart_2421689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421733 : List Nat := [1, 3, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_2421733 : Nat := 118140960795 + 2421733 * 2 ^ 59
def prefixEnd_2421733 : Nat := 4983230072969 + 3 ^ 40 * 2421733 * 2
def baseEnd_2421733 : Nat := 414504348618292897400053

theorem tailTrace_2421733 : CollatzResearch.WordTrace tailWord_2421733 prefixEnd_2421733 414504348618292897400053 := by
  unfold tailWord_2421733
  simp only [CollatzResearch.WordTrace]
  refine ⟨88327858935482414913205853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58885239290321609942137235 88327858935482414913205853)
  ·
    refine ⟨33122947100805905592452195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88327858935482414913205853 33122947100805905592452195)
    ·
      refine ⟨49684420651208858388678293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33122947100805905592452195 49684420651208858388678293)
      ·
        refine ⟨2328957218025415236969295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 49684420651208858388678293 2328957218025415236969295)
        ·
          refine ⟨3493435827038122855453943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328957218025415236969295 3493435827038122855453943)
          ·
            refine ⟨5240153740557184283180915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3493435827038122855453943 5240153740557184283180915)
            ·
              refine ⟨7860230610835776424771373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5240153740557184283180915 7860230610835776424771373)
              ·
                refine ⟨2947586479063416159289265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7860230610835776424771373 2947586479063416159289265)
                ·
                  refine ⟨2210689859297562119466949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947586479063416159289265 2210689859297562119466949)
                  ·
                    refine ⟨414504348618292897400053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210689859297562119466949 414504348618292897400053)
                    ·
                      rfl

theorem cell23_2421733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_2421733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421733 prefixEnd_2421733 := by exact prefixLift 2421733
  have htrace : WordTrace (prefixWord ++ tailWord_2421733) baseStart_2421733 baseEnd_2421733 := by
    simpa [prefixWord, tailWord_2421733, baseEnd_2421733] using wordTrace_append hprefix tailTrace_2421733
  have hstable : (prefixWord ++ tailWord_2421733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421733).length < 2 ^ (prefixWord ++ tailWord_2421733).sum := by decide
  have hdescent : baseEnd_2421733 < baseStart_2421733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421779 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 5, 4, 2]
def baseStart_2421779 : Nat := 118140960795 + 2421779 * 2 ^ 59
def prefixEnd_2421779 : Nat := 4983230072969 + 3 ^ 40 * 2421779 * 2
def baseEnd_2421779 : Nat := 1243536665964985512224947

theorem tailTrace_2421779 : CollatzResearch.WordTrace tailWord_2421779 prefixEnd_2421779 1243536665964985512224947 := by
  unfold tailWord_2421779
  simp only [CollatzResearch.WordTrace]
  refine ⟨88329536693315764769380391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58886357795543843179586927 88329536693315764769380391)
  ·
    refine ⟨132494305039973647154070587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88329536693315764769380391 132494305039973647154070587)
    ·
      refine ⟨198741457559960470731105881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132494305039973647154070587 198741457559960470731105881)
      ·
        refine ⟨149056093169970353048329411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198741457559960470731105881 149056093169970353048329411)
        ·
          refine ⟨223584139754955529572494117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149056093169970353048329411 223584139754955529572494117)
          ·
            refine ⟨41922026204054161794842647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 223584139754955529572494117 41922026204054161794842647)
            ·
              refine ⟨62883039306081242692263971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41922026204054161794842647 62883039306081242692263971)
              ·
                refine ⟨94324558959121864038395957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62883039306081242692263971 94324558959121864038395957)
                ·
                  refine ⟨8842927402417674753599621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94324558959121864038395957 8842927402417674753599621)
                  ·
                    refine ⟨1658048887953314016299929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8842927402417674753599621 1658048887953314016299929)
                    ·
                      refine ⟨1243536665964985512224947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658048887953314016299929 1243536665964985512224947)
                      ·
                        rfl

theorem cell23_2421779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 5, 4, 2].length) (baseStart_2421779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421779 prefixEnd_2421779 := by exact prefixLift 2421779
  have htrace : WordTrace (prefixWord ++ tailWord_2421779) baseStart_2421779 baseEnd_2421779 := by
    simpa [prefixWord, tailWord_2421779, baseEnd_2421779] using wordTrace_append hprefix tailTrace_2421779
  have hstable : (prefixWord ++ tailWord_2421779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421779).length < 2 ^ (prefixWord ++ tailWord_2421779).sum := by decide
  have hdescent : baseEnd_2421779 < baseStart_2421779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421829 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 3]
def baseStart_2421829 : Nat := 118140960795 + 2421829 * 2 ^ 59
def prefixEnd_2421829 : Nat := 4983230072969 + 3 ^ 40 * 2421829 * 2
def baseEnd_2421829 : Nat := 1243562339997710316599717

theorem tailTrace_2421829 : CollatzResearch.WordTrace tailWord_2421829 prefixEnd_2421829 1243562339997710316599717 := by
  unfold tailWord_2421829
  simp only [CollatzResearch.WordTrace]
  refine ⟨88331360343134623308700541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58887573562089748872467027 88331360343134623308700541)
  ·
    refine ⟨33124260128675483740762703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88331360343134623308700541 33124260128675483740762703)
    ·
      refine ⟨49686390193013225611144055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33124260128675483740762703 49686390193013225611144055)
      ·
        refine ⟨74529585289519838416716083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49686390193013225611144055 74529585289519838416716083)
        ·
          refine ⟨111794377934279757625074125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74529585289519838416716083 111794377934279757625074125)
          ·
            refine ⟨41922891725354909109402797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111794377934279757625074125 41922891725354909109402797)
            ·
              refine ⟨15721084397008090916026049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41922891725354909109402797 15721084397008090916026049)
              ·
                refine ⟨11790813297756068187019537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15721084397008090916026049 11790813297756068187019537)
                ·
                  refine ⟨8843109973317051140264653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11790813297756068187019537 8843109973317051140264653)
                  ·
                    refine ⟨3316166239993894177599245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8843109973317051140264653 3316166239993894177599245)
                    ·
                      refine ⟨1243562339997710316599717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316166239993894177599245 1243562339997710316599717)
                      ·
                        rfl

theorem cell23_2421829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 2, 3, 3].length) (baseStart_2421829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421829 prefixEnd_2421829 := by exact prefixLift 2421829
  have htrace : WordTrace (prefixWord ++ tailWord_2421829) baseStart_2421829 baseEnd_2421829 := by
    simpa [prefixWord, tailWord_2421829, baseEnd_2421829] using wordTrace_append hprefix tailTrace_2421829
  have hstable : (prefixWord ++ tailWord_2421829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421829).length < 2 ^ (prefixWord ++ tailWord_2421829).sum := by decide
  have hdescent : baseEnd_2421829 < baseStart_2421829 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421936 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 5, 1, 3]
def baseStart_2421936 : Nat := 118140960795 + 2421936 * 2 ^ 59
def prefixEnd_2421936 : Nat := 4983230072969 + 3 ^ 40 * 2421936 * 2
def baseEnd_2421936 : Nat := 1243617282427741397961725

theorem tailTrace_2421936 : CollatzResearch.WordTrace tailWord_2421936 prefixEnd_2421936 1243617282427741397961725 := by
  unfold tailWord_2421936
  simp only [CollatzResearch.WordTrace]
  refine ⟨44167631476873490291422831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58890175302497987055230441 44167631476873490291422831)
  ·
    refine ⟨66251447215310235437134247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44167631476873490291422831 66251447215310235437134247)
    ·
      refine ⟨99377170822965353155701371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66251447215310235437134247 99377170822965353155701371)
      ·
        refine ⟨149065756234448029733552057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99377170822965353155701371 149065756234448029733552057)
        ·
          refine ⟨111799317175836022300164043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149065756234448029733552057 111799317175836022300164043)
          ·
            refine ⟨167698975763754033450246065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111799317175836022300164043 167698975763754033450246065)
            ·
              refine ⟨125774231822815525087684549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167698975763754033450246065 125774231822815525087684549)
              ·
                refine ⟨23582668466777910953940853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 125774231822815525087684549 23582668466777910953940853)
                ·
                  refine ⟨2210875168760429151931955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23582668466777910953940853 2210875168760429151931955)
                  ·
                    refine ⟨3316312753140643727897933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2210875168760429151931955 3316312753140643727897933)
                    ·
                      refine ⟨1243617282427741397961725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316312753140643727897933 1243617282427741397961725)
                      ·
                        rfl

theorem cell23_2421936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_2421936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421936 prefixEnd_2421936 := by exact prefixLift 2421936
  have htrace : WordTrace (prefixWord ++ tailWord_2421936) baseStart_2421936 baseEnd_2421936 := by
    simpa [prefixWord, tailWord_2421936, baseEnd_2421936] using wordTrace_append hprefix tailTrace_2421936
  have hstable : (prefixWord ++ tailWord_2421936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421936).length < 2 ^ (prefixWord ++ tailWord_2421936).sum := by decide
  have hdescent : baseEnd_2421936 < baseStart_2421936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421946 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2]
def baseStart_2421946 : Nat := 118140960795 + 2421946 * 2 ^ 59
def prefixEnd_2421946 : Nat := 4983230072969 + 3 ^ 40 * 2421946 * 2
def baseEnd_2421946 : Nat := 1243622417234286358836679

theorem tailTrace_2421946 : CollatzResearch.WordTrace tailWord_2421946 prefixEnd_2421946 1243622417234286358836679 := by
  unfold tailWord_2421946
  simp only [CollatzResearch.WordTrace]
  refine ⟨22083906920927688072677423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58890418455807168193806461 22083906920927688072677423)
  ·
    refine ⟨33125860381391532109016135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22083906920927688072677423 33125860381391532109016135)
    ·
      refine ⟨49688790572087298163524203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33125860381391532109016135 49688790572087298163524203)
      ·
        refine ⟨74533185858130947245286305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49688790572087298163524203 74533185858130947245286305)
        ·
          refine ⟨55899889393598210433964729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74533185858130947245286305 55899889393598210433964729)
          ·
            refine ⟨41924917045198657825473547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55899889393598210433964729 41924917045198657825473547)
            ·
              refine ⟨62887375567797986738210321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41924917045198657825473547 62887375567797986738210321)
              ·
                refine ⟨47165531675848490053657741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 62887375567797986738210321 47165531675848490053657741)
                ·
                  refine ⟨17687074378443183770121653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47165531675848490053657741 17687074378443183770121653)
                  ·
                    refine ⟨1658163222979048478448905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17687074378443183770121653 1658163222979048478448905)
                    ·
                      refine ⟨1243622417234286358836679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658163222979048478448905 1243622417234286358836679)
                      ·
                        rfl

theorem cell23_2421946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_2421946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421946 prefixEnd_2421946 := by exact prefixLift 2421946
  have htrace : WordTrace (prefixWord ++ tailWord_2421946) baseStart_2421946 baseEnd_2421946 := by
    simpa [prefixWord, tailWord_2421946, baseEnd_2421946] using wordTrace_append hprefix tailTrace_2421946
  have hstable : (prefixWord ++ tailWord_2421946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421946).length < 2 ^ (prefixWord ++ tailWord_2421946).sum := by decide
  have hdescent : baseEnd_2421946 < baseStart_2421946 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2421974 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 2, 2, 3]
def baseStart_2421974 : Nat := 118140960795 + 2421974 * 2 ^ 59
def prefixEnd_2421974 : Nat := 4983230072969 + 3 ^ 40 * 2421974 * 2
def baseEnd_2421974 : Nat := 1243636794692612249286551

theorem tailTrace_2421974 : CollatzResearch.WordTrace tailWord_2421974 prefixEnd_2421974 1243636794692612249286551 := by
  unfold tailWord_2421974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521040557975582067045561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58891099285072875381819317 5521040557975582067045561)
  ·
    refine ⟨4140780418481686550284171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5521040557975582067045561 4140780418481686550284171)
    ·
      refine ⟨6211170627722529825426257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140780418481686550284171 6211170627722529825426257)
      ·
        refine ⟨4658377970791897369069693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6211170627722529825426257 4658377970791897369069693)
        ·
          refine ⟨1746891739046961513401135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4658377970791897369069693 1746891739046961513401135)
          ·
            refine ⟨2620337608570442270101703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746891739046961513401135 2620337608570442270101703)
            ·
              refine ⟨3930506412855663405152555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620337608570442270101703 3930506412855663405152555)
              ·
                refine ⟨5895759619283495107728833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930506412855663405152555 5895759619283495107728833)
                ·
                  refine ⟨4421819714462621330796625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5895759619283495107728833 4421819714462621330796625)
                  ·
                    refine ⟨3316364785846965998097469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4421819714462621330796625 3316364785846965998097469)
                    ·
                      refine ⟨1243636794692612249286551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316364785846965998097469 1243636794692612249286551)
                      ·
                        rfl

theorem cell23_2421974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_2421974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2421974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2421974 prefixEnd_2421974 := by exact prefixLift 2421974
  have htrace : WordTrace (prefixWord ++ tailWord_2421974) baseStart_2421974 baseEnd_2421974 := by
    simpa [prefixWord, tailWord_2421974, baseEnd_2421974] using wordTrace_append hprefix tailTrace_2421974
  have hstable : (prefixWord ++ tailWord_2421974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2421974).length < 2 ^ (prefixWord ++ tailWord_2421974).sum := by decide
  have hdescent : baseEnd_2421974 < baseStart_2421974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2421974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422003 : List Nat := [1, 1, 1, 2, 2, 5, 3, 2, 2, 4]
def baseStart_2422003 : Nat := 118140960795 + 2422003 * 2 ^ 59
def prefixEnd_2422003 : Nat := 4983230072969 + 3 ^ 40 * 2422003 * 2
def baseEnd_2422003 : Nat := 414550561877197545274639

theorem tailTrace_2422003 : CollatzResearch.WordTrace tailWord_2422003 prefixEnd_2422003 414550561877197545274639 := by
  unfold tailWord_2422003
  simp only [CollatzResearch.WordTrace]
  refine ⟨88337706644504251025534663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58891804429669500683689775 88337706644504251025534663)
  ·
    refine ⟨132506559966756376538301995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88337706644504251025534663 132506559966756376538301995)
    ·
      refine ⟨198759839950134564807452993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132506559966756376538301995 198759839950134564807452993)
      ·
        refine ⟨149069879962600923605589745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198759839950134564807452993 149069879962600923605589745)
        ·
          refine ⟨111802409971950692704192309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149069879962600923605589745 111802409971950692704192309)
          ·
            refine ⟨10481475934870377441018029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111802409971950692704192309 10481475934870377441018029)
            ·
              refine ⟨3930553475576391540381761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10481475934870377441018029 3930553475576391540381761)
              ·
                refine ⟨2947915106682293655286321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930553475576391540381761 2947915106682293655286321)
                ·
                  refine ⟨2210936330011720241464741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2947915106682293655286321 2210936330011720241464741)
                  ·
                    refine ⟨414550561877197545274639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2210936330011720241464741 414550561877197545274639)
                    ·
                      rfl

theorem cell23_2422003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 2, 2, 4].length) (baseStart_2422003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422003 prefixEnd_2422003 := by exact prefixLift 2422003
  have htrace : WordTrace (prefixWord ++ tailWord_2422003) baseStart_2422003 baseEnd_2422003 := by
    simpa [prefixWord, tailWord_2422003, baseEnd_2422003] using wordTrace_append hprefix tailTrace_2422003
  have hstable : (prefixWord ++ tailWord_2422003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422003).length < 2 ^ (prefixWord ++ tailWord_2422003).sum := by decide
  have hdescent : baseEnd_2422003 < baseStart_2422003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422006 : List Nat := [5, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2422006 : Nat := 118140960795 + 2422006 * 2 ^ 59
def prefixEnd_2422006 : Nat := 4983230072969 + 3 ^ 40 * 2422006 * 2
def baseEnd_2422006 : Nat := 1243653226073556124086403

theorem tailTrace_2422006 : CollatzResearch.WordTrace tailWord_2422006 prefixEnd_2422006 1243653226073556124086403 := by
  unfold tailWord_2422006
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521113503968336408618367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58891877375662255025262581 5521113503968336408618367)
  ·
    refine ⟨8281670255952504612927551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5521113503968336408618367 8281670255952504612927551)
    ·
      refine ⟨12422505383928756919391327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8281670255952504612927551 12422505383928756919391327)
      ·
        refine ⟨18633758075893135379086991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12422505383928756919391327 18633758075893135379086991)
        ·
          refine ⟨27950637113839703068630487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18633758075893135379086991 27950637113839703068630487)
          ·
            refine ⟨41925955670759554602945731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27950637113839703068630487 41925955670759554602945731)
            ·
              refine ⟨62888933506139331904418597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41925955670759554602945731 62888933506139331904418597)
              ·
                refine ⟨11791675032401124732078487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62888933506139331904418597 11791675032401124732078487)
                ·
                  refine ⟨17687512548601687098117731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11791675032401124732078487 17687512548601687098117731)
                  ·
                    refine ⟨26531268822902530647176597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17687512548601687098117731 26531268822902530647176597)
                    ·
                      refine ⟨1243653226073556124086403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26531268822902530647176597 1243653226073556124086403)
                      ·
                        rfl

theorem cell23_2422006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2422006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422006 prefixEnd_2422006 := by exact prefixLift 2422006
  have htrace : WordTrace (prefixWord ++ tailWord_2422006) baseStart_2422006 baseEnd_2422006 := by
    simpa [prefixWord, tailWord_2422006, baseEnd_2422006] using wordTrace_append hprefix tailTrace_2422006
  have hstable : (prefixWord ++ tailWord_2422006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422006).length < 2 ^ (prefixWord ++ tailWord_2422006).sum := by decide
  have hdescent : baseEnd_2422006 < baseStart_2422006 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422010 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2]
def baseStart_2422010 : Nat := 118140960795 + 2422010 * 2 ^ 59
def prefixEnd_2422010 : Nat := 4983230072969 + 3 ^ 40 * 2422010 * 2
def baseEnd_2422010 : Nat := 1243655279996174108436385

theorem tailTrace_2422010 : CollatzResearch.WordTrace tailWord_2422010 prefixEnd_2422010 1243655279996174108436385 := by
  unfold tailWord_2422010
  simp only [CollatzResearch.WordTrace]
  refine ⟨22084490488869722805259871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58891974636985927480692989 22084490488869722805259871)
  ·
    refine ⟨33126735733304584207889807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22084490488869722805259871 33126735733304584207889807)
    ·
      refine ⟨49690103599956876311834711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33126735733304584207889807 49690103599956876311834711)
      ·
        refine ⟨74535155399935314467752067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49690103599956876311834711 74535155399935314467752067)
        ·
          refine ⟨111802733099902971701628101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74535155399935314467752067 111802733099902971701628101)
          ·
            refine ⟨20963012456231807194055269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111802733099902971701628101 20963012456231807194055269)
            ·
              refine ⟨3930564835543463848885363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20963012456231807194055269 3930564835543463848885363)
              ·
                refine ⟨5895847253315195773328045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930564835543463848885363 5895847253315195773328045)
                ·
                  refine ⟨2210942719993198414998017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5895847253315195773328045 2210942719993198414998017)
                  ·
                    refine ⟨1658207039994898811248513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2210942719993198414998017 1658207039994898811248513)
                    ·
                      refine ⟨1243655279996174108436385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658207039994898811248513 1243655279996174108436385)
                      ·
                        rfl

theorem cell23_2422010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_2422010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422010 prefixEnd_2422010 := by exact prefixLift 2422010
  have htrace : WordTrace (prefixWord ++ tailWord_2422010) baseStart_2422010 baseEnd_2422010 := by
    simpa [prefixWord, tailWord_2422010, baseEnd_2422010] using wordTrace_append hprefix tailTrace_2422010
  have hstable : (prefixWord ++ tailWord_2422010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422010).length < 2 ^ (prefixWord ++ tailWord_2422010).sum := by decide
  have hdescent : baseEnd_2422010 < baseStart_2422010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422030 : List Nat := [4, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3]
def baseStart_2422030 : Nat := 118140960795 + 2422030 * 2 ^ 59
def prefixEnd_2422030 : Nat := 4983230072969 + 3 ^ 40 * 2422030 * 2
def baseEnd_2422030 : Nat := 1243665549609264030186293

theorem tailTrace_2422030 : CollatzResearch.WordTrace tailWord_2422030 prefixEnd_2422030 1243665549609264030186293 := by
  unfold tailWord_2422030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042336426925804329595943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58892460943604289757845029 11042336426925804329595943)
  ·
    refine ⟨16563504640388706494393915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11042336426925804329595943 16563504640388706494393915)
    ·
      refine ⟨24845256960583059741590873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16563504640388706494393915 24845256960583059741590873)
      ·
        refine ⟨18633942720437294806193155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24845256960583059741590873 18633942720437294806193155)
        ·
          refine ⟨27950914080655942209289733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18633942720437294806193155 27950914080655942209289733)
          ·
            refine ⟨5240796390122989164241825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27950914080655942209289733 5240796390122989164241825)
            ·
              refine ⟨3930597292592241873181369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5240796390122989164241825 3930597292592241873181369)
              ·
                refine ⟨2947947969444181404886027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930597292592241873181369 2947947969444181404886027)
                ·
                  refine ⟨4421921954166272107329041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2947947969444181404886027 4421921954166272107329041)
                  ·
                    refine ⟨3316441465624704080496781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4421921954166272107329041 3316441465624704080496781)
                    ·
                      refine ⟨1243665549609264030186293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316441465624704080496781 1243665549609264030186293)
                      ·
                        rfl

theorem cell23_2422030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 1, 2, 3].length) (baseStart_2422030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422030 prefixEnd_2422030 := by exact prefixLift 2422030
  have htrace : WordTrace (prefixWord ++ tailWord_2422030) baseStart_2422030 baseEnd_2422030 := by
    simpa [prefixWord, tailWord_2422030, baseEnd_2422030] using wordTrace_append hprefix tailTrace_2422030
  have hstable : (prefixWord ++ tailWord_2422030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422030).length < 2 ^ (prefixWord ++ tailWord_2422030).sum := by decide
  have hdescent : baseEnd_2422030 < baseStart_2422030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422059 : List Nat := [1, 1, 1, 1, 2, 1, 2, 1, 5, 8]
def baseStart_2422059 : Nat := 118140960795 + 2422059 * 2 ^ 59
def prefixEnd_2422059 : Nat := 4983230072969 + 3 ^ 40 * 2422059 * 2
def baseEnd_2422059 : Nat := 414560146849414805574553

theorem tailTrace_2422059 : CollatzResearch.WordTrace tailWord_2422059 prefixEnd_2422059 414560146849414805574553 := by
  unfold tailWord_2422059
  simp only [CollatzResearch.WordTrace]
  refine ⟨88339749132301372589573231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58893166088200915059715487 88339749132301372589573231)
  ·
    refine ⟨132509623698452058884359847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88339749132301372589573231 132509623698452058884359847)
    ·
      refine ⟨198764435547678088326539771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132509623698452058884359847 198764435547678088326539771)
      ·
        refine ⟨298146653321517132489809657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198764435547678088326539771 298146653321517132489809657)
        ·
          refine ⟨223609989991137849367357243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298146653321517132489809657 223609989991137849367357243)
          ·
            refine ⟨335414984986706774051035865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223609989991137849367357243 335414984986706774051035865)
            ·
              refine ⟨251561238740030080538276899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335414984986706774051035865 251561238740030080538276899)
              ·
                refine ⟨377341858110045120807415349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 251561238740030080538276899 377341858110045120807415349)
                ·
                  refine ⟨35375799197816730075695189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 377341858110045120807415349 35375799197816730075695189)
                  ·
                    refine ⟨414560146849414805574553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 35375799197816730075695189 414560146849414805574553)
                    ·
                      rfl

theorem cell23_2422059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_2422059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422059 prefixEnd_2422059 := by exact prefixLift 2422059
  have htrace : WordTrace (prefixWord ++ tailWord_2422059) baseStart_2422059 baseEnd_2422059 := by
    simpa [prefixWord, tailWord_2422059, baseEnd_2422059] using wordTrace_append hprefix tailTrace_2422059
  have hstable : (prefixWord ++ tailWord_2422059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422059).length < 2 ^ (prefixWord ++ tailWord_2422059).sum := by decide
  have hdescent : baseEnd_2422059 < baseStart_2422059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422083 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 1, 4, 2]
def baseStart_2422083 : Nat := 118140960795 + 2422083 * 2 ^ 59
def prefixEnd_2422083 : Nat := 4983230072969 + 3 ^ 40 * 2422083 * 2
def baseEnd_2422083 : Nat := 1243692764083952322823549

theorem tailTrace_2422083 : CollatzResearch.WordTrace tailWord_2422083 prefixEnd_2422083 1243692764083952322823549 := by
  unfold tailWord_2422083
  simp only [CollatzResearch.WordTrace]
  refine ⟨88340624484214424688446903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58893749656142949792297935 88340624484214424688446903)
  ·
    refine ⟨132510936726321637032670355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88340624484214424688446903 132510936726321637032670355)
    ·
      refine ⟨198766405089482455549005533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132510936726321637032670355 198766405089482455549005533)
      ·
        refine ⟨74537401908555920830877075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198766405089482455549005533 74537401908555920830877075)
        ·
          refine ⟨111806102862833881246315613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74537401908555920830877075 111806102862833881246315613)
          ·
            refine ⟨41927288573562705467368355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111806102862833881246315613 41927288573562705467368355)
            ·
              refine ⟨62890932860344058201052533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41927288573562705467368355 62890932860344058201052533)
              ·
                refine ⟨5896024955657255456348675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62890932860344058201052533 5896024955657255456348675)
                ·
                  refine ⟨8844037433485883184523013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896024955657255456348675 8844037433485883184523013)
                  ·
                    refine ⟨1658257018778603097098065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8844037433485883184523013 1658257018778603097098065)
                    ·
                      refine ⟨1243692764083952322823549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658257018778603097098065 1243692764083952322823549)
                      ·
                        rfl

theorem cell23_2422083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 1, 4, 2].length) (baseStart_2422083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422083 prefixEnd_2422083 := by exact prefixLift 2422083
  have htrace : WordTrace (prefixWord ++ tailWord_2422083) baseStart_2422083 baseEnd_2422083 := by
    simpa [prefixWord, tailWord_2422083, baseEnd_2422083] using wordTrace_append hprefix tailTrace_2422083
  have hstable : (prefixWord ++ tailWord_2422083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422083).length < 2 ^ (prefixWord ++ tailWord_2422083).sum := by decide
  have hdescent : baseEnd_2422083 < baseStart_2422083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422087 : List Nat := [1, 1, 4, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_2422087 : Nat := 118140960795 + 2422087 * 2 ^ 59
def prefixEnd_2422087 : Nat := 4983230072969 + 3 ^ 40 * 2422087 * 2
def baseEnd_2422087 : Nat := 1243694818006570307173531

theorem tailTrace_2422087 : CollatzResearch.WordTrace tailWord_2422087 prefixEnd_2422087 1243694818006570307173531 := by
  unfold tailWord_2422087
  simp only [CollatzResearch.WordTrace]
  refine ⟨88340770376199933371592515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58893846917466622247728343 88340770376199933371592515)
  ·
    refine ⟨132511155564299900057388773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88340770376199933371592515 132511155564299900057388773)
    ·
      refine ⟨24845841668306231260760395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132511155564299900057388773 24845841668306231260760395)
      ·
        refine ⟨37268762502459346891140593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24845841668306231260760395 37268762502459346891140593)
        ·
          refine ⟨27951571876844510168355445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37268762502459346891140593 27951571876844510168355445)
          ·
            refine ⟨2620459863454172828283323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27951571876844510168355445 2620459863454172828283323)
            ·
              refine ⟨3930689795181259242424985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620459863454172828283323 3930689795181259242424985)
              ·
                refine ⟨2948017346385944431818739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930689795181259242424985 2948017346385944431818739)
                ·
                  refine ⟨4422026019578916647728109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948017346385944431818739 4422026019578916647728109)
                  ·
                    refine ⟨1658259757342093742898041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4422026019578916647728109 1658259757342093742898041)
                    ·
                      refine ⟨1243694818006570307173531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658259757342093742898041 1243694818006570307173531)
                      ·
                        rfl

theorem cell23_2422087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_2422087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422087 prefixEnd_2422087 := by exact prefixLift 2422087
  have htrace : WordTrace (prefixWord ++ tailWord_2422087) baseStart_2422087 baseEnd_2422087 := by
    simpa [prefixWord, tailWord_2422087, baseEnd_2422087] using wordTrace_append hprefix tailTrace_2422087
  have hstable : (prefixWord ++ tailWord_2422087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422087).length < 2 ^ (prefixWord ++ tailWord_2422087).sum := by decide
  have hdescent : baseEnd_2422087 < baseStart_2422087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422100 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_2422100 : Nat := 118140960795 + 2422100 * 2 ^ 59
def prefixEnd_2422100 : Nat := 4983230072969 + 3 ^ 40 * 2422100 * 2
def baseEnd_2422100 : Nat := 1243701493255078756310971

theorem tailTrace_2422100 : CollatzResearch.WordTrace tailWord_2422100 prefixEnd_2422100 1243701493255078756310971 := by
  unfold tailWord_2422100
  simp only [CollatzResearch.WordTrace]
  refine ⟨44170622262576418295907877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58894163016768557727877169 44170622262576418295907877)
  ·
    refine ⟨8281991674233078430482727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44170622262576418295907877 8281991674233078430482727)
    ·
      refine ⟨12422987511349617645724091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8281991674233078430482727 12422987511349617645724091)
      ·
        refine ⟨18634481267024426468586137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12422987511349617645724091 18634481267024426468586137)
        ·
          refine ⟨13975860950268319851439603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18634481267024426468586137 13975860950268319851439603)
          ·
            refine ⟨20963791425402479777159405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13975860950268319851439603 20963791425402479777159405)
            ·
              refine ⟨7861421784525929916434777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20963791425402479777159405 7861421784525929916434777)
              ·
                refine ⟨5896066338394447437326083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861421784525929916434777 5896066338394447437326083)
                ·
                  refine ⟨8844099507591671155989125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896066338394447437326083 8844099507591671155989125)
                  ·
                    refine ⟨1658268657673438341747961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8844099507591671155989125 1658268657673438341747961)
                    ·
                      refine ⟨1243701493255078756310971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658268657673438341747961 1243701493255078756310971)
                      ·
                        rfl

theorem cell23_2422100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_2422100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422100 prefixEnd_2422100 := by exact prefixLift 2422100
  have htrace : WordTrace (prefixWord ++ tailWord_2422100) baseStart_2422100 baseEnd_2422100 := by
    simpa [prefixWord, tailWord_2422100, baseEnd_2422100] using wordTrace_append hprefix tailTrace_2422100
  have hstable : (prefixWord ++ tailWord_2422100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422100).length < 2 ^ (prefixWord ++ tailWord_2422100).sum := by decide
  have hdescent : baseEnd_2422100 < baseStart_2422100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422117 : List Nat := [1, 3, 1, 3, 1, 2, 4, 2, 2, 2, 2]
def baseStart_2422117 : Nat := 118140960795 + 2422117 * 2 ^ 59
def prefixEnd_2422117 : Nat := 4983230072969 + 3 ^ 40 * 2422117 * 2
def baseEnd_2422117 : Nat := 1243710222426205189798393

theorem tailTrace_2422117 : CollatzResearch.WordTrace tailWord_2422117 prefixEnd_2422117 1243710222426205189798393 := by
  unfold tailWord_2422117
  simp only [CollatzResearch.WordTrace]
  refine ⟨88341864566091248495184605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58894576377394165663456403 88341864566091248495184605)
  ·
    refine ⟨33128199212284218185694227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88341864566091248495184605 33128199212284218185694227)
    ·
      refine ⟨49692298818426327278541341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33128199212284218185694227 49692298818426327278541341)
      ·
        refine ⟨18634612056909872729453003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49692298818426327278541341 18634612056909872729453003)
        ·
          refine ⟨27951918085364809094179505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18634612056909872729453003 27951918085364809094179505)
          ·
            refine ⟨20963938564023606820634629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27951918085364809094179505 20963938564023606820634629)
            ·
              refine ⟨3930738480754426278868993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20963938564023606820634629 3930738480754426278868993)
              ·
                refine ⟨2948053860565819709151745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3930738480754426278868993 2948053860565819709151745)
                ·
                  refine ⟨2211040395424364781863809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2948053860565819709151745 2211040395424364781863809)
                  ·
                    refine ⟨1658280296568273586397857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211040395424364781863809 1658280296568273586397857)
                    ·
                      refine ⟨1243710222426205189798393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658280296568273586397857 1243710222426205189798393)
                      ·
                        rfl

theorem cell23_2422117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 2, 2, 2, 2].length) (baseStart_2422117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422117 prefixEnd_2422117 := by exact prefixLift 2422117
  have htrace : WordTrace (prefixWord ++ tailWord_2422117) baseStart_2422117 baseEnd_2422117 := by
    simpa [prefixWord, tailWord_2422117, baseEnd_2422117] using wordTrace_append hprefix tailTrace_2422117
  have hstable : (prefixWord ++ tailWord_2422117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422117).length < 2 ^ (prefixWord ++ tailWord_2422117).sum := by decide
  have hdescent : baseEnd_2422117 < baseStart_2422117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422153 : List Nat := [1, 2, 1, 1, 7, 1, 1, 1, 1, 7]
def baseStart_2422153 : Nat := 118140960795 + 2422153 * 2 ^ 59
def prefixEnd_2422153 : Nat := 4983230072969 + 3 ^ 40 * 2422153 * 2
def baseEnd_2422153 : Nat := 414576235909922349649409

theorem tailTrace_2422153 : CollatzResearch.WordTrace tailWord_2422153 prefixEnd_2422153 414576235909922349649409 := by
  unfold tailWord_2422153
  simp only [CollatzResearch.WordTrace]
  refine ⟨88343177593960826643495113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58895451729307217762330075 88343177593960826643495113)
  ·
    refine ⟨66257383195470619982621335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88343177593960826643495113 66257383195470619982621335)
    ·
      refine ⟨99386074793205929973932003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66257383195470619982621335 99386074793205929973932003)
      ·
        refine ⟨149079112189808894960898005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99386074793205929973932003 149079112189808894960898005)
        ·
          refine ⟨3494041691948645975646047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 149079112189808894960898005 3494041691948645975646047)
          ·
            refine ⟨5241062537922968963469071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494041691948645975646047 5241062537922968963469071)
            ·
              refine ⟨7861593806884453445203607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241062537922968963469071 7861593806884453445203607)
              ·
                refine ⟨11792390710326680167805411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7861593806884453445203607 11792390710326680167805411)
                ·
                  refine ⟨17688586065490020251708117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11792390710326680167805411 17688586065490020251708117)
                  ·
                    refine ⟨414576235909922349649409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17688586065490020251708117 414576235909922349649409)
                    ·
                      rfl

theorem cell23_2422153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 7].length) (baseStart_2422153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422153 prefixEnd_2422153 := by exact prefixLift 2422153
  have htrace : WordTrace (prefixWord ++ tailWord_2422153) baseStart_2422153 baseEnd_2422153 := by
    simpa [prefixWord, tailWord_2422153, baseEnd_2422153] using wordTrace_append hprefix tailTrace_2422153
  have hstable : (prefixWord ++ tailWord_2422153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422153).length < 2 ^ (prefixWord ++ tailWord_2422153).sum := by decide
  have hdescent : baseEnd_2422153 < baseStart_2422153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422193 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 3]
def baseStart_2422193 : Nat := 118140960795 + 2422193 * 2 ^ 59
def prefixEnd_2422193 : Nat := 4983230072969 + 3 ^ 40 * 2422193 * 2
def baseEnd_2422193 : Nat := 1243749246955946892448043

theorem tailTrace_2422193 : CollatzResearch.WordTrace tailWord_2422193 prefixEnd_2422193 1243749246955946892448043 := by
  unfold tailWord_2422193
  simp only [CollatzResearch.WordTrace]
  refine ⟨88344636513815913474951233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58896424342543942316634155 88344636513815913474951233)
  ·
    refine ⟨66258477385361935106213425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88344636513815913474951233 66258477385361935106213425)
    ·
      refine ⟨49693858039021451329660069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66258477385361935106213425 49693858039021451329660069)
      ·
        refine ⟨9317598382316522124311263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49693858039021451329660069 9317598382316522124311263)
        ·
          refine ⟨13976397573474783186466895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9317598382316522124311263 13976397573474783186466895)
          ·
            refine ⟨20964596360212174779700343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13976397573474783186466895 20964596360212174779700343)
            ·
              refine ⟨31446894540318262169550515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20964596360212174779700343 31446894540318262169550515)
              ·
                refine ⟨47170341810477393254325773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31446894540318262169550515 47170341810477393254325773)
                ·
                  refine ⟨17688878178929022470372165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47170341810477393254325773 17688878178929022470372165)
                  ·
                    refine ⟨3316664658549191713194781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17688878178929022470372165 3316664658549191713194781)
                    ·
                      refine ⟨1243749246955946892448043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316664658549191713194781 1243749246955946892448043)
                      ·
                        rfl

theorem cell23_2422193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_2422193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422193 prefixEnd_2422193 := by exact prefixLift 2422193
  have htrace : WordTrace (prefixWord ++ tailWord_2422193) baseStart_2422193 baseEnd_2422193 := by
    simpa [prefixWord, tailWord_2422193, baseEnd_2422193] using wordTrace_append hprefix tailTrace_2422193
  have hstable : (prefixWord ++ tailWord_2422193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422193).length < 2 ^ (prefixWord ++ tailWord_2422193).sum := by decide
  have hdescent : baseEnd_2422193 < baseStart_2422193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422230 : List Nat := [5, 2, 1, 1, 1, 2, 2, 1, 8]
def baseStart_2422230 : Nat := 118140960795 + 2422230 * 2 ^ 59
def prefixEnd_2422230 : Nat := 4983230072969 + 3 ^ 40 * 2422230 * 2
def baseEnd_2422230 : Nat := 138196471748907027520597

theorem tailTrace_2422230 : CollatzResearch.WordTrace tailWord_2422230 prefixEnd_2422230 138196471748907027520597 := by
  unfold tailWord_2422230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521624125917616799628009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58897324009787912529365429 5521624125917616799628009)
  ·
    refine ⟨4141218094438212599721007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5521624125917616799628009 4141218094438212599721007)
    ·
      refine ⟨6211827141657318899581511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4141218094438212599721007 6211827141657318899581511)
      ·
        refine ⟨9317740712485978349372267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6211827141657318899581511 9317740712485978349372267)
        ·
          refine ⟨13976611068728967524058401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9317740712485978349372267 13976611068728967524058401)
          ·
            refine ⟨10482458301546725643043801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13976611068728967524058401 10482458301546725643043801)
            ·
              refine ⟨7861843726160044232282851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10482458301546725643043801 7861843726160044232282851)
              ·
                refine ⟨11792765589240066348424277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7861843726160044232282851 11792765589240066348424277)
                ·
                  refine ⟨138196471748907027520597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11792765589240066348424277 138196471748907027520597)
                  ·
                    rfl

theorem cell23_2422230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_2422230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422230 prefixEnd_2422230 := by exact prefixLift 2422230
  have htrace : WordTrace (prefixWord ++ tailWord_2422230) baseStart_2422230 baseEnd_2422230 := by
    simpa [prefixWord, tailWord_2422230, baseEnd_2422230] using wordTrace_append hprefix tailTrace_2422230
  have hstable : (prefixWord ++ tailWord_2422230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422230).length < 2 ^ (prefixWord ++ tailWord_2422230).sum := by decide
  have hdescent : baseEnd_2422230 < baseStart_2422230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422234 : List Nat := [3, 1, 1, 2, 3, 3, 3, 2, 1, 4]
def baseStart_2422234 : Nat := 118140960795 + 2422234 * 2 ^ 59
def prefixEnd_2422234 : Nat := 4983230072969 + 3 ^ 40 * 2422234 * 2
def baseEnd_2422234 : Nat := 414590099887593744011785

theorem tailTrace_2422234 : CollatzResearch.WordTrace tailWord_2422234 prefixEnd_2422234 414590099887593744011785 := by
  unfold tailWord_2422234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22086532976666844369298439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58897421271111584984795837 22086532976666844369298439)
  ·
    refine ⟨33129799465000266553947659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22086532976666844369298439 33129799465000266553947659)
    ·
      refine ⟨49694699197500399830921489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33129799465000266553947659 49694699197500399830921489)
      ·
        refine ⟨37271024398125299873191117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49694699197500399830921489 37271024398125299873191117)
        ·
          refine ⟨13976634149296987452446669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37271024398125299873191117 13976634149296987452446669)
          ·
            refine ⟨5241237805986370294667501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13976634149296987452446669 5241237805986370294667501)
            ·
              refine ⟨1965464177244888860500313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5241237805986370294667501 1965464177244888860500313)
              ·
                refine ⟨1474098132933666645375235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965464177244888860500313 1474098132933666645375235)
                ·
                  refine ⟨2211147199400499968062853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474098132933666645375235 2211147199400499968062853)
                  ·
                    refine ⟨414590099887593744011785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211147199400499968062853 414590099887593744011785)
                    ·
                      rfl

theorem cell23_2422234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_2422234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422234 prefixEnd_2422234 := by exact prefixLift 2422234
  have htrace : WordTrace (prefixWord ++ tailWord_2422234) baseStart_2422234 baseEnd_2422234 := by
    simpa [prefixWord, tailWord_2422234, baseEnd_2422234] using wordTrace_append hprefix tailTrace_2422234
  have hstable : (prefixWord ++ tailWord_2422234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422234).length < 2 ^ (prefixWord ++ tailWord_2422234).sum := by decide
  have hdescent : baseEnd_2422234 < baseStart_2422234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422240 : List Nat := [2, 1, 1, 3, 1, 1, 2, 5, 3, 1, 3]
def baseStart_2422240 : Nat := 118140960795 + 2422240 * 2 ^ 59
def prefixEnd_2422240 : Nat := 4983230072969 + 3 ^ 40 * 2422240 * 2
def baseEnd_2422240 : Nat := 1243773380546708208560327

theorem tailTrace_2422240 : CollatzResearch.WordTrace tailWord_2422240 prefixEnd_2422240 1243773380546708208560327 := by
  unfold tailWord_2422240
  simp only [CollatzResearch.WordTrace]
  refine ⟨44173175372322820250956087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58897567163097093667941449 44173175372322820250956087)
  ·
    refine ⟨66259763058484230376434131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44173175372322820250956087 66259763058484230376434131)
    ·
      refine ⟨99389644587726345564651197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66259763058484230376434131 99389644587726345564651197)
      ·
        refine ⟨37271116720397379586744199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99389644587726345564651197 37271116720397379586744199)
        ·
          refine ⟨55906675080596069380116299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37271116720397379586744199 55906675080596069380116299)
          ·
            refine ⟨83860012620894104070174449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55906675080596069380116299 83860012620894104070174449)
            ·
              refine ⟨62895009465670578052630837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83860012620894104070174449 62895009465670578052630837)
              ·
                refine ⟨5896407137406616692434141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62895009465670578052630837 5896407137406616692434141)
                ·
                  refine ⟨2211152676527481259662803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5896407137406616692434141 2211152676527481259662803)
                  ·
                    refine ⟨3316729014791221889494205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2211152676527481259662803 3316729014791221889494205)
                    ·
                      refine ⟨1243773380546708208560327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316729014791221889494205 1243773380546708208560327)
                      ·
                        rfl

theorem cell23_2422240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_2422240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422240 prefixEnd_2422240 := by exact prefixLift 2422240
  have htrace : WordTrace (prefixWord ++ tailWord_2422240) baseStart_2422240 baseEnd_2422240 := by
    simpa [prefixWord, tailWord_2422240, baseEnd_2422240] using wordTrace_append hprefix tailTrace_2422240
  have hstable : (prefixWord ++ tailWord_2422240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422240).length < 2 ^ (prefixWord ++ tailWord_2422240).sum := by decide
  have hdescent : baseEnd_2422240 < baseStart_2422240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422247 : List Nat := [1, 1, 5, 2, 1, 4, 2, 1, 6]
def baseStart_2422247 : Nat := 118140960795 + 2422247 * 2 ^ 59
def prefixEnd_2422247 : Nat := 4983230072969 + 3 ^ 40 * 2422247 * 2
def baseEnd_2422247 : Nat := 138197441656809964574755

theorem tailTrace_2422247 : CollatzResearch.WordTrace tailWord_2422247 prefixEnd_2422247 138197441656809964574755 := by
  unfold tailWord_2422247
  simp only [CollatzResearch.WordTrace]
  refine ⟨88346606055620280697416995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58897737370413520464944663 88346606055620280697416995)
  ·
    refine ⟨132519909083430421046125493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88346606055620280697416995 132519909083430421046125493)
    ·
      refine ⟨12423741476571601973074265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132519909083430421046125493 12423741476571601973074265)
      ·
        refine ⟨9317806107428701479805699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12423741476571601973074265 9317806107428701479805699)
        ·
          refine ⟨13976709161143052219708549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9317806107428701479805699 13976709161143052219708549)
          ·
            refine ⟨2620632967714322291195353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13976709161143052219708549 2620632967714322291195353)
            ·
              refine ⟨1965474725785741718396515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620632967714322291195353 1965474725785741718396515)
              ·
                refine ⟨2948212088678612577594773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965474725785741718396515 2948212088678612577594773)
                ·
                  refine ⟨138197441656809964574755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2948212088678612577594773 138197441656809964574755)
                  ·
                    rfl

theorem cell23_2422247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 2, 1, 6].length) (baseStart_2422247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422247 prefixEnd_2422247 := by exact prefixLift 2422247
  have htrace : WordTrace (prefixWord ++ tailWord_2422247) baseStart_2422247 baseEnd_2422247 := by
    simpa [prefixWord, tailWord_2422247, baseEnd_2422247] using wordTrace_append hprefix tailTrace_2422247
  have hstable : (prefixWord ++ tailWord_2422247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422247).length < 2 ^ (prefixWord ++ tailWord_2422247).sum := by decide
  have hdescent : baseEnd_2422247 < baseStart_2422247 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422280 : List Nat := [2, 1, 3, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_2422280 : Nat := 118140960795 + 2422280 * 2 ^ 59
def prefixEnd_2422280 : Nat := 4983230072969 + 3 ^ 40 * 2422280 * 2
def baseEnd_2422280 : Nat := 1243793919772888052060143

theorem tailTrace_2422280 : CollatzResearch.WordTrace tailWord_2422280 prefixEnd_2422280 1243793919772888052060143 := by
  unfold tailWord_2422280
  simp only [CollatzResearch.WordTrace]
  refine ⟨44173904832250363666684147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58898539776333818222245529 44173904832250363666684147)
  ·
    refine ⟨66260857248375545500026221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44173904832250363666684147 66260857248375545500026221)
    ·
      refine ⟨24847821468140829562509833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66260857248375545500026221 24847821468140829562509833)
      ·
        refine ⟨18635866101105622171882375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24847821468140829562509833 18635866101105622171882375)
        ·
          refine ⟨27953799151658433257823563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18635866101105622171882375 27953799151658433257823563)
          ·
            refine ⟨41930698727487649886735345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27953799151658433257823563 41930698727487649886735345)
            ·
              refine ⟨31448024045615737415051509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41930698727487649886735345 31448024045615737415051509)
              ·
                refine ⟨2948252254276475382661079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31448024045615737415051509 2948252254276475382661079)
                ·
                  refine ⟨4422378381414713073991619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948252254276475382661079 4422378381414713073991619)
                  ·
                    refine ⟨6633567572122069610987429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4422378381414713073991619 6633567572122069610987429)
                    ·
                      refine ⟨1243793919772888052060143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6633567572122069610987429 1243793919772888052060143)
                      ·
                        rfl

theorem cell23_2422280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_2422280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422280 prefixEnd_2422280 := by exact prefixLift 2422280
  have htrace : WordTrace (prefixWord ++ tailWord_2422280) baseStart_2422280 baseEnd_2422280 := by
    simpa [prefixWord, tailWord_2422280, baseEnd_2422280] using wordTrace_append hprefix tailTrace_2422280
  have hstable : (prefixWord ++ tailWord_2422280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422280).length < 2 ^ (prefixWord ++ tailWord_2422280).sum := by decide
  have hdescent : baseEnd_2422280 < baseStart_2422280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422285 : List Nat := [1, 7, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_2422285 : Nat := 118140960795 + 2422285 * 2 ^ 59
def prefixEnd_2422285 : Nat := 4983230072969 + 3 ^ 40 * 2422285 * 2
def baseEnd_2422285 : Nat := 414598829058720177499207

theorem tailTrace_2422285 : CollatzResearch.WordTrace tailWord_2422285 prefixEnd_2422285 414598829058720177499207 := by
  unfold tailWord_2422285
  simp only [CollatzResearch.WordTrace]
  refine ⟨88347992029482613187300309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58898661352988408791533539 88347992029482613187300309)
  ·
    refine ⟨2070656063190998746577351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 88347992029482613187300309 2070656063190998746577351)
    ·
      refine ⟨3105984094786498119866027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2070656063190998746577351 3105984094786498119866027)
      ·
        refine ⟨4658976142179747179799041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105984094786498119866027 4658976142179747179799041)
        ·
          refine ⟨3494232106634810384849281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4658976142179747179799041 3494232106634810384849281)
          ·
            refine ⟨2620674079976107788636961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494232106634810384849281 2620674079976107788636961)
            ·
              refine ⟨1965505559982080841477721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620674079976107788636961 1965505559982080841477721)
              ·
                refine ⟨1474129169986560631108291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965505559982080841477721 1474129169986560631108291)
                ·
                  refine ⟨2211193754979840946662437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474129169986560631108291 2211193754979840946662437)
                  ·
                    refine ⟨414598829058720177499207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211193754979840946662437 414598829058720177499207)
                    ·
                      rfl

theorem cell23_2422285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_2422285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422285 prefixEnd_2422285 := by exact prefixLift 2422285
  have htrace : WordTrace (prefixWord ++ tailWord_2422285) baseStart_2422285 baseEnd_2422285 := by
    simpa [prefixWord, tailWord_2422285, baseEnd_2422285] using wordTrace_append hprefix tailTrace_2422285
  have hstable : (prefixWord ++ tailWord_2422285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422285).length < 2 ^ (prefixWord ++ tailWord_2422285).sum := by decide
  have hdescent : baseEnd_2422285 < baseStart_2422285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422291 : List Nat := [1, 1, 1, 2, 1, 8, 2, 2, 1, 1, 3]
def baseStart_2422291 : Nat := 118140960795 + 2422291 * 2 ^ 59
def prefixEnd_2422291 : Nat := 4983230072969 + 3 ^ 40 * 2422291 * 2
def baseEnd_2422291 : Nat := 1243799568060087509022593

theorem tailTrace_2422291 : CollatzResearch.WordTrace tailWord_2422291 prefixEnd_2422291 1243799568060087509022593 := by
  unfold tailWord_2422291
  simp only [CollatzResearch.WordTrace]
  refine ⟨88348210867460876212018727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58898807244973917474679151 88348210867460876212018727)
  ·
    refine ⟨132522316301191314318028091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88348210867460876212018727 132522316301191314318028091)
    ·
      refine ⟨198783474451786971477042137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132522316301191314318028091 198783474451786971477042137)
      ·
        refine ⟨149087605838840228607781603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198783474451786971477042137 149087605838840228607781603)
        ·
          refine ⟨223631408758260342911672405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149087605838840228607781603 223631408758260342911672405)
          ·
            refine ⟨2620680571385863393496161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 223631408758260342911672405 2620680571385863393496161)
            ·
              refine ⟨1965510428539397545122121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2620680571385863393496161 1965510428539397545122121)
              ·
                refine ⟨1474132821404548158841591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965510428539397545122121 1474132821404548158841591)
                ·
                  refine ⟨2211199232106822238262387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474132821404548158841591 2211199232106822238262387)
                  ·
                    refine ⟨3316798848160233357393581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2211199232106822238262387 3316798848160233357393581)
                    ·
                      refine ⟨1243799568060087509022593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316798848160233357393581 1243799568060087509022593)
                      ·
                        rfl

theorem cell23_2422291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2, 1, 1, 3].length) (baseStart_2422291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422291 prefixEnd_2422291 := by exact prefixLift 2422291
  have htrace : WordTrace (prefixWord ++ tailWord_2422291) baseStart_2422291 baseEnd_2422291 := by
    simpa [prefixWord, tailWord_2422291, baseEnd_2422291] using wordTrace_append hprefix tailTrace_2422291
  have hstable : (prefixWord ++ tailWord_2422291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422291).length < 2 ^ (prefixWord ++ tailWord_2422291).sum := by decide
  have hdescent : baseEnd_2422291 < baseStart_2422291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422300 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2422300 : Nat := 118140960795 + 2422300 * 2 ^ 59
def prefixEnd_2422300 : Nat := 4983230072969 + 3 ^ 40 * 2422300 * 2
def baseEnd_2422300 : Nat := 1243804189385977973810051

theorem tailTrace_2422300 : CollatzResearch.WordTrace tailWord_2422300 prefixEnd_2422300 1243804189385977973810051 := by
  unfold tailWord_2422300
  simp only [CollatzResearch.WordTrace]
  refine ⟨44174269562214135374548177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58899026082952180499397569 44174269562214135374548177)
  ·
    refine ⟨33130702171660601530911133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44174269562214135374548177 33130702171660601530911133)
    ·
      refine ⟨12424013314372725574091675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33130702171660601530911133 12424013314372725574091675)
      ·
        refine ⟨18636019971559088361137513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12424013314372725574091675 18636019971559088361137513)
        ·
          refine ⟨13977014978669316270853135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18636019971559088361137513 13977014978669316270853135)
          ·
            refine ⟨20965522468003974406279703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13977014978669316270853135 20965522468003974406279703)
            ·
              refine ⟨31448283702005961609419555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20965522468003974406279703 31448283702005961609419555)
              ·
                refine ⟨47172425553008942414129333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31448283702005961609419555 47172425553008942414129333)
                ·
                  refine ⟨4422414895594588351324625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47172425553008942414129333 4422414895594588351324625)
                  ·
                    refine ⟨3316811171695941263493469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4422414895594588351324625 3316811171695941263493469)
                    ·
                      refine ⟨1243804189385977973810051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316811171695941263493469 1243804189385977973810051)
                      ·
                        rfl

theorem cell23_2422300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2422300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422300 prefixEnd_2422300 := by exact prefixLift 2422300
  have htrace : WordTrace (prefixWord ++ tailWord_2422300) baseStart_2422300 baseEnd_2422300 := by
    simpa [prefixWord, tailWord_2422300, baseEnd_2422300] using wordTrace_append hprefix tailTrace_2422300
  have hstable : (prefixWord ++ tailWord_2422300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422300).length < 2 ^ (prefixWord ++ tailWord_2422300).sum := by decide
  have hdescent : baseEnd_2422300 < baseStart_2422300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422303 : List Nat := [1, 1, 2, 4, 1, 1, 5, 8]
def baseStart_2422303 : Nat := 118140960795 + 2422303 * 2 ^ 59
def prefixEnd_2422303 : Nat := 4983230072969 + 3 ^ 40 * 2422303 * 2
def baseEnd_2422303 : Nat := 46066878882516350447131

theorem tailTrace_2422303 : CollatzResearch.WordTrace tailWord_2422303 prefixEnd_2422303 46066878882516350447131 := by
  unfold tailWord_2422303
  simp only [CollatzResearch.WordTrace]
  refine ⟨88348648543417402261455563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58899099028944934840970375 88348648543417402261455563)
  ·
    refine ⟨132522972815126103392183345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88348648543417402261455563 132522972815126103392183345)
    ·
      refine ⟨99392229611344577544137509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132522972815126103392183345 99392229611344577544137509)
      ·
        refine ⟨18636043052127108289525783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99392229611344577544137509 18636043052127108289525783)
        ·
          refine ⟨27954064578190662434288675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18636043052127108289525783 27954064578190662434288675)
          ·
            refine ⟨41931096867285993651433013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27954064578190662434288675 41931096867285993651433013)
            ·
              refine ⟨3931040331308061904821845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41931096867285993651433013 3931040331308061904821845)
              ·
                refine ⟨46066878882516350447131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3931040331308061904821845 46066878882516350447131)
                ·
                  rfl

theorem cell23_2422303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 8].length) (baseStart_2422303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422303 prefixEnd_2422303 := by exact prefixLift 2422303
  have htrace : WordTrace (prefixWord ++ tailWord_2422303) baseStart_2422303 baseEnd_2422303 := by
    simpa [prefixWord, tailWord_2422303, baseEnd_2422303] using wordTrace_append hprefix tailTrace_2422303
  have hstable : (prefixWord ++ tailWord_2422303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422303).length < 2 ^ (prefixWord ++ tailWord_2422303).sum := by decide
  have hdescent : baseEnd_2422303 < baseStart_2422303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422314 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2422314 : Nat := 118140960795 + 2422314 * 2 ^ 59
def prefixEnd_2422314 : Nat := 4983230072969 + 3 ^ 40 * 2422314 * 2
def baseEnd_2422314 : Nat := 1243811378115140919034987

theorem tailTrace_2422314 : CollatzResearch.WordTrace tailWord_2422314 prefixEnd_2422314 1243811378115140919034987 := by
  unfold tailWord_2422314
  simp only [CollatzResearch.WordTrace]
  refine ⟨22087262436594387785026499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58899366497585034093403997 22087262436594387785026499)
  ·
    refine ⟨33130893654891581677539749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22087262436594387785026499 33130893654891581677539749)
    ·
      refine ⟨6212042560292171564538703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33130893654891581677539749 6212042560292171564538703)
      ·
        refine ⟨9318063840438257346808055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6212042560292171564538703 9318063840438257346808055)
        ·
          refine ⟨13977095760657386020212083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318063840438257346808055 13977095760657386020212083)
          ·
            refine ⟨20965643640986079030318125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13977095760657386020212083 20965643640986079030318125)
            ·
              refine ⟨7862116365369779636369297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20965643640986079030318125 7862116365369779636369297)
              ·
                refine ⟨5896587274027334727276973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7862116365369779636369297 5896587274027334727276973)
                ·
                  refine ⟨2211220227760250522728865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5896587274027334727276973 2211220227760250522728865)
                  ·
                    refine ⟨1658415170820187892046649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211220227760250522728865 1658415170820187892046649)
                    ·
                      refine ⟨1243811378115140919034987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658415170820187892046649 1243811378115140919034987)
                      ·
                        rfl

theorem cell23_2422314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2422314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422314 prefixEnd_2422314 := by exact prefixLift 2422314
  have htrace : WordTrace (prefixWord ++ tailWord_2422314) baseStart_2422314 baseEnd_2422314 := by
    simpa [prefixWord, tailWord_2422314, baseEnd_2422314] using wordTrace_append hprefix tailTrace_2422314
  have hstable : (prefixWord ++ tailWord_2422314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422314).length < 2 ^ (prefixWord ++ tailWord_2422314).sum := by decide
  have hdescent : baseEnd_2422314 < baseStart_2422314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422330 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3]
def baseStart_2422330 : Nat := 118140960795 + 2422330 * 2 ^ 59
def prefixEnd_2422330 : Nat := 4983230072969 + 3 ^ 40 * 2422330 * 2
def baseEnd_2422330 : Nat := 1243819593805612856434913

theorem tailTrace_2422330 : CollatzResearch.WordTrace tailWord_2422330 prefixEnd_2422330 1243819593805612856434913 := by
  unfold tailWord_2422330
  simp only [CollatzResearch.WordTrace]
  refine ⟨22087408328579896468172111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58899755542879723915125629 22087408328579896468172111)
  ·
    refine ⟨33131112492869844702258167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22087408328579896468172111 33131112492869844702258167)
    ·
      refine ⟨49696668739304767053387251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33131112492869844702258167 49696668739304767053387251)
      ·
        refine ⟨74545003108957150580080877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49696668739304767053387251 74545003108957150580080877)
        ·
          refine ⟨27954376165858931467530329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74545003108957150580080877 27954376165858931467530329)
          ·
            refine ⟨20965782124394198600647747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27954376165858931467530329 20965782124394198600647747)
            ·
              refine ⟨31448673186591297900971621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20965782124394198600647747 31448673186591297900971621)
              ·
                refine ⟨5896626222485868356432179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31448673186591297900971621 5896626222485868356432179)
                ·
                  refine ⟨8844939333728802534648269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896626222485868356432179 8844939333728802534648269)
                  ·
                    refine ⟨3316852250148300950493101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8844939333728802534648269 3316852250148300950493101)
                    ·
                      refine ⟨1243819593805612856434913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316852250148300950493101 1243819593805612856434913)
                      ·
                        rfl

theorem cell23_2422330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_2422330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422330 prefixEnd_2422330 := by exact prefixLift 2422330
  have htrace : WordTrace (prefixWord ++ tailWord_2422330) baseStart_2422330 baseEnd_2422330 := by
    simpa [prefixWord, tailWord_2422330, baseEnd_2422330] using wordTrace_append hprefix tailTrace_2422330
  have hstable : (prefixWord ++ tailWord_2422330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422330).length < 2 ^ (prefixWord ++ tailWord_2422330).sum := by decide
  have hdescent : baseEnd_2422330 < baseStart_2422330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422358 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_2422358 : Nat := 118140960795 + 2422358 * 2 ^ 59
def prefixEnd_2422358 : Nat := 4983230072969 + 3 ^ 40 * 2422358 * 2
def baseEnd_2422358 : Nat := 414611323754646248961595

theorem tailTrace_2422358 : CollatzResearch.WordTrace tailWord_2422358 prefixEnd_2422358 414611323754646248961595 := by
  unfold tailWord_2422358
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521915909888634165919233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58900436372145431103138485 5521915909888634165919233)
  ·
    refine ⟨4141436932416475624439425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5521915909888634165919233 4141436932416475624439425)
    ·
      refine ⟨3106077699312356718329569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4141436932416475624439425 3106077699312356718329569)
      ·
        refine ⟨2329558274484267538747177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3106077699312356718329569 2329558274484267538747177)
        ·
          refine ⟨1747168705863200654060383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2329558274484267538747177 1747168705863200654060383)
          ·
            refine ⟨2620753058794800981090575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747168705863200654060383 2620753058794800981090575)
            ·
              refine ⟨3931129588192201471635863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620753058794800981090575 3931129588192201471635863)
              ·
                refine ⟨5896694382288302207453795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931129588192201471635863 5896694382288302207453795)
                ·
                  refine ⟨8845041573432453311180693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896694382288302207453795 8845041573432453311180693)
                  ·
                    refine ⟨414611323754646248961595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8845041573432453311180693 414611323754646248961595)
                    ·
                      rfl

theorem cell23_2422358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_2422358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422358 prefixEnd_2422358 := by exact prefixLift 2422358
  have htrace : WordTrace (prefixWord ++ tailWord_2422358) baseStart_2422358 baseEnd_2422358 := by
    simpa [prefixWord, tailWord_2422358, baseEnd_2422358] using wordTrace_append hprefix tailTrace_2422358
  have hstable : (prefixWord ++ tailWord_2422358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422358).length < 2 ^ (prefixWord ++ tailWord_2422358).sum := by decide
  have hdescent : baseEnd_2422358 < baseStart_2422358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422364 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2422364 : Nat := 118140960795 + 2422364 * 2 ^ 59
def prefixEnd_2422364 : Nat := 4983230072969 + 3 ^ 40 * 2422364 * 2
def baseEnd_2422364 : Nat := 1243837052147865723409757

theorem tailTrace_2422364 : CollatzResearch.WordTrace tailWord_2422364 prefixEnd_2422364 1243837052147865723409757 := by
  unfold tailWord_2422364
  simp only [CollatzResearch.WordTrace]
  refine ⟨44175436698098204839713073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58900582264130939786284097 44175436698098204839713073)
  ·
    refine ⟨33131577523573653629784805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44175436698098204839713073 33131577523573653629784805)
    ·
      refine ⟨6212170785670060055584651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33131577523573653629784805 6212170785670060055584651)
      ·
        refine ⟨9318256178505090083376977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6212170785670060055584651 9318256178505090083376977)
        ·
          refine ⟨6988692133878817562532733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9318256178505090083376977 6988692133878817562532733)
          ·
            refine ⟨2620759550204556585949775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6988692133878817562532733 2620759550204556585949775)
            ·
              refine ⟨3931139325306834878924663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620759550204556585949775 3931139325306834878924663)
              ·
                refine ⟨5896708987960252318386995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931139325306834878924663 5896708987960252318386995)
                ·
                  refine ⟨8845063481940378477580493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5896708987960252318386995 8845063481940378477580493)
                  ·
                    refine ⟨3316898805727641929092685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8845063481940378477580493 3316898805727641929092685)
                    ·
                      refine ⟨1243837052147865723409757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3316898805727641929092685 1243837052147865723409757)
                      ·
                        rfl

theorem cell23_2422364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2422364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422364 prefixEnd_2422364 := by exact prefixLift 2422364
  have htrace : WordTrace (prefixWord ++ tailWord_2422364) baseStart_2422364 baseEnd_2422364 := by
    simpa [prefixWord, tailWord_2422364, baseEnd_2422364] using wordTrace_append hprefix tailTrace_2422364
  have hstable : (prefixWord ++ tailWord_2422364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422364).length < 2 ^ (prefixWord ++ tailWord_2422364).sum := by decide
  have hdescent : baseEnd_2422364 < baseStart_2422364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422403 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9]
def baseStart_2422403 : Nat := 118140960795 + 2422403 * 2 ^ 59
def prefixEnd_2422403 : Nat := 4983230072969 + 3 ^ 40 * 2422403 * 2
def baseEnd_2422403 : Nat := 1243857077893391070822077

theorem tailTrace_2422403 : CollatzResearch.WordTrace tailWord_2422403 prefixEnd_2422403 1243857077893391070822077 := by
  unfold tailWord_2422403
  simp only [CollatzResearch.WordTrace]
  refine ⟨88352295843055119340095863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58901530562036746226730575 88352295843055119340095863)
  ·
    refine ⟨132528443764582679010143795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88352295843055119340095863 132528443764582679010143795)
    ·
      refine ⟨198792665646874018515215693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132528443764582679010143795 198792665646874018515215693)
      ·
        refine ⟨74547249617577756943205885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198792665646874018515215693 74547249617577756943205885)
        ·
          refine ⟨27955218606591658853702207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74547249617577756943205885 27955218606591658853702207)
          ·
            refine ⟨41932827909887488280553311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27955218606591658853702207 41932827909887488280553311)
            ·
              refine ⟨62899241864831232420829967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41932827909887488280553311 62899241864831232420829967)
              ·
                refine ⟨94348862797246848631244951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62899241864831232420829967 94348862797246848631244951)
                ·
                  refine ⟨141523294195870272946867427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94348862797246848631244951 141523294195870272946867427)
                  ·
                    refine ⟨212284941293805409420301141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 141523294195870272946867427 212284941293805409420301141)
                    ·
                      refine ⟨1243857077893391070822077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 212284941293805409420301141 1243857077893391070822077)
                      ·
                        rfl

theorem cell23_2422403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_2422403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422403 prefixEnd_2422403 := by exact prefixLift 2422403
  have htrace : WordTrace (prefixWord ++ tailWord_2422403) baseStart_2422403 baseEnd_2422403 := by
    simpa [prefixWord, tailWord_2422403, baseEnd_2422403] using wordTrace_append hprefix tailTrace_2422403
  have hstable : (prefixWord ++ tailWord_2422403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422403).length < 2 ^ (prefixWord ++ tailWord_2422403).sum := by decide
  have hdescent : baseEnd_2422403 < baseStart_2422403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422450 : List Nat := [3, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2422450 : Nat := 118140960795 + 2422450 * 2 ^ 59
def prefixEnd_2422450 : Nat := 4983230072969 + 3 ^ 40 * 2422450 * 2
def baseEnd_2422450 : Nat := 1243881211484152386934361

theorem tailTrace_2422450 : CollatzResearch.WordTrace tailWord_2422450 prefixEnd_2422450 1243881211484152386934361 := by
  unfold tailWord_2422450
  simp only [CollatzResearch.WordTrace]
  refine ⟨22088502518471211591764201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58902673382589897578037869 22088502518471211591764201)
  ·
    refine ⟨16566376888853408693823151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22088502518471211591764201 16566376888853408693823151)
    ·
      refine ⟨24849565333280113040734727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16566376888853408693823151 24849565333280113040734727)
      ·
        refine ⟨37274347999920169561102091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24849565333280113040734727 37274347999920169561102091)
        ·
          refine ⟨55911521999880254341653137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37274347999920169561102091 55911521999880254341653137)
          ·
            refine ⟨41933641499910190756239853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55911521999880254341653137 41933641499910190756239853)
            ·
              refine ⟨15725115562466321533589945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41933641499910190756239853 15725115562466321533589945)
              ·
                refine ⟨11793836671849741150192459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15725115562466321533589945 11793836671849741150192459)
                ·
                  refine ⟨17690755007774611725288689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11793836671849741150192459 17690755007774611725288689)
                  ·
                    refine ⟨13268066255830958793966517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17690755007774611725288689 13268066255830958793966517)
                    ·
                      refine ⟨1243881211484152386934361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13268066255830958793966517 1243881211484152386934361)
                      ·
                        rfl

theorem cell23_2422450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2422450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422450 prefixEnd_2422450 := by exact prefixLift 2422450
  have htrace : WordTrace (prefixWord ++ tailWord_2422450) baseStart_2422450 baseEnd_2422450 := by
    simpa [prefixWord, tailWord_2422450, baseEnd_2422450] using wordTrace_append hprefix tailTrace_2422450
  have hstable : (prefixWord ++ tailWord_2422450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422450).length < 2 ^ (prefixWord ++ tailWord_2422450).sum := by decide
  have hdescent : baseEnd_2422450 < baseStart_2422450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422487 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 3, 4]
def baseStart_2422487 : Nat := 118140960795 + 2422487 * 2 ^ 59
def prefixEnd_2422487 : Nat := 4983230072969 + 3 ^ 40 * 2422487 * 2
def baseEnd_2422487 : Nat := 414633403422789580723897

theorem tailTrace_2422487 : CollatzResearch.WordTrace tailWord_2422487 prefixEnd_2422487 414633403422789580723897 := by
  unfold tailWord_2422487
  simp only [CollatzResearch.WordTrace]
  refine ⟨88355359574750801686153715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58903573049833867790769143 88355359574750801686153715)
  ·
    refine ⟨132533039362126202529230573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88355359574750801686153715 132533039362126202529230573)
    ·
      refine ⟨49699889760797325948461465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132533039362126202529230573 49699889760797325948461465)
      ·
        refine ⟨37274917320597994461346099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49699889760797325948461465 37274917320597994461346099)
        ·
          refine ⟨55912375980896991692019149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37274917320597994461346099 55912375980896991692019149)
          ·
            refine ⟨20967140992836371884507181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55912375980896991692019149 20967140992836371884507181)
            ·
              refine ⟨7862677872313639456690193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20967140992836371884507181 7862677872313639456690193)
              ·
                refine ⟨5897008404235229592517645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7862677872313639456690193 5897008404235229592517645)
                ·
                  refine ⟨2211378151588211097194117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5897008404235229592517645 2211378151588211097194117)
                  ·
                    refine ⟨414633403422789580723897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211378151588211097194117 414633403422789580723897)
                    ·
                      rfl

theorem cell23_2422487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 4].length) (baseStart_2422487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422487 prefixEnd_2422487 := by exact prefixLift 2422487
  have htrace : WordTrace (prefixWord ++ tailWord_2422487) baseStart_2422487 baseEnd_2422487 := by
    simpa [prefixWord, tailWord_2422487, baseEnd_2422487] using wordTrace_append hprefix tailTrace_2422487
  have hstable : (prefixWord ++ tailWord_2422487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422487).length < 2 ^ (prefixWord ++ tailWord_2422487).sum := by decide
  have hdescent : baseEnd_2422487 < baseStart_2422487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422500 : List Nat := [2, 3, 1, 1, 1, 3, 2, 2, 8]
def baseStart_2422500 : Nat := 118140960795 + 2422500 * 2 ^ 59
def prefixEnd_2422500 : Nat := 4983230072969 + 3 ^ 40 * 2422500 * 2
def baseEnd_2422500 : Nat := 138211876168541910145459

theorem tailTrace_2422500 : CollatzResearch.WordTrace tailWord_2422500 prefixEnd_2422500 138211876168541910145459 := by
  unfold tailWord_2422500
  simp only [CollatzResearch.WordTrace]
  refine ⟨44177916861851852453188477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58903889149135803270917969 44177916861851852453188477)
  ·
    refine ⟨16566718823194444669945679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44177916861851852453188477 16566718823194444669945679)
    ·
      refine ⟨24850078234791667004918519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16566718823194444669945679 24850078234791667004918519)
      ·
        refine ⟨37275117352187500507377779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24850078234791667004918519 37275117352187500507377779)
        ·
          refine ⟨55912676028281250761066669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37275117352187500507377779 55912676028281250761066669)
          ·
            refine ⟨20967253510605469035400001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55912676028281250761066669 20967253510605469035400001)
            ·
              refine ⟨15725440132954101776550001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20967253510605469035400001 15725440132954101776550001)
              ·
                refine ⟨11794080099715576332412501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15725440132954101776550001 11794080099715576332412501)
                ·
                  refine ⟨138211876168541910145459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11794080099715576332412501 138211876168541910145459)
                  ·
                    rfl

theorem cell23_2422500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_2422500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422500 prefixEnd_2422500 := by exact prefixLift 2422500
  have htrace : WordTrace (prefixWord ++ tailWord_2422500) baseStart_2422500 baseEnd_2422500 := by
    simpa [prefixWord, tailWord_2422500, baseEnd_2422500] using wordTrace_append hprefix tailTrace_2422500
  have hstable : (prefixWord ++ tailWord_2422500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422500).length < 2 ^ (prefixWord ++ tailWord_2422500).sum := by decide
  have hdescent : baseEnd_2422500 < baseStart_2422500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422540 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_2422540 : Nat := 118140960795 + 2422540 * 2 ^ 59
def prefixEnd_2422540 : Nat := 4983230072969 + 3 ^ 40 * 2422540 * 2
def baseEnd_2422540 : Nat := 1243927424743057034808947

theorem tailTrace_2422540 : CollatzResearch.WordTrace tailWord_2422540 prefixEnd_2422540 1243927424743057034808947 := by
  unfold tailWord_2422540
  simp only [CollatzResearch.WordTrace]
  refine ⟨44178646321779395868916537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58904861762372527825222049 44178646321779395868916537)
  ·
    refine ⟨33133984741334546901687403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44178646321779395868916537 33133984741334546901687403)
    ·
      refine ⟨49700977112001820352531105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33133984741334546901687403 49700977112001820352531105)
      ·
        refine ⟨37275732834001365264398329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49700977112001820352531105 37275732834001365264398329)
        ·
          refine ⟨27956799625501023948298747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37275732834001365264398329 27956799625501023948298747)
          ·
            refine ⟨41935199438251535922448121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27956799625501023948298747 41935199438251535922448121)
            ·
              refine ⟨31451399578688651941836091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41935199438251535922448121 31451399578688651941836091)
              ·
                refine ⟨47177099368032977912754137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31451399578688651941836091 47177099368032977912754137)
                ·
                  refine ⟨35382824526024733434565603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47177099368032977912754137 35382824526024733434565603)
                  ·
                    refine ⟨53074236789037100151848405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35382824526024733434565603 53074236789037100151848405)
                    ·
                      refine ⟨1243927424743057034808947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53074236789037100151848405 1243927424743057034808947)
                      ·
                        rfl

theorem cell23_2422540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_2422540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422540 prefixEnd_2422540 := by exact prefixLift 2422540
  have htrace : WordTrace (prefixWord ++ tailWord_2422540) baseStart_2422540 baseEnd_2422540 := by
    simpa [prefixWord, tailWord_2422540, baseEnd_2422540] using wordTrace_append hprefix tailTrace_2422540
  have hstable : (prefixWord ++ tailWord_2422540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422540).length < 2 ^ (prefixWord ++ tailWord_2422540).sum := by decide
  have hdescent : baseEnd_2422540 < baseStart_2422540 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422554 : List Nat := [3, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2]
def baseStart_2422554 : Nat := 118140960795 + 2422554 * 2 ^ 59
def prefixEnd_2422554 : Nat := 4983230072969 + 3 ^ 40 * 2422554 * 2
def baseEnd_2422554 : Nat := 1243934613472219980033883

theorem tailTrace_2422554 : CollatzResearch.WordTrace tailWord_2422554 prefixEnd_2422554 1243934613472219980033883 := by
  unfold tailWord_2422554
  simp only [CollatzResearch.WordTrace]
  refine ⟨22089450816377018032210679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58905202177005381419228477 22089450816377018032210679)
  ·
    refine ⟨33134176224565527048316019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22089450816377018032210679 33134176224565527048316019)
    ·
      refine ⟨49701264336848290572474029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33134176224565527048316019 49701264336848290572474029)
      ·
        refine ⟨18637974126318108964677761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49701264336848290572474029 18637974126318108964677761)
        ·
          refine ⟨13978480594738581723508321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18637974126318108964677761 13978480594738581723508321)
          ·
            refine ⟨10483860446053936292631241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13978480594738581723508321 10483860446053936292631241)
            ·
              refine ⟨7862895334540452219473431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10483860446053936292631241 7862895334540452219473431)
              ·
                refine ⟨11794343001810678329210147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7862895334540452219473431 11794343001810678329210147)
                ·
                  refine ⟨17691514502716017493815221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11794343001810678329210147 17691514502716017493815221)
                  ·
                    refine ⟨1658579484629626640045177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17691514502716017493815221 1658579484629626640045177)
                    ·
                      refine ⟨1243934613472219980033883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658579484629626640045177 1243934613472219980033883)
                      ·
                        rfl

theorem cell23_2422554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_2422554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422554 prefixEnd_2422554 := by exact prefixLift 2422554
  have htrace : WordTrace (prefixWord ++ tailWord_2422554) baseStart_2422554 baseEnd_2422554 := by
    simpa [prefixWord, tailWord_2422554, baseEnd_2422554] using wordTrace_append hprefix tailTrace_2422554
  have hstable : (prefixWord ++ tailWord_2422554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422554).length < 2 ^ (prefixWord ++ tailWord_2422554).sum := by decide
  have hdescent : baseEnd_2422554 < baseStart_2422554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422564 : List Nat := [2, 3, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_2422564 : Nat := 118140960795 + 2422564 * 2 ^ 59
def prefixEnd_2422564 : Nat := 4983230072969 + 3 ^ 40 * 2422564 * 2
def baseEnd_2422564 : Nat := 414646582759588313636279

theorem tailTrace_2422564 : CollatzResearch.WordTrace tailWord_2422564 prefixEnd_2422564 414646582759588313636279 := by
  unfold tailWord_2422564
  simp only [CollatzResearch.WordTrace]
  refine ⟨44179083997735921918353373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58905445330314562557804497 44179083997735921918353373)
  ·
    refine ⟨16567156499150970719382515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44179083997735921918353373 16567156499150970719382515)
    ·
      refine ⟨24850734748726456079073773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16567156499150970719382515 24850734748726456079073773)
      ·
        refine ⟨9319025530772421029652665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24850734748726456079073773 9319025530772421029652665)
        ·
          refine ⟨6989269148079315772239499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9319025530772421029652665 6989269148079315772239499)
          ·
            refine ⟨10483903722118973658359249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989269148079315772239499 10483903722118973658359249)
            ·
              refine ⟨7862927791589230243769437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10483903722118973658359249 7862927791589230243769437)
              ·
                refine ⟨2948597921845961341413539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7862927791589230243769437 2948597921845961341413539)
                ·
                  refine ⟨4422896882768942012120309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948597921845961341413539 4422896882768942012120309)
                  ·
                    refine ⟨414646582759588313636279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4422896882768942012120309 414646582759588313636279)
                    ·
                      rfl

theorem cell23_2422564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_2422564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422564 prefixEnd_2422564 := by exact prefixLift 2422564
  have htrace : WordTrace (prefixWord ++ tailWord_2422564) baseStart_2422564 baseEnd_2422564 := by
    simpa [prefixWord, tailWord_2422564, baseEnd_2422564] using wordTrace_append hprefix tailTrace_2422564
  have hstable : (prefixWord ++ tailWord_2422564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422564).length < 2 ^ (prefixWord ++ tailWord_2422564).sum := by decide
  have hdescent : baseEnd_2422564 < baseStart_2422564 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422597 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_2422597 : Nat := 118140960795 + 2422597 * 2 ^ 59
def prefixEnd_2422597 : Nat := 4983230072969 + 3 ^ 40 * 2422597 * 2
def baseEnd_2422597 : Nat := 1243956693140363311796185

theorem tailTrace_2422597 : CollatzResearch.WordTrace tailWord_2422597 prefixEnd_2422597 1243956693140363311796185 := by
  unfold tailWord_2422597
  simp only [CollatzResearch.WordTrace]
  refine ⟨88359371604352290472658045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58906247736234860315105363 88359371604352290472658045)
  ·
    refine ⟨33134764351632108927246767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88359371604352290472658045 33134764351632108927246767)
    ·
      refine ⟨49702146527448163390870151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33134764351632108927246767 49702146527448163390870151)
      ·
        refine ⟨74553219791172245086305227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49702146527448163390870151 74553219791172245086305227)
        ·
          refine ⟨111829829686758367629457841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74553219791172245086305227 111829829686758367629457841)
          ·
            refine ⟨83872372265068775722093381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111829829686758367629457841 83872372265068775722093381)
            ·
              refine ⟨15726069799700395447892509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83872372265068775722093381 15726069799700395447892509)
              ·
                refine ⟨5897276174887648292959691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15726069799700395447892509 5897276174887648292959691)
                ·
                  refine ⟨8845914262331472439439537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897276174887648292959691 8845914262331472439439537)
                  ·
                    refine ⟨6634435696748604329579653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8845914262331472439439537 6634435696748604329579653)
                    ·
                      refine ⟨1243956693140363311796185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6634435696748604329579653 1243956693140363311796185)
                      ·
                        rfl

theorem cell23_2422597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_2422597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422597 prefixEnd_2422597 := by exact prefixLift 2422597
  have htrace : WordTrace (prefixWord ++ tailWord_2422597) baseStart_2422597 baseEnd_2422597 := by
    simpa [prefixWord, tailWord_2422597, baseEnd_2422597] using wordTrace_append hprefix tailTrace_2422597
  have hstable : (prefixWord ++ tailWord_2422597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422597).length < 2 ^ (prefixWord ++ tailWord_2422597).sum := by decide
  have hdescent : baseEnd_2422597 < baseStart_2422597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422598 : List Nat := [6, 1, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2422598 : Nat := 118140960795 + 2422598 * 2 ^ 59
def prefixEnd_2422598 : Nat := 4983230072969 + 3 ^ 40 * 2422598 * 2
def baseEnd_2422598 : Nat := 414652402207005935961227

theorem tailTrace_2422598 : CollatzResearch.WordTrace tailWord_2422598 prefixEnd_2422598 414652402207005935961227 := by
  unfold tailWord_2422598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2761231502417145863857639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58906272051565778428962965 2761231502417145863857639)
  ·
    refine ⟨4141847253625718795786459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2761231502417145863857639 4141847253625718795786459)
    ·
      refine ⟨6212770880438578193679689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4141847253625718795786459 6212770880438578193679689)
      ·
        refine ⟨4659578160328933645259767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6212770880438578193679689 4659578160328933645259767)
        ·
          refine ⟨6989367240493400467889651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659578160328933645259767 6989367240493400467889651)
          ·
            refine ⟨10484050860740100701834477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989367240493400467889651 10484050860740100701834477)
            ·
              refine ⟨3931519072777537763187929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10484050860740100701834477 3931519072777537763187929)
              ·
                refine ⟨2948639304583153322390947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3931519072777537763187929 2948639304583153322390947)
                ·
                  refine ⟨4422958956874729983586421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948639304583153322390947 4422958956874729983586421)
                  ·
                    refine ⟨414652402207005935961227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4422958956874729983586421 414652402207005935961227)
                    ·
                      rfl

theorem cell23_2422598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2422598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422598 prefixEnd_2422598 := by exact prefixLift 2422598
  have htrace : WordTrace (prefixWord ++ tailWord_2422598) baseStart_2422598 baseEnd_2422598 := by
    simpa [prefixWord, tailWord_2422598, baseEnd_2422598] using wordTrace_append hprefix tailTrace_2422598
  have hstable : (prefixWord ++ tailWord_2422598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422598).length < 2 ^ (prefixWord ++ tailWord_2422598).sum := by decide
  have hdescent : baseEnd_2422598 < baseStart_2422598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422618 : List Nat := [3, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2]
def baseStart_2422618 : Nat := 118140960795 + 2422618 * 2 ^ 59
def prefixEnd_2422618 : Nat := 4983230072969 + 3 ^ 40 * 2422618 * 2
def baseEnd_2422618 : Nat := 1243967476234107729633589

theorem tailTrace_2422618 : CollatzResearch.WordTrace tailWord_2422618 prefixEnd_2422618 1243967476234107729633589 := by
  unfold tailWord_2422618
  simp only [CollatzResearch.WordTrace]
  refine ⟨22090034384319052764793127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58906758358184140706115005 22090034384319052764793127)
  ·
    refine ⟨33135051576478579147189691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22090034384319052764793127 33135051576478579147189691)
    ·
      refine ⟨49702577364717868720784537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33135051576478579147189691 49702577364717868720784537)
      ·
        refine ⟨37276933023538401540588403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49702577364717868720784537 37276933023538401540588403)
        ·
          refine ⟨55915399535307602310882605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37276933023538401540588403 55915399535307602310882605)
          ·
            refine ⟨20968274825740350866580977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55915399535307602310882605 20968274825740350866580977)
            ·
              refine ⟨15726206119305263149935733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20968274825740350866580977 15726206119305263149935733)
              ·
                refine ⟨1474331823684868420306475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15726206119305263149935733 1474331823684868420306475)
                ·
                  refine ⟨2211497735527302630459713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474331823684868420306475 2211497735527302630459713)
                  ·
                    refine ⟨1658623301645476972844785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211497735527302630459713 1658623301645476972844785)
                    ·
                      refine ⟨1243967476234107729633589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658623301645476972844785 1243967476234107729633589)
                      ·
                        rfl

theorem cell23_2422618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_2422618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422618 prefixEnd_2422618 := by exact prefixLift 2422618
  have htrace : WordTrace (prefixWord ++ tailWord_2422618) baseStart_2422618 baseEnd_2422618 := by
    simpa [prefixWord, tailWord_2422618, baseEnd_2422618] using wordTrace_append hprefix tailTrace_2422618
  have hstable : (prefixWord ++ tailWord_2422618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422618).length < 2 ^ (prefixWord ++ tailWord_2422618).sum := by decide
  have hdescent : baseEnd_2422618 < baseStart_2422618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422637 : List Nat := [1, 5, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_2422637 : Nat := 118140960795 + 2422637 * 2 ^ 59
def prefixEnd_2422637 : Nat := 4983230072969 + 3 ^ 40 * 2422637 * 2
def baseEnd_2422637 : Nat := 414659077455514385098667

theorem tailTrace_2422637 : CollatzResearch.WordTrace tailWord_2422637 prefixEnd_2422637 414659077455514385098667 := by
  unfold tailWord_2422637
  simp only [CollatzResearch.WordTrace]
  refine ⟨88360830524207377304114165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58907220349471584869409443 88360830524207377304114165)
  ·
    refine ⟨8283827861644441622260703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88360830524207377304114165 8283827861644441622260703)
    ·
      refine ⟨12425741792466662433391055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8283827861644441622260703 12425741792466662433391055)
      ·
        refine ⟨18638612688699993650086583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12425741792466662433391055 18638612688699993650086583)
        ·
          refine ⟨27957919033049990475129875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18638612688699993650086583 27957919033049990475129875)
          ·
            refine ⟨41936878549574985712694813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27957919033049990475129875 41936878549574985712694813)
            ·
              refine ⟨15726329456090619642260555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41936878549574985712694813 15726329456090619642260555)
              ·
                refine ⟨23589494184135929463390833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15726329456090619642260555 23589494184135929463390833)
                ·
                  refine ⟨17692120638101947097543125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23589494184135929463390833 17692120638101947097543125)
                  ·
                    refine ⟨414659077455514385098667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 17692120638101947097543125 414659077455514385098667)
                    ·
                      rfl

theorem cell23_2422637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_2422637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422637 prefixEnd_2422637 := by exact prefixLift 2422637
  have htrace : WordTrace (prefixWord ++ tailWord_2422637) baseStart_2422637 baseEnd_2422637 := by
    simpa [prefixWord, tailWord_2422637, baseEnd_2422637] using wordTrace_append hprefix tailTrace_2422637
  have hstable : (prefixWord ++ tailWord_2422637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422637).length < 2 ^ (prefixWord ++ tailWord_2422637).sum := by decide
  have hdescent : baseEnd_2422637 < baseStart_2422637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422661 : List Nat := [1, 3, 1, 1, 3, 2, 2, 4, 1, 3, 2]
def baseStart_2422661 : Nat := 118140960795 + 2422661 * 2 ^ 59
def prefixEnd_2422661 : Nat := 4983230072969 + 3 ^ 40 * 2422661 * 2
def baseEnd_2422661 : Nat := 1243989555902251061395891

theorem tailTrace_2422661 : CollatzResearch.WordTrace tailWord_2422661 prefixEnd_2422661 1243989555902251061395891 := by
  unfold tailWord_2422661
  simp only [CollatzResearch.WordTrace]
  refine ⟨88361705876120429402987837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58907803917413619601991891 88361705876120429402987837)
  ·
    refine ⟨33135639703545161026120439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88361705876120429402987837 33135639703545161026120439)
    ·
      refine ⟨49703459555317741539180659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33135639703545161026120439 49703459555317741539180659)
      ·
        refine ⟨74555189332976612308770989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49703459555317741539180659 74555189332976612308770989)
        ·
          refine ⟨27958195999866229615789121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74555189332976612308770989 27958195999866229615789121)
          ·
            refine ⟨20968646999899672211841841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27958195999866229615789121 20968646999899672211841841)
            ·
              refine ⟨15726485249924754158881381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20968646999899672211841841 15726485249924754158881381)
              ·
                refine ⟨2948715984360891404790259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15726485249924754158881381 2948715984360891404790259)
                ·
                  refine ⟨4423073976541337107185389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2948715984360891404790259 4423073976541337107185389)
                  ·
                    refine ⟨1658652741203001415194521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4423073976541337107185389 1658652741203001415194521)
                    ·
                      refine ⟨1243989555902251061395891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658652741203001415194521 1243989555902251061395891)
                      ·
                        rfl

theorem cell23_2422661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4, 1, 3, 2].length) (baseStart_2422661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422661 prefixEnd_2422661 := by exact prefixLift 2422661
  have htrace : WordTrace (prefixWord ++ tailWord_2422661) baseStart_2422661 baseEnd_2422661 := by
    simpa [prefixWord, tailWord_2422661, baseEnd_2422661] using wordTrace_append hprefix tailTrace_2422661
  have hstable : (prefixWord ++ tailWord_2422661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422661).length < 2 ^ (prefixWord ++ tailWord_2422661).sum := by decide
  have hdescent : baseEnd_2422661 < baseStart_2422661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422677 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_2422677 : Nat := 118140960795 + 2422677 * 2 ^ 59
def prefixEnd_2422677 : Nat := 4983230072969 + 3 ^ 40 * 2422677 * 2
def baseEnd_2422677 : Nat := 1243997771592722998795817

theorem tailTrace_2422677 : CollatzResearch.WordTrace tailWord_2422677 prefixEnd_2422677 1243997771592722998795817 := by
  unfold tailWord_2422677
  simp only [CollatzResearch.WordTrace]
  refine ⟨88362289444062464135570285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58908192962708309423713523 88362289444062464135570285)
  ·
    refine ⟨33135858541523424050838857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88362289444062464135570285 33135858541523424050838857)
    ·
      refine ⟨24851893906142568038129143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33135858541523424050838857 24851893906142568038129143)
      ·
        refine ⟨37277840859213852057193715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24851893906142568038129143 37277840859213852057193715)
        ·
          refine ⟨55916761288820778085790573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37277840859213852057193715 55916761288820778085790573)
          ·
            refine ⟨20968785483307791782171465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55916761288820778085790573 20968785483307791782171465)
            ·
              refine ⟨15726589112480843836628599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20968785483307791782171465 15726589112480843836628599)
              ·
                refine ⟨23589883668721265754942899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15726589112480843836628599 23589883668721265754942899)
                ·
                  refine ⟨35384825503081898632414349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23589883668721265754942899 35384825503081898632414349)
                  ·
                    refine ⟨13269309563655711987155381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35384825503081898632414349 13269309563655711987155381)
                    ·
                      refine ⟨1243997771592722998795817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13269309563655711987155381 1243997771592722998795817)
                      ·
                        rfl

theorem cell23_2422677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_2422677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422677 prefixEnd_2422677 := by exact prefixLift 2422677
  have htrace : WordTrace (prefixWord ++ tailWord_2422677) baseStart_2422677 baseEnd_2422677 := by
    simpa [prefixWord, tailWord_2422677, baseEnd_2422677] using wordTrace_append hprefix tailTrace_2422677
  have hstable : (prefixWord ++ tailWord_2422677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422677).length < 2 ^ (prefixWord ++ tailWord_2422677).sum := by decide
  have hdescent : baseEnd_2422677 < baseStart_2422677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422684 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_2422684 : Nat := 118140960795 + 2422684 * 2 ^ 59
def prefixEnd_2422684 : Nat := 4983230072969 + 3 ^ 40 * 2422684 * 2
def baseEnd_2422684 : Nat := 414667121985768157136095

theorem tailTrace_2422684 : CollatzResearch.WordTrace tailWord_2422684 prefixEnd_2422684 414667121985768157136095 := by
  unfold tailWord_2422684
  simp only [CollatzResearch.WordTrace]
  refine ⟨44181272377518552165537553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58908363170024736220716737 44181272377518552165537553)
  ·
    refine ⟨33135954283138914124153165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44181272377518552165537553 33135954283138914124153165)
    ·
      refine ⟨12425982856177092796557437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33135954283138914124153165 12425982856177092796557437)
      ·
        refine ⟨4659743571066409798709039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12425982856177092796557437 4659743571066409798709039)
        ·
          refine ⟨6989615356599614698063559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4659743571066409798709039 6989615356599614698063559)
          ·
            refine ⟨10484423034899422047095339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6989615356599614698063559 10484423034899422047095339)
            ·
              refine ⟨15726634552349133070643009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10484423034899422047095339 15726634552349133070643009)
              ·
                refine ⟨11794975914261849802982257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15726634552349133070643009 11794975914261849802982257)
                ·
                  refine ⟨8846231935696387352236693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11794975914261849802982257 8846231935696387352236693)
                  ·
                    refine ⟨414667121985768157136095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8846231935696387352236693 414667121985768157136095)
                    ·
                      rfl

theorem cell23_2422684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_2422684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422684 prefixEnd_2422684 := by exact prefixLift 2422684
  have htrace : WordTrace (prefixWord ++ tailWord_2422684) baseStart_2422684 baseEnd_2422684 := by
    simpa [prefixWord, tailWord_2422684, baseEnd_2422684] using wordTrace_append hprefix tailTrace_2422684
  have hstable : (prefixWord ++ tailWord_2422684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422684).length < 2 ^ (prefixWord ++ tailWord_2422684).sum := by decide
  have hdescent : baseEnd_2422684 < baseStart_2422684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422702 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3]
def baseStart_2422702 : Nat := 118140960795 + 2422702 * 2 ^ 59
def prefixEnd_2422702 : Nat := 4983230072969 + 3 ^ 40 * 2422702 * 2
def baseEnd_2422702 : Nat := 1244010608609085400983203

theorem tailTrace_2422702 : CollatzResearch.WordTrace tailWord_2422702 prefixEnd_2422702 1244010608609085400983203 := by
  unfold tailWord_2422702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11045400158621486675653795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58908800845981262270153573 11045400158621486675653795)
  ·
    refine ⟨16568100237932230013480693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11045400158621486675653795 16568100237932230013480693)
    ·
      refine ⟨1553259397306146563763815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16568100237932230013480693 1553259397306146563763815)
      ·
        refine ⟨2329889095959219845645723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553259397306146563763815 2329889095959219845645723)
        ·
          refine ⟨3494833643938829768468585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2329889095959219845645723 3494833643938829768468585)
          ·
            refine ⟨2621125232954122326351439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3494833643938829768468585 2621125232954122326351439)
            ·
              refine ⟨3931687849431183489527159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621125232954122326351439 3931687849431183489527159)
              ·
                refine ⟨5897531774146775234290739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3931687849431183489527159 5897531774146775234290739)
                ·
                  refine ⟨8846297661220162851436109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5897531774146775234290739 8846297661220162851436109)
                  ·
                    refine ⟨3317361622957561069288541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8846297661220162851436109 3317361622957561069288541)
                    ·
                      refine ⟨1244010608609085400983203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3317361622957561069288541 1244010608609085400983203)
                      ·
                        rfl

theorem cell23_2422702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_2422702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422702 prefixEnd_2422702 := by exact prefixLift 2422702
  have htrace : WordTrace (prefixWord ++ tailWord_2422702) baseStart_2422702 baseEnd_2422702 := by
    simpa [prefixWord, tailWord_2422702, baseEnd_2422702] using wordTrace_append hprefix tailTrace_2422702
  have hstable : (prefixWord ++ tailWord_2422702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422702).length < 2 ^ (prefixWord ++ tailWord_2422702).sum := by decide
  have hdescent : baseEnd_2422702 < baseStart_2422702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422744 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_2422744 : Nat := 118140960795 + 2422744 * 2 ^ 59
def prefixEnd_2422744 : Nat := 4983230072969 + 3 ^ 40 * 2422744 * 2
def baseEnd_2422744 : Nat := 414677391598858078886003

theorem tailTrace_2422744 : CollatzResearch.WordTrace tailWord_2422744 prefixEnd_2422744 414677391598858078886003 := by
  unfold tailWord_2422744
  simp only [CollatzResearch.WordTrace]
  refine ⟨44182366567409867289129643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58909822089879823052172857 44182366567409867289129643)
  ·
    refine ⟨66273549851114800933694465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44182366567409867289129643 66273549851114800933694465)
    ·
      refine ⟨49705162388336100700270849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66273549851114800933694465 49705162388336100700270849)
      ·
        refine ⟨37278871791252075525203137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49705162388336100700270849 37278871791252075525203137)
        ·
          refine ⟨27959153843439056643902353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37278871791252075525203137 27959153843439056643902353)
          ·
            refine ⟨20969365382579292482926765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27959153843439056643902353 20969365382579292482926765)
            ·
              refine ⟨7863512018467234681097537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20969365382579292482926765 7863512018467234681097537)
              ·
                refine ⟨5897634013850426010823153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7863512018467234681097537 5897634013850426010823153)
                ·
                  refine ⟨4423225510387819508117365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5897634013850426010823153 4423225510387819508117365)
                  ·
                    refine ⟨414677391598858078886003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4423225510387819508117365 414677391598858078886003)
                    ·
                      rfl

theorem cell23_2422744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_2422744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422744 prefixEnd_2422744 := by exact prefixLift 2422744
  have htrace : WordTrace (prefixWord ++ tailWord_2422744) baseStart_2422744 baseEnd_2422744 := by
    simpa [prefixWord, tailWord_2422744, baseEnd_2422744] using wordTrace_append hprefix tailTrace_2422744
  have hstable : (prefixWord ++ tailWord_2422744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422744).length < 2 ^ (prefixWord ++ tailWord_2422744).sum := by decide
  have hdescent : baseEnd_2422744 < baseStart_2422744 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422759 : List Nat := [1, 1, 5, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2422759 : Nat := 118140960795 + 2422759 * 2 ^ 59
def prefixEnd_2422759 : Nat := 4983230072969 + 3 ^ 40 * 2422759 * 2
def baseEnd_2422759 : Nat := 1244039877006391677970441

theorem tailTrace_2422759 : CollatzResearch.WordTrace tailWord_2422759 prefixEnd_2422759 1244039877006391677970441 := by
  unfold tailWord_2422759
  simp only [CollatzResearch.WordTrace]
  refine ⟨88365280229765392140055331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58910186819843594760036887 88365280229765392140055331)
  ·
    refine ⟨132547920344648088210082997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88365280229765392140055331 132547920344648088210082997)
    ·
      refine ⟨12426367532310758269695281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 132547920344648088210082997 12426367532310758269695281)
      ·
        refine ⟨9319775649233068702271461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12426367532310758269695281 9319775649233068702271461)
        ·
          refine ⟨1747457934231200381675899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9319775649233068702271461 1747457934231200381675899)
          ·
            refine ⟨2621186901346800572513849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747457934231200381675899 2621186901346800572513849)
            ·
              refine ⟨1965890176010100429385387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621186901346800572513849 1965890176010100429385387)
              ·
                refine ⟨2948835264015150644078081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1965890176010100429385387 2948835264015150644078081)
                ·
                  refine ⟨2211626448011362983058561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2948835264015150644078081 2211626448011362983058561)
                  ·
                    refine ⟨1658719836008522237293921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211626448011362983058561 1658719836008522237293921)
                    ·
                      refine ⟨1244039877006391677970441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658719836008522237293921 1244039877006391677970441)
                      ·
                        rfl

theorem cell23_2422759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2422759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422759 prefixEnd_2422759 := by exact prefixLift 2422759
  have htrace : WordTrace (prefixWord ++ tailWord_2422759) baseStart_2422759 baseEnd_2422759 := by
    simpa [prefixWord, tailWord_2422759, baseEnd_2422759] using wordTrace_append hprefix tailTrace_2422759
  have hstable : (prefixWord ++ tailWord_2422759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422759).length < 2 ^ (prefixWord ++ tailWord_2422759).sum := by decide
  have hdescent : baseEnd_2422759 < baseStart_2422759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422787 : List Nat := [1, 1, 1, 3, 2, 1, 1, 3, 10]
def baseStart_2422787 : Nat := 118140960795 + 2422787 * 2 ^ 59
def prefixEnd_2422787 : Nat := 4983230072969 + 3 ^ 40 * 2422787 * 2
def baseEnd_2422787 : Nat := 138228250496079729824479

theorem tailTrace_2422787 : CollatzResearch.WordTrace tailWord_2422787 prefixEnd_2422787 138228250496079729824479 := by
  unfold tailWord_2422787
  simp only [CollatzResearch.WordTrace]
  refine ⟨88366301473663952922074615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58910867649109301948049743 88366301473663952922074615)
  ·
    refine ⟨132549452210495929383111923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88366301473663952922074615 132549452210495929383111923)
    ·
      refine ⟨198824178315743894074667885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132549452210495929383111923 198824178315743894074667885)
      ·
        refine ⟨74559066868403960278000457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 198824178315743894074667885 74559066868403960278000457)
        ·
          refine ⟨55919300151302970208500343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74559066868403960278000457 55919300151302970208500343)
          ·
            refine ⟨83878950226954455312750515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55919300151302970208500343 83878950226954455312750515)
            ·
              refine ⟨125818425340431682969125773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83878950226954455312750515 125818425340431682969125773)
              ·
                refine ⟨47181909502661881113422165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 125818425340431682969125773 47181909502661881113422165)
                ·
                  refine ⟨138228250496079729824479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 47181909502661881113422165 138228250496079729824479)
                  ·
                    rfl

theorem cell23_2422787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 3, 10].length) (baseStart_2422787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422787 prefixEnd_2422787 := by exact prefixLift 2422787
  have htrace : WordTrace (prefixWord ++ tailWord_2422787) baseStart_2422787 baseEnd_2422787 := by
    simpa [prefixWord, tailWord_2422787, baseEnd_2422787] using wordTrace_append hprefix tailTrace_2422787
  have hstable : (prefixWord ++ tailWord_2422787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422787).length < 2 ^ (prefixWord ++ tailWord_2422787).sum := by decide
  have hdescent : baseEnd_2422787 < baseStart_2422787 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422808 : List Nat := [2, 1, 2, 3, 2, 1, 3, 4, 1, 4]
def baseStart_2422808 : Nat := 118140960795 + 2422808 * 2 ^ 59
def prefixEnd_2422808 : Nat := 4983230072969 + 3 ^ 40 * 2422808 * 2
def baseEnd_2422808 : Nat := 414688345852820662085905

theorem tailTrace_2422808 : CollatzResearch.WordTrace tailWord_2422808 prefixEnd_2422808 414688345852820662085905 := by
  unfold tailWord_2422808
  simp only [CollatzResearch.WordTrace]
  refine ⟨44183533703293936754294539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58911378271058582339059385 44183533703293936754294539)
  ·
    refine ⟨66275300554940905131441809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44183533703293936754294539 66275300554940905131441809)
    ·
      refine ⟨49706475416205678848581357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66275300554940905131441809 49706475416205678848581357)
      ·
        refine ⟨18639928281077129568218009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49706475416205678848581357 18639928281077129568218009)
        ·
          refine ⟨13979946210807847176163507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18639928281077129568218009 13979946210807847176163507)
          ·
            refine ⟨20969919316211770764245261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13979946210807847176163507 20969919316211770764245261)
            ·
              refine ⟨7863719743579414036591973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20969919316211770764245261 7863719743579414036591973)
              ·
                refine ⟨1474447451921140131860995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7863719743579414036591973 1474447451921140131860995)
                ·
                  refine ⟨2211671177881710197791493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474447451921140131860995 2211671177881710197791493)
                  ·
                    refine ⟨414688345852820662085905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211671177881710197791493 414688345852820662085905)
                    ·
                      rfl

theorem cell23_2422808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_2422808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422808 prefixEnd_2422808 := by exact prefixLift 2422808
  have htrace : WordTrace (prefixWord ++ tailWord_2422808) baseStart_2422808 baseEnd_2422808 := by
    simpa [prefixWord, tailWord_2422808, baseEnd_2422808] using wordTrace_append hprefix tailTrace_2422808
  have hstable : (prefixWord ++ tailWord_2422808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422808).length < 2 ^ (prefixWord ++ tailWord_2422808).sum := by decide
  have hdescent : baseEnd_2422808 < baseStart_2422808 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422908 : List Nat := [2, 2, 2, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_2422908 : Nat := 118140960795 + 2422908 * 2 ^ 59
def prefixEnd_2422908 : Nat := 4983230072969 + 3 ^ 40 * 2422908 * 2
def baseEnd_2422908 : Nat := 1244116385623911595007255

theorem tailTrace_2422908 : CollatzResearch.WordTrace tailWord_2422908 prefixEnd_2422908 1244116385623911595007255 := by
  unfold tailWord_2422908
  simp only [CollatzResearch.WordTrace]
  refine ⟨44185357353112795293614689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58913809804150393724819585 44185357353112795293614689)
  ·
    refine ⟨33139018014834596470211017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44185357353112795293614689 33139018014834596470211017)
    ·
      refine ⟨24854263511125947352658263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33139018014834596470211017 24854263511125947352658263)
      ·
        refine ⟨37281395266688921028987395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24854263511125947352658263 37281395266688921028987395)
        ·
          refine ⟨55922092900033381543481093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37281395266688921028987395 55922092900033381543481093)
          ·
            refine ⟨10485392418756259039402705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55922092900033381543481093 10485392418756259039402705)
            ·
              refine ⟨7864044314067194279552029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10485392418756259039402705 7864044314067194279552029)
              ·
                refine ⟨2949016617775197854832011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7864044314067194279552029 2949016617775197854832011)
                ·
                  refine ⟨4423524926662796782248017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949016617775197854832011 4423524926662796782248017)
                  ·
                    refine ⟨3317643694997097586686013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4423524926662796782248017 3317643694997097586686013)
                    ·
                      refine ⟨1244116385623911595007255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3317643694997097586686013 1244116385623911595007255)
                      ·
                        rfl

theorem cell23_2422908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_2422908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422908 prefixEnd_2422908 := by exact prefixLift 2422908
  have htrace : WordTrace (prefixWord ++ tailWord_2422908) baseStart_2422908 baseEnd_2422908 := by
    simpa [prefixWord, tailWord_2422908, baseEnd_2422908] using wordTrace_append hprefix tailTrace_2422908
  have hstable : (prefixWord ++ tailWord_2422908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422908).length < 2 ^ (prefixWord ++ tailWord_2422908).sum := by decide
  have hdescent : baseEnd_2422908 < baseStart_2422908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422922 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2]
def baseStart_2422922 : Nat := 118140960795 + 2422922 * 2 ^ 59
def prefixEnd_2422922 : Nat := 4983230072969 + 3 ^ 40 * 2422922 * 2
def baseEnd_2422922 : Nat := 1244123574353074540232191

theorem tailTrace_2422922 : CollatzResearch.WordTrace tailWord_2422922 prefixEnd_2422922 1244123574353074540232191 := by
  unfold tailWord_2422922
  simp only [CollatzResearch.WordTrace]
  refine ⟨22092806332043717744559755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58914150218783247318826013 22092806332043717744559755)
  ·
    refine ⟨33139209498065576616839633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22092806332043717744559755 33139209498065576616839633)
    ·
      refine ⟨24854407123549182462629725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33139209498065576616839633 24854407123549182462629725)
      ·
        refine ⟨9320402671330943423486147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24854407123549182462629725 9320402671330943423486147)
        ·
          refine ⟨13980604006996415135229221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9320402671330943423486147 13980604006996415135229221)
          ·
            refine ⟨2621363251311827837855479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13980604006996415135229221 2621363251311827837855479)
            ·
              refine ⟨3932044876967741756783219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621363251311827837855479 3932044876967741756783219)
              ·
                refine ⟨5898067315451612635174829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3932044876967741756783219 5898067315451612635174829)
                ·
                  refine ⟨2211775243294354738190561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5898067315451612635174829 2211775243294354738190561)
                  ·
                    refine ⟨1658831432470766053642921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2211775243294354738190561 1658831432470766053642921)
                    ·
                      refine ⟨1244123574353074540232191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658831432470766053642921 1244123574353074540232191)
                      ·
                        rfl

theorem cell23_2422922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_2422922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422922 prefixEnd_2422922 := by exact prefixLift 2422922
  have htrace : WordTrace (prefixWord ++ tailWord_2422922) baseStart_2422922 baseEnd_2422922 := by
    simpa [prefixWord, tailWord_2422922, baseEnd_2422922] using wordTrace_append hprefix tailTrace_2422922
  have hstable : (prefixWord ++ tailWord_2422922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422922).length < 2 ^ (prefixWord ++ tailWord_2422922).sum := by decide
  have hdescent : baseEnd_2422922 < baseStart_2422922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422931 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 2, 7, 2]
def baseStart_2422931 : Nat := 118140960795 + 2422931 * 2 ^ 59
def prefixEnd_2422931 : Nat := 4983230072969 + 3 ^ 40 * 2422931 * 2
def baseEnd_2422931 : Nat := 1244128195678965005019649

theorem tailTrace_2422931 : CollatzResearch.WordTrace tailWord_2422931 prefixEnd_2422931 1244128195678965005019649 := by
  unfold tailWord_2422931
  simp only [CollatzResearch.WordTrace]
  refine ⟨88371553585142265515316647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58914369056761510343544431 88371553585142265515316647)
  ·
    refine ⟨132557330377713398272974971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88371553585142265515316647 132557330377713398272974971)
    ·
      refine ⟨198835995566570097409462457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132557330377713398272974971 198835995566570097409462457)
      ·
        refine ⟨149126996674927573057096843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198835995566570097409462457 149126996674927573057096843)
        ·
          refine ⟨223690495012391359585645265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149126996674927573057096843 223690495012391359585645265)
          ·
            refine ⟨167767871259293519689233949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223690495012391359585645265 167767871259293519689233949)
            ·
              refine ⟨62912951722235069883462731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167767871259293519689233949 62912951722235069883462731)
              ·
                refine ⟨94369427583352604825194097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62912951722235069883462731 94369427583352604825194097)
                ·
                  refine ⟨70777070687514453618895573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94369427583352604825194097 70777070687514453618895573)
                  ·
                    refine ⟨1658837594238620006692865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 70777070687514453618895573 1658837594238620006692865)
                    ·
                      refine ⟨1244128195678965005019649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658837594238620006692865 1244128195678965005019649)
                      ·
                        rfl

theorem cell23_2422931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 7, 2].length) (baseStart_2422931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422931 prefixEnd_2422931 := by exact prefixLift 2422931
  have htrace : WordTrace (prefixWord ++ tailWord_2422931) baseStart_2422931 baseEnd_2422931 := by
    simpa [prefixWord, tailWord_2422931, baseEnd_2422931] using wordTrace_append hprefix tailTrace_2422931
  have hstable : (prefixWord ++ tailWord_2422931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422931).length < 2 ^ (prefixWord ++ tailWord_2422931).sum := by decide
  have hdescent : baseEnd_2422931 < baseStart_2422931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422932 : List Nat := [2, 4, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_2422932 : Nat := 118140960795 + 2422932 * 2 ^ 59
def prefixEnd_2422932 : Nat := 4983230072969 + 3 ^ 40 * 2422932 * 2
def baseEnd_2422932 : Nat := 414709569719873167035715

theorem tailTrace_2422932 : CollatzResearch.WordTrace tailWord_2422932 prefixEnd_2422932 414709569719873167035715 := by
  unfold tailWord_2422932
  simp only [CollatzResearch.WordTrace]
  refine ⟨44185795029069321343051525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58914393372092428457402033 44185795029069321343051525)
  ·
    refine ⟨8284836567950497751822161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44185795029069321343051525 8284836567950497751822161)
    ·
      refine ⟨6213627425962873313866621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8284836567950497751822161 6213627425962873313866621)
      ·
        refine ⟨2330110284736077492699983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6213627425962873313866621 2330110284736077492699983)
        ·
          refine ⟨3495165427104116239049975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330110284736077492699983 3495165427104116239049975)
          ·
            refine ⟨5242748140656174358574963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495165427104116239049975 5242748140656174358574963)
            ·
              refine ⟨7864122210984261537862445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5242748140656174358574963 7864122210984261537862445)
              ·
                refine ⟨2949045829119098076698417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7864122210984261537862445 2949045829119098076698417)
                ·
                  refine ⟨2211784371839323557523813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2949045829119098076698417 2211784371839323557523813)
                  ·
                    refine ⟨414709569719873167035715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211784371839323557523813 414709569719873167035715)
                    ·
                      rfl

theorem cell23_2422932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_2422932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422932 prefixEnd_2422932 := by exact prefixLift 2422932
  have htrace : WordTrace (prefixWord ++ tailWord_2422932) baseStart_2422932 baseEnd_2422932 := by
    simpa [prefixWord, tailWord_2422932, baseEnd_2422932] using wordTrace_append hprefix tailTrace_2422932
  have hstable : (prefixWord ++ tailWord_2422932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422932).length < 2 ^ (prefixWord ++ tailWord_2422932).sum := by decide
  have hdescent : baseEnd_2422932 < baseStart_2422932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422972 : List Nat := [2, 2, 2, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2422972 : Nat := 118140960795 + 2422972 * 2 ^ 59
def prefixEnd_2422972 : Nat := 4983230072969 + 3 ^ 40 * 2422972 * 2
def baseEnd_2422972 : Nat := 1244149248385799344606961

theorem tailTrace_2422972 : CollatzResearch.WordTrace tailWord_2422972 prefixEnd_2422972 1244149248385799344606961 := by
  unfold tailWord_2422972
  simp only [CollatzResearch.WordTrace]
  refine ⟨44186524488996864758779585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58915365985329153011706113 44186524488996864758779585)
  ·
    refine ⟨33139893366747648569084689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44186524488996864758779585 33139893366747648569084689)
    ·
      refine ⟨24854920025060736426813517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33139893366747648569084689 24854920025060736426813517)
      ·
        refine ⟨9320595009397776160055069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24854920025060736426813517 9320595009397776160055069)
        ·
          refine ⟨3495223128524166060020651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9320595009397776160055069 3495223128524166060020651)
          ·
            refine ⟨5242834692786249090030977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3495223128524166060020651 5242834692786249090030977)
            ·
              refine ⟨3932126019589686817523233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5242834692786249090030977 3932126019589686817523233)
              ·
                refine ⟨2949094514692265113142425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3932126019589686817523233 2949094514692265113142425)
                ·
                  refine ⟨2211820886019198834856819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2949094514692265113142425 2211820886019198834856819)
                  ·
                    refine ⟨3317731329028798252285229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2211820886019198834856819 3317731329028798252285229)
                    ·
                      refine ⟨1244149248385799344606961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3317731329028798252285229 1244149248385799344606961)
                      ·
                        rfl

theorem cell23_2422972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2422972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422972 prefixEnd_2422972 := by exact prefixLift 2422972
  have htrace : WordTrace (prefixWord ++ tailWord_2422972) baseStart_2422972 baseEnd_2422972 := by
    simpa [prefixWord, tailWord_2422972, baseEnd_2422972] using wordTrace_append hprefix tailTrace_2422972
  have hstable : (prefixWord ++ tailWord_2422972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422972).length < 2 ^ (prefixWord ++ tailWord_2422972).sum := by decide
  have hdescent : baseEnd_2422972 < baseStart_2422972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422981 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 3]
def baseStart_2422981 : Nat := 118140960795 + 2422981 * 2 ^ 59
def prefixEnd_2422981 : Nat := 4983230072969 + 3 ^ 40 * 2422981 * 2
def baseEnd_2422981 : Nat := 1244153869711689809394419

theorem tailTrace_2422981 : CollatzResearch.WordTrace tailWord_2422981 prefixEnd_2422981 1244153869711689809394419 := by
  unfold tailWord_2422981
  simp only [CollatzResearch.WordTrace]
  refine ⟨88373377234961124054636797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58915584823307416036424531 88373377234961124054636797)
  ·
    refine ⟨33140016463110421520488799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88373377234961124054636797 33140016463110421520488799)
    ·
      refine ⟨49710024694665632280733199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33140016463110421520488799 49710024694665632280733199)
      ·
        refine ⟨74565037041998448421099799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49710024694665632280733199 74565037041998448421099799)
        ·
          refine ⟨111847555562997672631649699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74565037041998448421099799 111847555562997672631649699)
          ·
            refine ⟨167771333344496508947474549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111847555562997672631649699 167771333344496508947474549)
            ·
              refine ⟨15728562501046547713825739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167771333344496508947474549 15728562501046547713825739)
              ·
                refine ⟨23592843751569821570738609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15728562501046547713825739 23592843751569821570738609)
                ·
                  refine ⟨17694632813677366178053957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23592843751569821570738609 17694632813677366178053957)
                  ·
                    refine ⟨3317743652564506158385117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17694632813677366178053957 3317743652564506158385117)
                    ·
                      refine ⟨1244153869711689809394419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3317743652564506158385117 1244153869711689809394419)
                      ·
                        rfl

theorem cell23_2422981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 4, 3].length) (baseStart_2422981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422981 prefixEnd_2422981 := by exact prefixLift 2422981
  have htrace : WordTrace (prefixWord ++ tailWord_2422981) baseStart_2422981 baseEnd_2422981 := by
    simpa [prefixWord, tailWord_2422981, baseEnd_2422981] using wordTrace_append hprefix tailTrace_2422981
  have hstable : (prefixWord ++ tailWord_2422981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422981).length < 2 ^ (prefixWord ++ tailWord_2422981).sum := by decide
  have hdescent : baseEnd_2422981 < baseStart_2422981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2422991 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_2422991 : Nat := 118140960795 + 2422991 * 2 ^ 59
def prefixEnd_2422991 : Nat := 4983230072969 + 3 ^ 40 * 2422991 * 2
def baseEnd_2422991 : Nat := 1244159004518234770269373

theorem tailTrace_2422991 : CollatzResearch.WordTrace tailWord_2422991 prefixEnd_2422991 1244159004518234770269373 := by
  unfold tailWord_2422991
  simp only [CollatzResearch.WordTrace]
  refine ⟨88373741964924895762500827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58915827976616597175000551 88373741964924895762500827)
  ·
    refine ⟨132560612947387343643751241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88373741964924895762500827 132560612947387343643751241)
    ·
      refine ⟨99420459710540507732813431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132560612947387343643751241 99420459710540507732813431)
      ·
        refine ⟨149130689565810761599220147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99420459710540507732813431 149130689565810761599220147)
        ·
          refine ⟨223696034348716142398830221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149130689565810761599220147 223696034348716142398830221)
          ·
            refine ⟨83886012880768553399561333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223696034348716142398830221 83886012880768553399561333)
            ·
              refine ⟨7864313707572051881208875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 83886012880768553399561333 7864313707572051881208875)
              ·
                refine ⟨11796470561358077821813313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7864313707572051881208875 11796470561358077821813313)
                ·
                  refine ⟨8847352921018558366359985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11796470561358077821813313 8847352921018558366359985)
                  ·
                    refine ⟨6635514690763918774769989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8847352921018558366359985 6635514690763918774769989)
                    ·
                      refine ⟨1244159004518234770269373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6635514690763918774769989 1244159004518234770269373)
                      ·
                        rfl

theorem cell23_2422991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_2422991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2422991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2422991 prefixEnd_2422991 := by exact prefixLift 2422991
  have htrace : WordTrace (prefixWord ++ tailWord_2422991) baseStart_2422991 baseEnd_2422991 := by
    simpa [prefixWord, tailWord_2422991, baseEnd_2422991] using wordTrace_append hprefix tailTrace_2422991
  have hstable : (prefixWord ++ tailWord_2422991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2422991).length < 2 ^ (prefixWord ++ tailWord_2422991).sum := by decide
  have hdescent : baseEnd_2422991 < baseStart_2422991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2422991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423041 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_2423041 : Nat := 118140960795 + 2423041 * 2 ^ 59
def prefixEnd_2423041 : Nat := 4983230072969 + 3 ^ 40 * 2423041 * 2
def baseEnd_2423041 : Nat := 1244184678550959574644143

theorem tailTrace_2423041 : CollatzResearch.WordTrace tailWord_2423041 prefixEnd_2423041 1244184678550959574644143 := by
  unfold tailWord_2423041
  simp only [CollatzResearch.WordTrace]
  refine ⟨88375565614743754301820977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58917043743162502867880651 88375565614743754301820977)
  ·
    refine ⟨66281674211057815726365733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88375565614743754301820977 66281674211057815726365733)
    ·
      refine ⟨12427813914573340448693575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66281674211057815726365733 12427813914573340448693575)
      ·
        refine ⟨18641720871860010673040363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12427813914573340448693575 18641720871860010673040363)
        ·
          refine ⟨27962581307790016009560545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18641720871860010673040363 27962581307790016009560545)
          ·
            refine ⟨20971935980842512007170409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27962581307790016009560545 20971935980842512007170409)
            ·
              refine ⟨15728951985631884005377807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20971935980842512007170409 15728951985631884005377807)
              ·
                refine ⟨23593427978447826008066711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15728951985631884005377807 23593427978447826008066711)
                ·
                  refine ⟨35390141967671739012100067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23593427978447826008066711 35390141967671739012100067)
                  ·
                    refine ⟨53085212951507608518150101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35390141967671739012100067 53085212951507608518150101)
                    ·
                      refine ⟨1244184678550959574644143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53085212951507608518150101 1244184678550959574644143)
                      ·
                        rfl

theorem cell23_2423041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_2423041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423041 prefixEnd_2423041 := by exact prefixLift 2423041
  have htrace : WordTrace (prefixWord ++ tailWord_2423041) baseStart_2423041 baseEnd_2423041 := by
    simpa [prefixWord, tailWord_2423041, baseEnd_2423041] using wordTrace_append hprefix tailTrace_2423041
  have hstable : (prefixWord ++ tailWord_2423041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423041).length < 2 ^ (prefixWord ++ tailWord_2423041).sum := by decide
  have hdescent : baseEnd_2423041 < baseStart_2423041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423051 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4]
def baseStart_2423051 : Nat := 118140960795 + 2423051 * 2 ^ 59
def prefixEnd_2423051 : Nat := 4983230072969 + 3 ^ 40 * 2423051 * 2
def baseEnd_2423051 : Nat := 1244189813357504535519097

theorem tailTrace_2423051 : CollatzResearch.WordTrace tailWord_2423051 prefixEnd_2423051 1244189813357504535519097 := by
  unfold tailWord_2423051
  simp only [CollatzResearch.WordTrace]
  refine ⟨88375930344707526009685007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58917286896471684006456671 88375930344707526009685007)
  ·
    refine ⟨132563895517061289014527511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88375930344707526009685007 132563895517061289014527511)
    ·
      refine ⟨198845843275591933521791267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132563895517061289014527511 198845843275591933521791267)
      ·
        refine ⟨298268764913387900282686901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198845843275591933521791267 298268764913387900282686901)
        ·
          refine ⟨27962696710630115651501897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 298268764913387900282686901 27962696710630115651501897)
          ·
            refine ⟨20972022532972586738626423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27962696710630115651501897 20972022532972586738626423)
            ·
              refine ⟨31458033799458880107939635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20972022532972586738626423 31458033799458880107939635)
              ·
                refine ⟨47187050699188320161909453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31458033799458880107939635 47187050699188320161909453)
                ·
                  refine ⟨17695144012195620060716045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47187050699188320161909453 17695144012195620060716045)
                  ·
                    refine ⟨6635679004573357522768517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17695144012195620060716045 6635679004573357522768517)
                    ·
                      refine ⟨1244189813357504535519097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6635679004573357522768517 1244189813357504535519097)
                      ·
                        rfl

theorem cell23_2423051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_2423051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423051 prefixEnd_2423051 := by exact prefixLift 2423051
  have htrace : WordTrace (prefixWord ++ tailWord_2423051) baseStart_2423051 baseEnd_2423051 := by
    simpa [prefixWord, tailWord_2423051, baseEnd_2423051] using wordTrace_append hprefix tailTrace_2423051
  have hstable : (prefixWord ++ tailWord_2423051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423051).length < 2 ^ (prefixWord ++ tailWord_2423051).sum := by decide
  have hdescent : baseEnd_2423051 < baseStart_2423051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423068 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_2423068 : Nat := 118140960795 + 2423068 * 2 ^ 59
def prefixEnd_2423068 : Nat := 4983230072969 + 3 ^ 40 * 2423068 * 2
def baseEnd_2423068 : Nat := 1244198542528630969006519

theorem tailTrace_2423068 : CollatzResearch.WordTrace tailWord_2423068 prefixEnd_2423068 1244198542528630969006519 := by
  unfold tailWord_2423068
  simp only [CollatzResearch.WordTrace]
  refine ⟨44188275192822968956526929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58917700257097291942035905 44188275192822968956526929)
  ·
    refine ⟨33141206394617226717395197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44188275192822968956526929 33141206394617226717395197)
    ·
      refine ⟨12427952397981460019023199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33141206394617226717395197 12427952397981460019023199)
      ·
        refine ⟨18641928596972190028534799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12427952397981460019023199 18641928596972190028534799)
        ·
          refine ⟨27962892895458285042802199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18641928596972190028534799 27962892895458285042802199)
          ·
            refine ⟨41944339343187427564203299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27962892895458285042802199 41944339343187427564203299)
            ·
              refine ⟨62916509014781141346304949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41944339343187427564203299 62916509014781141346304949)
              ·
                refine ⟨5898422720135732001216089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 62916509014781141346304949 5898422720135732001216089)
                ·
                  refine ⟨4423817040101799000912067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5898422720135732001216089 4423817040101799000912067)
                  ·
                    refine ⟨6635725560152698501368101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4423817040101799000912067 6635725560152698501368101)
                    ·
                      refine ⟨1244198542528630969006519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6635725560152698501368101 1244198542528630969006519)
                      ·
                        rfl

theorem cell23_2423068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_2423068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423068 prefixEnd_2423068 := by exact prefixLift 2423068
  have htrace : WordTrace (prefixWord ++ tailWord_2423068) baseStart_2423068 baseEnd_2423068 := by
    simpa [prefixWord, tailWord_2423068, baseEnd_2423068] using wordTrace_append hprefix tailTrace_2423068
  have hstable : (prefixWord ++ tailWord_2423068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423068).length < 2 ^ (prefixWord ++ tailWord_2423068).sum := by decide
  have hdescent : baseEnd_2423068 < baseStart_2423068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423069 : List Nat := [1, 4, 2, 3, 3, 1, 1, 3, 5]
def baseStart_2423069 : Nat := 118140960795 + 2423069 * 2 ^ 59
def prefixEnd_2423069 : Nat := 4983230072969 + 3 ^ 40 * 2423069 * 2
def baseEnd_2423069 : Nat := 138244339556587273899335

theorem tailTrace_2423069 : CollatzResearch.WordTrace tailWord_2423069 prefixEnd_2423069 138244339556587273899335 := by
  unfold tailWord_2423069
  simp only [CollatzResearch.WordTrace]
  refine ⟨88376586858642315083840261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58917724572428210055893507 88376586858642315083840261)
  ·
    refine ⟨16570610035995434078220049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88376586858642315083840261 16570610035995434078220049)
    ·
      refine ⟨12427957526996575558665037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16570610035995434078220049 12427957526996575558665037)
      ·
        refine ⟨4660484072623715834499389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12427957526996575558665037 4660484072623715834499389)
        ·
          refine ⟨1747681527233893437937271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4660484072623715834499389 1747681527233893437937271)
          ·
            refine ⟨2621522290850840156905907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1747681527233893437937271 2621522290850840156905907)
            ·
              refine ⟨3932283436276260235358861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621522290850840156905907 3932283436276260235358861)
              ·
                refine ⟨1474606288603597588259573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3932283436276260235358861 1474606288603597588259573)
                ·
                  refine ⟨138244339556587273899335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1474606288603597588259573 138244339556587273899335)
                  ·
                    rfl

theorem cell23_2423069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_2423069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423069 prefixEnd_2423069 := by exact prefixLift 2423069
  have htrace : WordTrace (prefixWord ++ tailWord_2423069) baseStart_2423069 baseEnd_2423069 := by
    simpa [prefixWord, tailWord_2423069, baseEnd_2423069] using wordTrace_append hprefix tailTrace_2423069
  have hstable : (prefixWord ++ tailWord_2423069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423069).length < 2 ^ (prefixWord ++ tailWord_2423069).sum := by decide
  have hdescent : baseEnd_2423069 < baseStart_2423069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423091 : List Nat := [1, 1, 1, 2, 5, 1, 1, 3, 8]
def baseStart_2423091 : Nat := 118140960795 + 2423091 * 2 ^ 59
def prefixEnd_2423091 : Nat := 4983230072969 + 3 ^ 40 * 2423091 * 2
def baseEnd_2423091 : Nat := 138245594731520486557657

theorem tailTrace_2423091 : CollatzResearch.WordTrace tailWord_2423091 prefixEnd_2423091 138245594731520486557657 := by
  unfold tailWord_2423091
  simp only [CollatzResearch.WordTrace]
  refine ⟨88377389264562612841141127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58918259509708408560760751 88377389264562612841141127)
  ·
    refine ⟨132566083896843919261711691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88377389264562612841141127 132566083896843919261711691)
    ·
      refine ⟨198849125845265878892567537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132566083896843919261711691 198849125845265878892567537)
      ·
        refine ⟨149136844383949409169425653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198849125845265878892567537 149136844383949409169425653)
        ·
          refine ⟨13981579160995257109633655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 149136844383949409169425653 13981579160995257109633655)
          ·
            refine ⟨20972368741492885664450483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13981579160995257109633655 20972368741492885664450483)
            ·
              refine ⟨31458553112239328496675725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20972368741492885664450483 31458553112239328496675725)
              ·
                refine ⟨11796957417089748186253397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31458553112239328496675725 11796957417089748186253397)
                ·
                  refine ⟨138245594731520486557657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 11796957417089748186253397 138245594731520486557657)
                  ·
                    rfl

theorem cell23_2423091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 3, 8].length) (baseStart_2423091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423091 prefixEnd_2423091 := by exact prefixLift 2423091
  have htrace : WordTrace (prefixWord ++ tailWord_2423091) baseStart_2423091 baseEnd_2423091 := by
    simpa [prefixWord, tailWord_2423091, baseEnd_2423091] using wordTrace_append hprefix tailTrace_2423091
  have hstable : (prefixWord ++ tailWord_2423091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423091).length < 2 ^ (prefixWord ++ tailWord_2423091).sum := by decide
  have hdescent : baseEnd_2423091 < baseStart_2423091 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423095 : List Nat := [1, 1, 3, 1, 2, 1, 1, 8, 1, 4]
def baseStart_2423095 : Nat := 118140960795 + 2423095 * 2 ^ 59
def prefixEnd_2423095 : Nat := 4983230072969 + 3 ^ 40 * 2423095 * 2
def baseEnd_2423095 : Nat := 414737468835434121122965

theorem tailTrace_2423095 : CollatzResearch.WordTrace tailWord_2423095 prefixEnd_2423095 414737468835434121122965 := by
  unfold tailWord_2423095
  simp only [CollatzResearch.WordTrace]
  refine ⟨88377535156548121524286739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58918356771032081016191159 88377535156548121524286739)
  ·
    refine ⟨132566302734822182286430109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88377535156548121524286739 132566302734822182286430109)
    ·
      refine ⟨49712363525558318357411291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132566302734822182286430109 49712363525558318357411291)
      ·
        refine ⟨74568545288337477536116937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49712363525558318357411291 74568545288337477536116937)
        ·
          refine ⟨55926408966253108152087703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74568545288337477536116937 55926408966253108152087703)
          ·
            refine ⟨83889613449379662228131555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55926408966253108152087703 83889613449379662228131555)
            ·
              refine ⟨125834420174069493342197333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83889613449379662228131555 125834420174069493342197333)
              ·
                refine ⟨1474622111414876875103875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 125834420174069493342197333 1474622111414876875103875)
                ·
                  refine ⟨2211933167122315312655813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474622111414876875103875 2211933167122315312655813)
                  ·
                    refine ⟨414737468835434121122965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211933167122315312655813 414737468835434121122965)
                    ·
                      rfl

theorem cell23_2423095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_2423095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423095 prefixEnd_2423095 := by exact prefixLift 2423095
  have htrace : WordTrace (prefixWord ++ tailWord_2423095) baseStart_2423095 baseEnd_2423095 := by
    simpa [prefixWord, tailWord_2423095, baseEnd_2423095] using wordTrace_append hprefix tailTrace_2423095
  have hstable : (prefixWord ++ tailWord_2423095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423095).length < 2 ^ (prefixWord ++ tailWord_2423095).sum := by decide
  have hdescent : baseEnd_2423095 < baseStart_2423095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423145 : List Nat := [1, 2, 1, 1, 1, 3, 3, 4, 2, 3, 2]
def baseStart_2423145 : Nat := 118140960795 + 2423145 * 2 ^ 59
def prefixEnd_2423145 : Nat := 4983230072969 + 3 ^ 40 * 2423145 * 2
def baseEnd_2423145 : Nat := 1244238080539027167743665

theorem tailTrace_2423145 : CollatzResearch.WordTrace tailWord_2423145 prefixEnd_2423145 1244238080539027167743665 := by
  unfold tailWord_2423145
  simp only [CollatzResearch.WordTrace]
  refine ⟨88379358806366980063606889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58919572537577986709071259 88379358806366980063606889)
  ·
    refine ⟨66284519104775235047705167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88379358806366980063606889 66284519104775235047705167)
    ·
      refine ⟨99426778657162852571557751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66284519104775235047705167 99426778657162852571557751)
      ·
        refine ⟨149140167985744278857336627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99426778657162852571557751 149140167985744278857336627)
        ·
          refine ⟨223710251978616418286004941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149140167985744278857336627 223710251978616418286004941)
          ·
            refine ⟨83891344491981156857251853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 223710251978616418286004941 83891344491981156857251853)
            ·
              refine ⟨31459254184492933821469445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 83891344491981156857251853 31459254184492933821469445)
              ·
                refine ⟨5898610159592425091525521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31459254184492933821469445 5898610159592425091525521)
                ·
                  refine ⟨4423957619694318818644141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5898610159592425091525521 4423957619694318818644141)
                  ·
                    refine ⟨1658984107385369556991553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4423957619694318818644141 1658984107385369556991553)
                    ·
                      refine ⟨1244238080539027167743665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1658984107385369556991553 1244238080539027167743665)
                      ·
                        rfl

theorem cell23_2423145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 4, 2, 3, 2].length) (baseStart_2423145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423145 prefixEnd_2423145 := by exact prefixLift 2423145
  have htrace : WordTrace (prefixWord ++ tailWord_2423145) baseStart_2423145 baseEnd_2423145 := by
    simpa [prefixWord, tailWord_2423145, baseEnd_2423145] using wordTrace_append hprefix tailTrace_2423145
  have hstable : (prefixWord ++ tailWord_2423145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423145).length < 2 ^ (prefixWord ++ tailWord_2423145).sum := by decide
  have hdescent : baseEnd_2423145 < baseStart_2423145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423146 : List Nat := [3, 1, 3, 3, 1, 3, 2, 2, 1, 4]
def baseStart_2423146 : Nat := 118140960795 + 2423146 * 2 ^ 59
def prefixEnd_2423146 : Nat := 4983230072969 + 3 ^ 40 * 2423146 * 2
def baseEnd_2423146 : Nat := 414746198006560554610387

theorem tailTrace_2423146 : CollatzResearch.WordTrace tailWord_2423146 prefixEnd_2423146 414746198006560554610387 := by
  unfold tailWord_2423146
  simp only [CollatzResearch.WordTrace]
  refine ⟨22094848819840839308598323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58919596852908904822928861 22094848819840839308598323)
  ·
    refine ⟨33142273229761258962897485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22094848819840839308598323 33142273229761258962897485)
    ·
      refine ⟨12428352461160472111086557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33142273229761258962897485 12428352461160472111086557)
      ·
        refine ⟨4660632172935177041657459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12428352461160472111086557 4660632172935177041657459)
        ·
          refine ⟨6990948259402765562486189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660632172935177041657459 6990948259402765562486189)
          ·
            refine ⟨2621605597276037085932321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6990948259402765562486189 2621605597276037085932321)
            ·
              refine ⟨1966204197957027814449241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621605597276037085932321 1966204197957027814449241)
              ·
                refine ⟨1474653148467770860836931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966204197957027814449241 1474653148467770860836931)
                ·
                  refine ⟨2211979722701656291255397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474653148467770860836931 2211979722701656291255397)
                  ·
                    refine ⟨414746198006560554610387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211979722701656291255397 414746198006560554610387)
                    ·
                      rfl

theorem cell23_2423146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_2423146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423146 prefixEnd_2423146 := by exact prefixLift 2423146
  have htrace : WordTrace (prefixWord ++ tailWord_2423146) baseStart_2423146 baseEnd_2423146 := by
    simpa [prefixWord, tailWord_2423146, baseEnd_2423146] using wordTrace_append hprefix tailTrace_2423146
  have hstable : (prefixWord ++ tailWord_2423146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423146).length < 2 ^ (prefixWord ++ tailWord_2423146).sum := by decide
  have hdescent : baseEnd_2423146 < baseStart_2423146 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423168 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 8, 4]
def baseStart_2423168 : Nat := 118140960795 + 2423168 * 2 ^ 59
def prefixEnd_2423168 : Nat := 4983230072969 + 3 ^ 40 * 2423168 * 2
def baseEnd_2423168 : Nat := 414749963531360192585353

theorem tailTrace_2423168 : CollatzResearch.WordTrace tailWord_2423168 prefixEnd_2423168 414749963531360192585353 := by
  unfold tailWord_2423168
  simp only [CollatzResearch.WordTrace]
  refine ⟨44190098842641827495847079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58920131790189103327796105 44190098842641827495847079)
  ·
    refine ⟨66285148263962741243770619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44190098842641827495847079 66285148263962741243770619)
    ·
      refine ⟨99427722395944111865655929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66285148263962741243770619 99427722395944111865655929)
      ·
        refine ⟨74570791796958083899241947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99427722395944111865655929 74570791796958083899241947)
        ·
          refine ⟨111856187695437125848862921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74570791796958083899241947 111856187695437125848862921)
          ·
            refine ⟨83892140771577844386647191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111856187695437125848862921 83892140771577844386647191)
            ·
              refine ⟨125838211157366766579970787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83892140771577844386647191 125838211157366766579970787)
              ·
                refine ⟨188757316736050149869956181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125838211157366766579970787 188757316736050149869956181)
                ·
                  refine ⟨2211999805500587693788549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 188757316736050149869956181 2211999805500587693788549)
                  ·
                    refine ⟨414749963531360192585353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2211999805500587693788549 414749963531360192585353)
                    ·
                      rfl

theorem cell23_2423168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_2423168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423168 prefixEnd_2423168 := by exact prefixLift 2423168
  have htrace : WordTrace (prefixWord ++ tailWord_2423168) baseStart_2423168 baseEnd_2423168 := by
    simpa [prefixWord, tailWord_2423168, baseEnd_2423168] using wordTrace_append hprefix tailTrace_2423168
  have hstable : (prefixWord ++ tailWord_2423168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423168).length < 2 ^ (prefixWord ++ tailWord_2423168).sum := by decide
  have hdescent : baseEnd_2423168 < baseStart_2423168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423175 : List Nat := [1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_2423175 : Nat := 118140960795 + 2423175 * 2 ^ 59
def prefixEnd_2423175 : Nat := 4983230072969 + 3 ^ 40 * 2423175 * 2
def baseEnd_2423175 : Nat := 1244253484958662050368527

theorem tailTrace_2423175 : CollatzResearch.WordTrace tailWord_2423175 prefixEnd_2423175 1244253484958662050368527 := by
  unfold tailWord_2423175
  simp only [CollatzResearch.WordTrace]
  refine ⟨88380452996258295187198979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58920301997505530124799319 88380452996258295187198979)
  ·
    refine ⟨132570679494387442780798469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88380452996258295187198979 132570679494387442780798469)
    ·
      refine ⟨24857002405197645521399713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132570679494387442780798469 24857002405197645521399713)
      ·
        refine ⟨18642751803898234141049785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24857002405197645521399713 18642751803898234141049785)
        ·
          refine ⟨13982063852923675605787339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18642751803898234141049785 13982063852923675605787339)
          ·
            refine ⟨20973095779385513408681009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13982063852923675605787339 20973095779385513408681009)
            ·
              refine ⟨15729821834539135056510757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20973095779385513408681009 15729821834539135056510757)
              ·
                refine ⟨2949341593976087823095767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15729821834539135056510757 2949341593976087823095767)
                ·
                  refine ⟨4424012390964131734643651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949341593976087823095767 4424012390964131734643651)
                  ·
                    refine ⟨6636018586446197601965477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4424012390964131734643651 6636018586446197601965477)
                    ·
                      refine ⟨1244253484958662050368527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6636018586446197601965477 1244253484958662050368527)
                      ·
                        rfl

theorem cell23_2423175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_2423175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423175 prefixEnd_2423175 := by exact prefixLift 2423175
  have htrace : WordTrace (prefixWord ++ tailWord_2423175) baseStart_2423175 baseEnd_2423175 := by
    simpa [prefixWord, tailWord_2423175, baseEnd_2423175] using wordTrace_append hprefix tailTrace_2423175
  have hstable : (prefixWord ++ tailWord_2423175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423175).length < 2 ^ (prefixWord ++ tailWord_2423175).sum := by decide
  have hdescent : baseEnd_2423175 < baseStart_2423175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423192 : List Nat := [2, 1, 2, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_2423192 : Nat := 118140960795 + 2423192 * 2 ^ 59
def prefixEnd_2423192 : Nat := 4983230072969 + 3 ^ 40 * 2423192 * 2
def baseEnd_2423192 : Nat := 1244262214129788483855949

theorem tailTrace_2423192 : CollatzResearch.WordTrace tailWord_2423192 prefixEnd_2423192 1244262214129788483855949 := by
  unfold tailWord_2423192
  simp only [CollatzResearch.WordTrace]
  refine ⟨44190536518598353545283915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58920715358131138060378553 44190536518598353545283915)
  ·
    refine ⟨66285804777897530317925873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44190536518598353545283915 66285804777897530317925873)
    ·
      refine ⟨49714353583423147738444405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66285804777897530317925873 49714353583423147738444405)
      ·
        refine ⟨4660720648445920100479163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49714353583423147738444405 4660720648445920100479163)
        ·
          refine ⟨6991080972668880150718745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660720648445920100479163 6991080972668880150718745)
          ·
            refine ⟨5243310729501660113039059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6991080972668880150718745 5243310729501660113039059)
            ·
              refine ⟨7864966094252490169558589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5243310729501660113039059 7864966094252490169558589)
              ·
                refine ⟨2949362285344683813584471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7864966094252490169558589 2949362285344683813584471)
                ·
                  refine ⟨4424043428017025720376707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2949362285344683813584471 4424043428017025720376707)
                  ·
                    refine ⟨6636065142025538580565061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4424043428017025720376707 6636065142025538580565061)
                    ·
                      refine ⟨1244262214129788483855949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6636065142025538580565061 1244262214129788483855949)
                      ·
                        rfl

theorem cell23_2423192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_2423192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423192 prefixEnd_2423192 := by exact prefixLift 2423192
  have htrace : WordTrace (prefixWord ++ tailWord_2423192) baseStart_2423192 baseEnd_2423192 := by
    simpa [prefixWord, tailWord_2423192, baseEnd_2423192] using wordTrace_append hprefix tailTrace_2423192
  have hstable : (prefixWord ++ tailWord_2423192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423192).length < 2 ^ (prefixWord ++ tailWord_2423192).sum := by decide
  have hdescent : baseEnd_2423192 < baseStart_2423192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423288 : List Nat := [2, 1, 2, 1, 1, 4, 2, 1, 9]
def baseStart_2423288 : Nat := 118140960795 + 2423288 * 2 ^ 59
def prefixEnd_2423288 : Nat := 4983230072969 + 3 ^ 40 * 2423288 * 2
def baseEnd_2423288 : Nat := 138256834252513345361723

theorem tailTrace_2423288 : CollatzResearch.WordTrace tailWord_2423288 prefixEnd_2423288 138256834252513345361723 := by
  unfold tailWord_2423288
  simp only [CollatzResearch.WordTrace]
  refine ⟨44192287222424457743031259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58923049629899276990708345 44192287222424457743031259)
  ·
    refine ⟨66288430833636686614546889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44192287222424457743031259 66288430833636686614546889)
    ·
      refine ⟨49716323125227514960910167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66288430833636686614546889 49716323125227514960910167)
      ·
        refine ⟨74574484687841272441365251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49716323125227514960910167 74574484687841272441365251)
        ·
          refine ⟨111861727031761908662047877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74574484687841272441365251 111861727031761908662047877)
          ·
            refine ⟨20974073818455357874133977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111861727031761908662047877 20974073818455357874133977)
            ·
              refine ⟨15730555363841518405600483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20974073818455357874133977 15730555363841518405600483)
              ·
                refine ⟨23595833045762277608400725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15730555363841518405600483 23595833045762277608400725)
                ·
                  refine ⟨138256834252513345361723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 23595833045762277608400725 138256834252513345361723)
                  ·
                    rfl

theorem cell23_2423288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_2423288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423288 prefixEnd_2423288 := by exact prefixLift 2423288
  have htrace : WordTrace (prefixWord ++ tailWord_2423288) baseStart_2423288 baseEnd_2423288 := by
    simpa [prefixWord, tailWord_2423288, baseEnd_2423288] using wordTrace_append hprefix tailTrace_2423288
  have hstable : (prefixWord ++ tailWord_2423288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423288).length < 2 ^ (prefixWord ++ tailWord_2423288).sum := by decide
  have hdescent : baseEnd_2423288 < baseStart_2423288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423315 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 3]
def baseStart_2423315 : Nat := 118140960795 + 2423315 * 2 ^ 59
def prefixEnd_2423315 : Nat := 4983230072969 + 3 ^ 40 * 2423315 * 2
def baseEnd_2423315 : Nat := 1244325372250291502617883

theorem tailTrace_2423315 : CollatzResearch.WordTrace tailWord_2423315 prefixEnd_2423315 1244325372250291502617883 := by
  unfold tailWord_2423315
  simp only [CollatzResearch.WordTrace]
  refine ⟨88385559215751099097295399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58923706143834066064863599 88385559215751099097295399)
  ·
    refine ⟨132578338823626648645943099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88385559215751099097295399 132578338823626648645943099)
    ·
      refine ⟨198867508235439972968914649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132578338823626648645943099 198867508235439972968914649)
      ·
        refine ⟨149150631176579979726685987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 198867508235439972968914649 149150631176579979726685987)
        ·
          refine ⟨223725946764869969590028981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149150631176579979726685987 223725946764869969590028981)
          ·
            refine ⟨20974307509206559649065217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 223725946764869969590028981 20974307509206559649065217)
            ·
              refine ⟨15730730631904919736798913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20974307509206559649065217 15730730631904919736798913)
              ·
                refine ⟨11798047973928689802599185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15730730631904919736798913 11798047973928689802599185)
                ·
                  refine ⟨8848535980446517351949389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11798047973928689802599185 8848535980446517351949389)
                  ·
                    refine ⟨3318200992667444006981021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8848535980446517351949389 3318200992667444006981021)
                    ·
                      refine ⟨1244325372250291502617883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318200992667444006981021 1244325372250291502617883)
                      ·
                        rfl

theorem cell23_2423315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 3].length) (baseStart_2423315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423315 prefixEnd_2423315 := by exact prefixLift 2423315
  have htrace : WordTrace (prefixWord ++ tailWord_2423315) baseStart_2423315 baseEnd_2423315 := by
    simpa [prefixWord, tailWord_2423315, baseEnd_2423315] using wordTrace_append hprefix tailTrace_2423315
  have hstable : (prefixWord ++ tailWord_2423315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423315).length < 2 ^ (prefixWord ++ tailWord_2423315).sum := by decide
  have hdescent : baseEnd_2423315 < baseStart_2423315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423372 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 4, 4, 2]
def baseStart_2423372 : Nat := 118140960795 + 2423372 * 2 ^ 59
def prefixEnd_2423372 : Nat := 4983230072969 + 3 ^ 40 * 2423372 * 2
def baseEnd_2423372 : Nat := 1244354640647597779605121

theorem tailTrace_2423372 : CollatzResearch.WordTrace tailWord_2423372 prefixEnd_2423372 1244354640647597779605121 := by
  unfold tailWord_2423372
  simp only [CollatzResearch.WordTrace]
  refine ⟨44193819088272298916060185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58925092117696398554746913 44193819088272298916060185)
  ·
    refine ⟨33145364316204224187045139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44193819088272298916060185 33145364316204224187045139)
    ·
      refine ⟨49718046474306336280567709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33145364316204224187045139 49718046474306336280567709)
      ·
        refine ⟨18644267427864876105212891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49718046474306336280567709 18644267427864876105212891)
        ·
          refine ⟨27966401141797314157819337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18644267427864876105212891 27966401141797314157819337)
          ·
            refine ⟨20974800856347985618364503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27966401141797314157819337 20974800856347985618364503)
            ·
              refine ⟨31462201284521978427546755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20974800856347985618364503 31462201284521978427546755)
              ·
                refine ⟨47193301926782967641320133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31462201284521978427546755 47193301926782967641320133)
                ·
                  refine ⟨8848744111271806432747525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47193301926782967641320133 8848744111271806432747525)
                  ·
                    refine ⟨1659139520863463706140161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8848744111271806432747525 1659139520863463706140161)
                    ·
                      refine ⟨1244354640647597779605121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659139520863463706140161 1244354640647597779605121)
                      ·
                        rfl

theorem cell23_2423372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_2423372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423372 prefixEnd_2423372 := by exact prefixLift 2423372
  have htrace : WordTrace (prefixWord ++ tailWord_2423372) baseStart_2423372 baseEnd_2423372 := by
    simpa [prefixWord, tailWord_2423372, baseEnd_2423372] using wordTrace_append hprefix tailTrace_2423372
  have hstable : (prefixWord ++ tailWord_2423372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423372).length < 2 ^ (prefixWord ++ tailWord_2423372).sum := by decide
  have hdescent : baseEnd_2423372 < baseStart_2423372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423445 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_2423445 : Nat := 118140960795 + 2423445 * 2 ^ 59
def prefixEnd_2423445 : Nat := 4983230072969 + 3 ^ 40 * 2423445 * 2
def baseEnd_2423445 : Nat := 1244392124735375993992285

theorem tailTrace_2423445 : CollatzResearch.WordTrace tailWord_2423445 prefixEnd_2423445 1244392124735375993992285 := by
  unfold tailWord_2423445
  simp only [CollatzResearch.WordTrace]
  refine ⟨88390300705280131299527789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58926867136853420866351859 88390300705280131299527789)
  ·
    refine ⟨33146362764480049237322921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88390300705280131299527789 33146362764480049237322921)
    ·
      refine ⟨24859772073360036927992191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33146362764480049237322921 24859772073360036927992191)
      ·
        refine ⟨37289658110040055391988287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24859772073360036927992191 37289658110040055391988287)
        ·
          refine ⟨55934487165060083087982431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37289658110040055391988287 55934487165060083087982431)
          ·
            refine ⟨83901730747590124631973647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55934487165060083087982431 83901730747590124631973647)
            ·
              refine ⟨125852596121385186947960471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83901730747590124631973647 125852596121385186947960471)
              ·
                refine ⟨188778894182077780421940707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125852596121385186947960471 188778894182077780421940707)
                ·
                  refine ⟨283168341273116670632911061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188778894182077780421940707 283168341273116670632911061)
                  ·
                    refine ⟨6636757998588671967958853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 283168341273116670632911061 6636757998588671967958853)
                    ·
                      refine ⟨1244392124735375993992285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6636757998588671967958853 1244392124735375993992285)
                      ·
                        rfl

theorem cell23_2423445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_2423445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423445 prefixEnd_2423445 := by exact prefixLift 2423445
  have htrace : WordTrace (prefixWord ++ tailWord_2423445) baseStart_2423445 baseEnd_2423445 := by
    simpa [prefixWord, tailWord_2423445, baseEnd_2423445] using wordTrace_append hprefix tailTrace_2423445
  have hstable : (prefixWord ++ tailWord_2423445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423445).length < 2 ^ (prefixWord ++ tailWord_2423445).sum := by decide
  have hdescent : baseEnd_2423445 < baseStart_2423445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423465 : List Nat := [1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 5]
def baseStart_2423465 : Nat := 118140960795 + 2423465 * 2 ^ 59
def prefixEnd_2423465 : Nat := 4983230072969 + 3 ^ 40 * 2423465 * 2
def baseEnd_2423465 : Nat := 1244402394348465915742193

theorem tailTrace_2423465 : CollatzResearch.WordTrace tailWord_2423465 prefixEnd_2423465 1244402394348465915742193 := by
  unfold tailWord_2423465
  simp only [CollatzResearch.WordTrace]
  refine ⟨88391030165207674715255849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58927353443471783143503899 88391030165207674715255849)
  ·
    refine ⟨66293272623905756036441887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88391030165207674715255849 66293272623905756036441887)
    ·
      refine ⟨99439908935858634054662831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66293272623905756036441887 99439908935858634054662831)
      ·
        refine ⟨149159863403787951081994247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99439908935858634054662831 149159863403787951081994247)
        ·
          refine ⟨223739795105681926622991371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149159863403787951081994247 223739795105681926622991371)
          ·
            refine ⟨335609692658522889934487057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223739795105681926622991371 335609692658522889934487057)
            ·
              refine ⟨251707269493892167450865293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335609692658522889934487057 251707269493892167450865293)
              ·
                refine ⟨94390226060209562794074485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251707269493892167450865293 94390226060209562794074485)
                ·
                  refine ⟨8849083693144646511944483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 94390226060209562794074485 8849083693144646511944483)
                  ·
                    refine ⟨13273625539716969767916725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8849083693144646511944483 13273625539716969767916725)
                    ·
                      refine ⟨1244402394348465915742193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13273625539716969767916725 1244402394348465915742193)
                      ·
                        rfl

theorem cell23_2423465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 1, 5].length) (baseStart_2423465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423465 prefixEnd_2423465 := by exact prefixLift 2423465
  have htrace : WordTrace (prefixWord ++ tailWord_2423465) baseStart_2423465 baseEnd_2423465 := by
    simpa [prefixWord, tailWord_2423465, baseEnd_2423465] using wordTrace_append hprefix tailTrace_2423465
  have hstable : (prefixWord ++ tailWord_2423465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423465).length < 2 ^ (prefixWord ++ tailWord_2423465).sum := by decide
  have hdescent : baseEnd_2423465 < baseStart_2423465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423485 : List Nat := [1, 4, 1, 2, 1, 14]
def baseStart_2423485 : Nat := 118140960795 + 2423485 * 2 ^ 59
def prefixEnd_2423485 : Nat := 4983230072969 + 3 ^ 40 * 2423485 * 2
def baseEnd_2423485 : Nat := 5121039769389118672807

theorem tailTrace_2423485 : CollatzResearch.WordTrace tailWord_2423485 prefixEnd_2423485 5121039769389118672807 := by
  unfold tailWord_2423485
  simp only [CollatzResearch.WordTrace]
  refine ⟨88391759625135218130983909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58927839750090145420655939 88391759625135218130983909)
  ·
    refine ⟨16573454929712853399559483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88391759625135218130983909 16573454929712853399559483)
    ·
      refine ⟨24860182394569280099339225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573454929712853399559483 24860182394569280099339225)
      ·
        refine ⟨18645136795926960074504419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24860182394569280099339225 18645136795926960074504419)
        ·
          refine ⟨27967705193890440111756629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18645136795926960074504419 27967705193890440111756629)
          ·
            refine ⟨5121039769389118672807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 27967705193890440111756629 5121039769389118672807)
            ·
              rfl

theorem cell23_2423485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 14].length) (baseStart_2423485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423485 prefixEnd_2423485 := by exact prefixLift 2423485
  have htrace : WordTrace (prefixWord ++ tailWord_2423485) baseStart_2423485 baseEnd_2423485 := by
    simpa [prefixWord, tailWord_2423485, baseEnd_2423485] using wordTrace_append hprefix tailTrace_2423485
  have hstable : (prefixWord ++ tailWord_2423485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423485).length < 2 ^ (prefixWord ++ tailWord_2423485).sum := by decide
  have hdescent : baseEnd_2423485 < baseStart_2423485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423495 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_2423495 : Nat := 118140960795 + 2423495 * 2 ^ 59
def prefixEnd_2423495 : Nat := 4983230072969 + 3 ^ 40 * 2423495 * 2
def baseEnd_2423495 : Nat := 1244417798768100798367055

theorem tailTrace_2423495 : CollatzResearch.WordTrace tailWord_2423495 prefixEnd_2423495 1244417798768100798367055 := by
  unfold tailWord_2423495
  simp only [CollatzResearch.WordTrace]
  refine ⟨88392124355098989838847939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58928082903399326559231959 88392124355098989838847939)
  ·
    refine ⟨132588186532648484758271909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88392124355098989838847939 132588186532648484758271909)
    ·
      refine ⟨24860284974871590892175983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 132588186532648484758271909 24860284974871590892175983)
      ·
        refine ⟨37290427462307386338263975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24860284974871590892175983 37290427462307386338263975)
        ·
          refine ⟨55935641193461079507395963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37290427462307386338263975 55935641193461079507395963)
          ·
            refine ⟨83903461790191619261093945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55935641193461079507395963 83903461790191619261093945)
            ·
              refine ⟨62927596342643714445820459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 83903461790191619261093945 62927596342643714445820459)
              ·
                refine ⟨94391394513965571668730689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 62927596342643714445820459 94391394513965571668730689)
                ·
                  refine ⟨70793545885474178751548017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94391394513965571668730689 70793545885474178751548017)
                  ·
                    refine ⟨53095159414105634063661013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70793545885474178751548017 53095159414105634063661013)
                    ·
                      refine ⟨1244417798768100798367055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53095159414105634063661013 1244417798768100798367055)
                      ·
                        rfl

theorem cell23_2423495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_2423495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423495 prefixEnd_2423495 := by exact prefixLift 2423495
  have htrace : WordTrace (prefixWord ++ tailWord_2423495) baseStart_2423495 baseEnd_2423495 := by
    simpa [prefixWord, tailWord_2423495, baseEnd_2423495] using wordTrace_append hprefix tailTrace_2423495
  have hstable : (prefixWord ++ tailWord_2423495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423495).length < 2 ^ (prefixWord ++ tailWord_2423495).sum := by decide
  have hdescent : baseEnd_2423495 < baseStart_2423495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423502 : List Nat := [4, 1, 1, 1, 3, 2, 3, 8]
def baseStart_2423502 : Nat := 118140960795 + 2423502 * 2 ^ 59
def prefixEnd_2423502 : Nat := 4983230072969 + 3 ^ 40 * 2423502 * 2
def baseEnd_2423502 : Nat := 46089681227136380406649

theorem tailTrace_2423502 : CollatzResearch.WordTrace tailWord_2423502 prefixEnd_2423502 46089681227136380406649 := by
  unfold tailWord_2423502
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049047458259203754294095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58928253110715753356235173 11049047458259203754294095)
  ·
    refine ⟨16573571187388805631441143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11049047458259203754294095 16573571187388805631441143)
    ·
      refine ⟨24860356781083208447161715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16573571187388805631441143 24860356781083208447161715)
      ·
        refine ⟨37290535171624812670742573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24860356781083208447161715 37290535171624812670742573)
        ·
          refine ⟨13983950689359304751528465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37290535171624812670742573 13983950689359304751528465)
          ·
            refine ⟨10487963017019478563646349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13983950689359304751528465 10487963017019478563646349)
            ·
              refine ⟨3932986131382304461367381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10487963017019478563646349 3932986131382304461367381)
              ·
                refine ⟨46089681227136380406649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3932986131382304461367381 46089681227136380406649)
                ·
                  rfl

theorem cell23_2423502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 8].length) (baseStart_2423502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423502 prefixEnd_2423502 := by exact prefixLift 2423502
  have htrace : WordTrace (prefixWord ++ tailWord_2423502) baseStart_2423502 baseEnd_2423502 := by
    simpa [prefixWord, tailWord_2423502, baseEnd_2423502] using wordTrace_append hprefix tailTrace_2423502
  have hstable : (prefixWord ++ tailWord_2423502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423502).length < 2 ^ (prefixWord ++ tailWord_2423502).sum := by decide
  have hdescent : baseEnd_2423502 < baseStart_2423502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423516 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_2423516 : Nat := 118140960795 + 2423516 * 2 ^ 59
def prefixEnd_2423516 : Nat := 4983230072969 + 3 ^ 40 * 2423516 * 2
def baseEnd_2423516 : Nat := 1244428581861845216204459

theorem tailTrace_2423516 : CollatzResearch.WordTrace tailWord_2423516 prefixEnd_2423516 1244428581861845216204459 := by
  unfold tailWord_2423516
  simp only [CollatzResearch.WordTrace]
  refine ⟨44196445144011455212681201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58928593525348606950241601 44196445144011455212681201)
  ·
    refine ⟨33147333858008591409510901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44196445144011455212681201 33147333858008591409510901)
    ·
      refine ⟨3107562549188305444641647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33147333858008591409510901 3107562549188305444641647)
      ·
        refine ⟨4661343823782458166962471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3107562549188305444641647 4661343823782458166962471)
        ·
          refine ⟨6992015735673687250443707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661343823782458166962471 6992015735673687250443707)
          ·
            refine ⟨10488023603510530875665561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6992015735673687250443707 10488023603510530875665561)
            ·
              refine ⟨7866017702632898156749171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10488023603510530875665561 7866017702632898156749171)
              ·
                refine ⟨11799026553949347235123757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7866017702632898156749171 11799026553949347235123757)
                ·
                  refine ⟨4424634957731005213171409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11799026553949347235123757 4424634957731005213171409)
                  ·
                    refine ⟨3318476218298253909878557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424634957731005213171409 3318476218298253909878557)
                    ·
                      refine ⟨1244428581861845216204459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318476218298253909878557 1244428581861845216204459)
                      ·
                        rfl

theorem cell23_2423516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_2423516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423516 prefixEnd_2423516 := by exact prefixLift 2423516
  have htrace : WordTrace (prefixWord ++ tailWord_2423516) baseStart_2423516 baseEnd_2423516 := by
    simpa [prefixWord, tailWord_2423516, baseEnd_2423516] using wordTrace_append hprefix tailTrace_2423516
  have hstable : (prefixWord ++ tailWord_2423516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423516).length < 2 ^ (prefixWord ++ tailWord_2423516).sum := by decide
  have hdescent : baseEnd_2423516 < baseStart_2423516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423546 : List Nat := [3, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3]
def baseStart_2423546 : Nat := 118140960795 + 2423546 * 2 ^ 59
def prefixEnd_2423546 : Nat := 4983230072969 + 3 ^ 40 * 2423546 * 2
def baseEnd_2423546 : Nat := 1244443986281480098829321

theorem tailTrace_2423546 : CollatzResearch.WordTrace tailWord_2423546 prefixEnd_2423546 1244443986281480098829321 := by
  unfold tailWord_2423546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22098496119478556387238623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58929322985276150365969661 22098496119478556387238623)
  ·
    refine ⟨33147744179217834580857935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22098496119478556387238623 33147744179217834580857935)
    ·
      refine ⟨49721616268826751871286903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33147744179217834580857935 49721616268826751871286903)
      ·
        refine ⟨74582424403240127806930355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49721616268826751871286903 74582424403240127806930355)
        ·
          refine ⟨111873636604860191710395533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74582424403240127806930355 111873636604860191710395533)
          ·
            refine ⟨41952613726822571891398325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111873636604860191710395533 41952613726822571891398325)
            ·
              refine ⟨3933057536889616114818593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41952613726822571891398325 3933057536889616114818593)
              ·
                refine ⟨2949793152667212086113945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933057536889616114818593 2949793152667212086113945)
                ·
                  refine ⟨2212344864500409064585459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2949793152667212086113945 2212344864500409064585459)
                  ·
                    refine ⟨3318517296750613596878189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2212344864500409064585459 3318517296750613596878189)
                    ·
                      refine ⟨1244443986281480098829321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318517296750613596878189 1244443986281480098829321)
                      ·
                        rfl

theorem cell23_2423546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3].length) (baseStart_2423546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423546 prefixEnd_2423546 := by exact prefixLift 2423546
  have htrace : WordTrace (prefixWord ++ tailWord_2423546) baseStart_2423546 baseEnd_2423546 := by
    simpa [prefixWord, tailWord_2423546, baseEnd_2423546] using wordTrace_append hprefix tailTrace_2423546
  have hstable : (prefixWord ++ tailWord_2423546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423546).length < 2 ^ (prefixWord ++ tailWord_2423546).sum := by decide
  have hdescent : baseEnd_2423546 < baseStart_2423546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423562 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 2, 6]
def baseStart_2423562 : Nat := 118140960795 + 2423562 * 2 ^ 59
def prefixEnd_2423562 : Nat := 4983230072969 + 3 ^ 40 * 2423562 * 2
def baseEnd_2423562 : Nat := 414817400657317345409749

theorem tailTrace_2423562 : CollatzResearch.WordTrace tailWord_2423562 prefixEnd_2423562 414817400657317345409749 := by
  unfold tailWord_2423562
  simp only [CollatzResearch.WordTrace]
  refine ⟨22098642011464065070384235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58929712030570840187691293 22098642011464065070384235)
  ·
    refine ⟨33147963017196097605576353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22098642011464065070384235 33147963017196097605576353)
    ·
      refine ⟨24860972262897073204182265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33147963017196097605576353 24860972262897073204182265)
      ·
        refine ⟨18645729197172804903136699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24860972262897073204182265 18645729197172804903136699)
        ·
          refine ⟨27968593795759207354705049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18645729197172804903136699 27968593795759207354705049)
          ·
            refine ⟨20976445346819405516028787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27968593795759207354705049 20976445346819405516028787)
            ·
              refine ⟨31464668020229108274043181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20976445346819405516028787 31464668020229108274043181)
              ·
                refine ⟨11799250507585915602766193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31464668020229108274043181 11799250507585915602766193)
                ·
                  refine ⟨8849437880689436702074645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11799250507585915602766193 8849437880689436702074645)
                  ·
                    refine ⟨414817400657317345409749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8849437880689436702074645 414817400657317345409749)
                    ·
                      rfl

theorem cell23_2423562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_2423562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423562 prefixEnd_2423562 := by exact prefixLift 2423562
  have htrace : WordTrace (prefixWord ++ tailWord_2423562) baseStart_2423562 baseEnd_2423562 := by
    simpa [prefixWord, tailWord_2423562, baseEnd_2423562] using wordTrace_append hprefix tailTrace_2423562
  have hstable : (prefixWord ++ tailWord_2423562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423562).length < 2 ^ (prefixWord ++ tailWord_2423562).sum := by decide
  have hdescent : baseEnd_2423562 < baseStart_2423562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423602 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2423602 : Nat := 118140960795 + 2423602 * 2 ^ 59
def prefixEnd_2423602 : Nat := 4983230072969 + 3 ^ 40 * 2423602 * 2
def baseEnd_2423602 : Nat := 1244472741198131879729063

theorem tailTrace_2423602 : CollatzResearch.WordTrace tailWord_2423602 prefixEnd_2423602 1244472741198131879729063 := by
  unfold tailWord_2423602
  simp only [CollatzResearch.WordTrace]
  refine ⟨22099006741427836778248265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58930684643807564741995373 22099006741427836778248265)
  ·
    refine ⟨16574255056070877583686199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22099006741427836778248265 16574255056070877583686199)
    ·
      refine ⟨24861382584106316375529299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16574255056070877583686199 24861382584106316375529299)
      ·
        refine ⟨37292073876159474563293949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24861382584106316375529299 37292073876159474563293949)
        ·
          refine ⟨13984527703559802961235231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37292073876159474563293949 13984527703559802961235231)
          ·
            refine ⟨20976791555339704441852847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13984527703559802961235231 20976791555339704441852847)
            ·
              refine ⟨31465187333009556662779271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20976791555339704441852847 31465187333009556662779271)
              ·
                refine ⟨47197780999514334994168907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31465187333009556662779271 47197780999514334994168907)
                ·
                  refine ⟨70796671499271502491253361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47197780999514334994168907 70796671499271502491253361)
                  ·
                    refine ⟨53097503624453626868440021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 70796671499271502491253361 53097503624453626868440021)
                    ·
                      refine ⟨1244472741198131879729063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 53097503624453626868440021 1244472741198131879729063)
                      ·
                        rfl

theorem cell23_2423602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2423602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423602 prefixEnd_2423602 := by exact prefixLift 2423602
  have htrace : WordTrace (prefixWord ++ tailWord_2423602) baseStart_2423602 baseEnd_2423602 := by
    simpa [prefixWord, tailWord_2423602, baseEnd_2423602] using wordTrace_append hprefix tailTrace_2423602
  have hstable : (prefixWord ++ tailWord_2423602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423602).length < 2 ^ (prefixWord ++ tailWord_2423602).sum := by decide
  have hdescent : baseEnd_2423602 < baseStart_2423602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423639 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 2, 5]
def baseStart_2423639 : Nat := 118140960795 + 2423639 * 2 ^ 59
def prefixEnd_2423639 : Nat := 4983230072969 + 3 ^ 40 * 2423639 * 2
def baseEnd_2423639 : Nat := 414830579994116078322131

theorem tailTrace_2423639 : CollatzResearch.WordTrace tailWord_2423639 prefixEnd_2423639 414830579994116078322131 := by
  unfold tailWord_2423639
  simp only [CollatzResearch.WordTrace]
  refine ⟨88397376466577302432089971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58931584311051534954726647 88397376466577302432089971)
  ·
    refine ⟨132596064699865953648134957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88397376466577302432089971 132596064699865953648134957)
    ·
      refine ⟨49723524262449732618050609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132596064699865953648134957 49723524262449732618050609)
      ·
        refine ⟨37292643196837299463537957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49723524262449732618050609 37292643196837299463537957)
        ·
          refine ⟨6992370599406993649413367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37292643196837299463537957 6992370599406993649413367)
          ·
            refine ⟨10488555899110490474120051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6992370599406993649413367 10488555899110490474120051)
            ·
              refine ⟨15732833848665735711180077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10488555899110490474120051 15732833848665735711180077)
              ·
                refine ⟨5899812693249650891692529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15732833848665735711180077 5899812693249650891692529)
                ·
                  refine ⟨4424859519937238168769397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5899812693249650891692529 4424859519937238168769397)
                  ·
                    refine ⟨414830579994116078322131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4424859519937238168769397 414830579994116078322131)
                    ·
                      rfl

theorem cell23_2423639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_2423639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423639 prefixEnd_2423639 := by exact prefixLift 2423639
  have htrace : WordTrace (prefixWord ++ tailWord_2423639) baseStart_2423639 baseEnd_2423639 := by
    simpa [prefixWord, tailWord_2423639, baseEnd_2423639] using wordTrace_append hprefix tailTrace_2423639
  have hstable : (prefixWord ++ tailWord_2423639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423639).length < 2 ^ (prefixWord ++ tailWord_2423639).sum := by decide
  have hdescent : baseEnd_2423639 < baseStart_2423639 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423659 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 4]
def baseStart_2423659 : Nat := 118140960795 + 2423659 * 2 ^ 59
def prefixEnd_2423659 : Nat := 4983230072969 + 3 ^ 40 * 2423659 * 2
def baseEnd_2423659 : Nat := 1244502009595438156716301

theorem tailTrace_2423659 : CollatzResearch.WordTrace tailWord_2423659 prefixEnd_2423659 1244502009595438156716301 := by
  unfold tailWord_2423659
  simp only [CollatzResearch.WordTrace]
  refine ⟨88398105926504845847818031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58932070617669897231878687 88398105926504845847818031)
  ·
    refine ⟨132597158889757268771727047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88398105926504845847818031 132597158889757268771727047)
    ·
      refine ⟨198895738334635903157590571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132597158889757268771727047 198895738334635903157590571)
      ·
        refine ⟨298343607501953854736385857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 198895738334635903157590571 298343607501953854736385857)
        ·
          refine ⟨223757705626465391052289393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 298343607501953854736385857 223757705626465391052289393)
          ·
            refine ⟨167818279219849043289217045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223757705626465391052289393 167818279219849043289217045)
            ·
              refine ⟨7866481838430423904182049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167818279219849043289217045 7866481838430423904182049)
              ·
                refine ⟨5899861378822817928136537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7866481838430423904182049 5899861378822817928136537)
                ·
                  refine ⟨4424896034117113446102403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5899861378822817928136537 4424896034117113446102403)
                  ·
                    refine ⟨6637344051175670169153605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4424896034117113446102403 6637344051175670169153605)
                    ·
                      refine ⟨1244502009595438156716301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6637344051175670169153605 1244502009595438156716301)
                      ·
                        rfl

theorem cell23_2423659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 4].length) (baseStart_2423659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423659 prefixEnd_2423659 := by exact prefixLift 2423659
  have htrace : WordTrace (prefixWord ++ tailWord_2423659) baseStart_2423659 baseEnd_2423659 := by
    simpa [prefixWord, tailWord_2423659, baseEnd_2423659] using wordTrace_append hprefix tailTrace_2423659
  have hstable : (prefixWord ++ tailWord_2423659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423659).length < 2 ^ (prefixWord ++ tailWord_2423659).sum := by decide
  have hdescent : baseEnd_2423659 < baseStart_2423659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423672 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_2423672 : Nat := 118140960795 + 2423672 * 2 ^ 59
def prefixEnd_2423672 : Nat := 4983230072969 + 3 ^ 40 * 2423672 * 2
def baseEnd_2423672 : Nat := 1244508684843946605853741

theorem tailTrace_2423672 : CollatzResearch.WordTrace tailWord_2423672 prefixEnd_2423672 1244508684843946605853741 := by
  unfold tailWord_2423672
  simp only [CollatzResearch.WordTrace]
  refine ⟨44199290037728874534020635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58932386716971832712027513 44199290037728874534020635)
  ·
    refine ⟨66298935056593311801030953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44199290037728874534020635 66298935056593311801030953)
    ·
      refine ⟨49724201292444983850773215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66298935056593311801030953 49724201292444983850773215)
      ·
        refine ⟨74586301938667475776159823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49724201292444983850773215 74586301938667475776159823)
        ·
          refine ⟨111879452908001213664239735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74586301938667475776159823 111879452908001213664239735)
          ·
            refine ⟨167819179362001820496359603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111879452908001213664239735 167819179362001820496359603)
            ·
              refine ⟨251728769043002730744539405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167819179362001820496359603 251728769043002730744539405)
              ·
                refine ⟨94398288391126024029202277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251728769043002730744539405 94398288391126024029202277)
                ·
                  refine ⟨17699679073336129505475427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94398288391126024029202277 17699679073336129505475427)
                  ·
                    refine ⟨26549518610004194258213141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17699679073336129505475427 26549518610004194258213141)
                    ·
                      refine ⟨1244508684843946605853741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26549518610004194258213141 1244508684843946605853741)
                      ·
                        rfl

theorem cell23_2423672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_2423672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423672 prefixEnd_2423672 := by exact prefixLift 2423672
  have htrace : WordTrace (prefixWord ++ tailWord_2423672) baseStart_2423672 baseEnd_2423672 := by
    simpa [prefixWord, tailWord_2423672, baseEnd_2423672] using wordTrace_append hprefix tailTrace_2423672
  have hstable : (prefixWord ++ tailWord_2423672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423672).length < 2 ^ (prefixWord ++ tailWord_2423672).sum := by decide
  have hdescent : baseEnd_2423672 < baseStart_2423672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423679 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 3]
def baseStart_2423679 : Nat := 118140960795 + 2423679 * 2 ^ 59
def prefixEnd_2423679 : Nat := 4983230072969 + 3 ^ 40 * 2423679 * 2
def baseEnd_2423679 : Nat := 1244512279208528078466209

theorem tailTrace_2423679 : CollatzResearch.WordTrace tailWord_2423679 prefixEnd_2423679 1244512279208528078466209 := by
  unfold tailWord_2423679
  simp only [CollatzResearch.WordTrace]
  refine ⟨88398835386432389263546091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58932556924288259509030727 88398835386432389263546091)
  ·
    refine ⟨132598253079648583895319137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88398835386432389263546091 132598253079648583895319137)
    ·
      refine ⟨99448689809736437921489353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132598253079648583895319137 99448689809736437921489353)
      ·
        refine ⟨74586517357302328441117015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99448689809736437921489353 74586517357302328441117015)
        ·
          refine ⟨111879776035953492661675523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74586517357302328441117015 111879776035953492661675523)
          ·
            refine ⟨167819664053930238992513285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111879776035953492661675523 167819664053930238992513285)
            ·
              refine ⟨31466187010111919811096241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 167819664053930238992513285 31466187010111919811096241)
              ·
                refine ⟨23599640257583939858322181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31466187010111919811096241 23599640257583939858322181)
                ·
                  refine ⟨4424932548296988723435409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23599640257583939858322181 4424932548296988723435409)
                  ·
                    refine ⟨3318699411222741542576557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4424932548296988723435409 3318699411222741542576557)
                    ·
                      refine ⟨1244512279208528078466209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318699411222741542576557 1244512279208528078466209)
                      ·
                        rfl

theorem cell23_2423679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_2423679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423679 prefixEnd_2423679 := by exact prefixLift 2423679
  have htrace : WordTrace (prefixWord ++ tailWord_2423679) baseStart_2423679 baseEnd_2423679 := by
    simpa [prefixWord, tailWord_2423679, baseEnd_2423679] using wordTrace_append hprefix tailTrace_2423679
  have hstable : (prefixWord ++ tailWord_2423679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423679).length < 2 ^ (prefixWord ++ tailWord_2423679).sum := by decide
  have hdescent : baseEnd_2423679 < baseStart_2423679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423703 : List Nat := [1, 1, 3, 3, 1, 2, 4, 3, 1, 4]
def baseStart_2423703 : Nat := 118140960795 + 2423703 * 2 ^ 59
def prefixEnd_2423703 : Nat := 4983230072969 + 3 ^ 40 * 2423703 * 2
def baseEnd_2423703 : Nat := 414841534248078661522033

theorem tailTrace_2423703 : CollatzResearch.WordTrace tailWord_2423703 prefixEnd_2423703 414841534248078661522033 := by
  unfold tailWord_2423703
  simp only [CollatzResearch.WordTrace]
  refine ⟨88399710738345441362419763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58933140492230294241613175 88399710738345441362419763)
  ·
    refine ⟨132599566107518162043629645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88399710738345441362419763 132599566107518162043629645)
    ·
      refine ⟨49724837290319310766361117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 132599566107518162043629645 49724837290319310766361117)
      ·
        refine ⟨18646813983869741537385419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49724837290319310766361117 18646813983869741537385419)
        ·
          refine ⟨27970220975804612306078129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18646813983869741537385419 27970220975804612306078129)
          ·
            refine ⟨20977665731853459229558597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27970220975804612306078129 20977665731853459229558597)
            ·
              refine ⟨3933312324722523605542237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20977665731853459229558597 3933312324722523605542237)
              ·
                refine ⟨1474992121770946352078339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3933312324722523605542237 1474992121770946352078339)
                ·
                  refine ⟨2212488182656419528117509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1474992121770946352078339 2212488182656419528117509)
                  ·
                    refine ⟨414841534248078661522033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2212488182656419528117509 414841534248078661522033)
                    ·
                      rfl

theorem cell23_2423703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_2423703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423703 prefixEnd_2423703 := by exact prefixLift 2423703
  have htrace : WordTrace (prefixWord ++ tailWord_2423703) baseStart_2423703 baseEnd_2423703 := by
    simpa [prefixWord, tailWord_2423703, baseEnd_2423703] using wordTrace_append hprefix tailTrace_2423703
  have hstable : (prefixWord ++ tailWord_2423703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423703).length < 2 ^ (prefixWord ++ tailWord_2423703).sum := by decide
  have hdescent : baseEnd_2423703 < baseStart_2423703 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423736 : List Nat := [2, 1, 2, 1, 2, 4, 1, 2, 1, 5, 2]
def baseStart_2423736 : Nat := 118140960795 + 2423736 * 2 ^ 59
def prefixEnd_2423736 : Nat := 4983230072969 + 3 ^ 40 * 2423736 * 2
def baseEnd_2423736 : Nat := 1244541547605834355453447

theorem tailTrace_2423736 : CollatzResearch.WordTrace tailWord_2423736 prefixEnd_2423736 1244541547605834355453447 := by
  unfold tailWord_2423736
  simp only [CollatzResearch.WordTrace]
  refine ⟨44200457173612943999185531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58933942898150591998914041 44200457173612943999185531)
  ·
    refine ⟨66300685760419415998778297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44200457173612943999185531 66300685760419415998778297)
    ·
      refine ⟨49725514320314561999083723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66300685760419415998778297 49725514320314561999083723)
      ·
        refine ⟨74588271480471842998625585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49725514320314561999083723 74588271480471842998625585)
        ·
          refine ⟨55941203610353882248969189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74588271480471842998625585 55941203610353882248969189)
          ·
            refine ⟨10488975676941352921681723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55941203610353882248969189 10488975676941352921681723)
            ·
              refine ⟨15733463515412029382522585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10488975676941352921681723 15733463515412029382522585)
              ·
                refine ⟨11800097636559022036891939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15733463515412029382522585 11800097636559022036891939)
                ·
                  refine ⟨17700146454838533055337909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11800097636559022036891939 17700146454838533055337909)
                  ·
                    refine ⟨1659388730141112473937929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 17700146454838533055337909 1659388730141112473937929)
                    ·
                      refine ⟨1244541547605834355453447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659388730141112473937929 1244541547605834355453447)
                      ·
                        rfl

theorem cell23_2423736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_2423736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423736 prefixEnd_2423736 := by exact prefixLift 2423736
  have htrace : WordTrace (prefixWord ++ tailWord_2423736) baseStart_2423736 baseEnd_2423736 := by
    simpa [prefixWord, tailWord_2423736, baseEnd_2423736] using wordTrace_append hprefix tailTrace_2423736
  have hstable : (prefixWord ++ tailWord_2423736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423736).length < 2 ^ (prefixWord ++ tailWord_2423736).sum := by decide
  have hdescent : baseEnd_2423736 < baseStart_2423736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423749 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 4]
def baseStart_2423749 : Nat := 118140960795 + 2423749 * 2 ^ 59
def prefixEnd_2423749 : Nat := 4983230072969 + 3 ^ 40 * 2423749 * 2
def baseEnd_2423749 : Nat := 1244548222854342804590887

theorem tailTrace_2423749 : CollatzResearch.WordTrace tailWord_2423749 prefixEnd_2423749 1244548222854342804590887 := by
  unfold tailWord_2423749
  simp only [CollatzResearch.WordTrace]
  refine ⟨88401388496178791218594301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58934258997452527479062867 88401388496178791218594301)
  ·
    refine ⟨33150520686067046706972863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88401388496178791218594301 33150520686067046706972863)
    ·
      refine ⟨49725781029100570060459295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33150520686067046706972863 49725781029100570060459295)
      ·
        refine ⟨74588671543650855090688943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49725781029100570060459295 74588671543650855090688943)
        ·
          refine ⟨111883007315476282636033415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74588671543650855090688943 111883007315476282636033415)
          ·
            refine ⟨167824510973214423954050123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111883007315476282636033415 167824510973214423954050123)
            ·
              refine ⟨251736766459821635931075185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167824510973214423954050123 251736766459821635931075185)
              ·
                refine ⟨188802574844866226948306389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251736766459821635931075185 188802574844866226948306389)
                ·
                  refine ⟨4425060347926552194100931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 188802574844866226948306389 4425060347926552194100931)
                  ·
                    refine ⟨6637590521889828291151397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4425060347926552194100931 6637590521889828291151397)
                    ·
                      refine ⟨1244548222854342804590887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6637590521889828291151397 1244548222854342804590887)
                      ·
                        rfl

theorem cell23_2423749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 1, 4].length) (baseStart_2423749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423749 prefixEnd_2423749 := by exact prefixLift 2423749
  have htrace : WordTrace (prefixWord ++ tailWord_2423749) baseStart_2423749 baseEnd_2423749 := by
    simpa [prefixWord, tailWord_2423749, baseEnd_2423749] using wordTrace_append hprefix tailTrace_2423749
  have hstable : (prefixWord ++ tailWord_2423749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423749).length < 2 ^ (prefixWord ++ tailWord_2423749).sum := by decide
  have hdescent : baseEnd_2423749 < baseStart_2423749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423779 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6]
def baseStart_2423779 : Nat := 118140960795 + 2423779 * 2 ^ 59
def prefixEnd_2423779 : Nat := 4983230072969 + 3 ^ 40 * 2423779 * 2
def baseEnd_2423779 : Nat := 1244563627273977687215749

theorem tailTrace_2423779 : CollatzResearch.WordTrace tailWord_2423779 prefixEnd_2423779 1244563627273977687215749 := by
  unfold tailWord_2423779
  simp only [CollatzResearch.WordTrace]
  refine ⟨88402482686070106342186391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58934988457380070894790927 88402482686070106342186391)
  ·
    refine ⟨132603724029105159513279587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88402482686070106342186391 132603724029105159513279587)
    ·
      refine ⟨198905586043657739269919381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132603724029105159513279587 198905586043657739269919381)
      ·
        refine ⟨9323699345796456528277471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 198905586043657739269919381 9323699345796456528277471)
        ·
          refine ⟨13985549018694684792416207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9323699345796456528277471 13985549018694684792416207)
          ·
            refine ⟨20978323528042027188624311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13985549018694684792416207 20978323528042027188624311)
            ·
              refine ⟨31467485292063040782936467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20978323528042027188624311 31467485292063040782936467)
              ·
                refine ⟨47201227938094561174404701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31467485292063040782936467 47201227938094561174404701)
                ·
                  refine ⟨17700460476785460440401763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47201227938094561174404701 17700460476785460440401763)
                  ·
                    refine ⟨26550690715178190660602645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17700460476785460440401763 26550690715178190660602645)
                    ·
                      refine ⟨1244563627273977687215749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 26550690715178190660602645 1244563627273977687215749)
                      ·
                        rfl

theorem cell23_2423779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_2423779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423779 prefixEnd_2423779 := by exact prefixLift 2423779
  have htrace : WordTrace (prefixWord ++ tailWord_2423779) baseStart_2423779 baseEnd_2423779 := by
    simpa [prefixWord, tailWord_2423779, baseEnd_2423779] using wordTrace_append hprefix tailTrace_2423779
  have hstable : (prefixWord ++ tailWord_2423779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423779).length < 2 ^ (prefixWord ++ tailWord_2423779).sum := by decide
  have hdescent : baseEnd_2423779 < baseStart_2423779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423786 : List Nat := [3, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_2423786 : Nat := 118140960795 + 2423786 * 2 ^ 59
def prefixEnd_2423786 : Nat := 4983230072969 + 3 ^ 40 * 2423786 * 2
def baseEnd_2423786 : Nat := 1244567221638559159828217

theorem tailTrace_2423786 : CollatzResearch.WordTrace tailWord_2423786 prefixEnd_2423786 1244567221638559159828217 := by
  unfold tailWord_2423786
  simp only [CollatzResearch.WordTrace]
  refine ⟨22100684499261186634422803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58935158664696497691794141 22100684499261186634422803)
  ·
    refine ⟨33151026748891779951634205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22100684499261186634422803 33151026748891779951634205)
    ·
      refine ⟨12431635030834417481862827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33151026748891779951634205 12431635030834417481862827)
      ·
        refine ⟨18647452546251626222794241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12431635030834417481862827 18647452546251626222794241)
        ·
          refine ⟨13985589409688719667095681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18647452546251626222794241 13985589409688719667095681)
          ·
            refine ⟨10489192057266539750321761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13985589409688719667095681 10489192057266539750321761)
            ·
              refine ⟨7866894042949904812741321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10489192057266539750321761 7866894042949904812741321)
              ·
                refine ⟨5900170532212428609555991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7866894042949904812741321 5900170532212428609555991)
                ·
                  refine ⟨8850255798318642914333987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900170532212428609555991 8850255798318642914333987)
                  ·
                    refine ⟨13275383697477964371500981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8850255798318642914333987 13275383697477964371500981)
                    ·
                      refine ⟨1244567221638559159828217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13275383697477964371500981 1244567221638559159828217)
                      ·
                        rfl

theorem cell23_2423786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_2423786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423786 prefixEnd_2423786 := by exact prefixLift 2423786
  have htrace : WordTrace (prefixWord ++ tailWord_2423786) baseStart_2423786 baseEnd_2423786 := by
    simpa [prefixWord, tailWord_2423786, baseEnd_2423786] using wordTrace_append hprefix tailTrace_2423786
  have hstable : (prefixWord ++ tailWord_2423786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423786).length < 2 ^ (prefixWord ++ tailWord_2423786).sum := by decide
  have hdescent : baseEnd_2423786 < baseStart_2423786 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423793 : List Nat := [1, 2, 2, 2, 4, 2, 1, 3, 2, 4]
def baseStart_2423793 : Nat := 118140960795 + 2423793 * 2 ^ 59
def prefixEnd_2423793 : Nat := 4983230072969 + 3 ^ 40 * 2423793 * 2
def baseEnd_2423793 : Nat := 414856938667713544146895

theorem tailTrace_2423793 : CollatzResearch.WordTrace tailWord_2423793 prefixEnd_2423793 414856938667713544146895 := by
  unfold tailWord_2423793
  simp only [CollatzResearch.WordTrace]
  refine ⟨88402993308019386733196033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58935328872012924488797355 88402993308019386733196033)
  ·
    refine ⟨66302244981014540049897025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88402993308019386733196033 66302244981014540049897025)
    ·
      refine ⟨49726683735760905037422769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66302244981014540049897025 49726683735760905037422769)
      ·
        refine ⟨37295012801820678778067077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49726683735760905037422769 37295012801820678778067077)
        ·
          refine ⟨6992814900341377270887577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37295012801820678778067077 6992814900341377270887577)
          ·
            refine ⟨5244611175256032953165683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6992814900341377270887577 5244611175256032953165683)
            ·
              refine ⟨7866916762884049429748525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244611175256032953165683 7866916762884049429748525)
              ·
                refine ⟨2950093786081518536155697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7866916762884049429748525 2950093786081518536155697)
                ·
                  refine ⟨2212570339561138902116773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950093786081518536155697 2212570339561138902116773)
                  ·
                    refine ⟨414856938667713544146895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2212570339561138902116773 414856938667713544146895)
                    ·
                      rfl

theorem cell23_2423793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_2423793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423793 prefixEnd_2423793 := by exact prefixLift 2423793
  have htrace : WordTrace (prefixWord ++ tailWord_2423793) baseStart_2423793 baseEnd_2423793 := by
    simpa [prefixWord, tailWord_2423793, baseEnd_2423793] using wordTrace_append hprefix tailTrace_2423793
  have hstable : (prefixWord ++ tailWord_2423793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423793).length < 2 ^ (prefixWord ++ tailWord_2423793).sum := by decide
  have hdescent : baseEnd_2423793 < baseStart_2423793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423797 : List Nat := [1, 3, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2423797 : Nat := 118140960795 + 2423797 * 2 ^ 59
def prefixEnd_2423797 : Nat := 4983230072969 + 3 ^ 40 * 2423797 * 2
def baseEnd_2423797 : Nat := 414857623308586205596889

theorem tailTrace_2423797 : CollatzResearch.WordTrace tailWord_2423797 prefixEnd_2423797 414857623308586205596889 := by
  unfold tailWord_2423797
  simp only [CollatzResearch.WordTrace]
  refine ⟨88403139200004895416341645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58935426133336596944227763 88403139200004895416341645)
  ·
    refine ⟨33151177200001835781128117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88403139200004895416341645 33151177200001835781128117)
    ·
      refine ⟨3107922862500172104480761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33151177200001835781128117 3107922862500172104480761)
      ·
        refine ⟨2330942146875129078360571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3107922862500172104480761 2330942146875129078360571)
        ·
          refine ⟨3496413220312693617540857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330942146875129078360571 3496413220312693617540857)
          ·
            refine ⟨2622309915234520213155643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3496413220312693617540857 2622309915234520213155643)
            ·
              refine ⟨3933464872851780319733465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622309915234520213155643 3933464872851780319733465)
              ·
                refine ⟨2950098654638835239800099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3933464872851780319733465 2950098654638835239800099)
                ·
                  refine ⟨4425147981958252859700149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950098654638835239800099 4425147981958252859700149)
                  ·
                    refine ⟨414857623308586205596889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4425147981958252859700149 414857623308586205596889)
                    ·
                      rfl

theorem cell23_2423797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2423797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423797 prefixEnd_2423797 := by exact prefixLift 2423797
  have htrace : WordTrace (prefixWord ++ tailWord_2423797) baseStart_2423797 baseEnd_2423797 := by
    simpa [prefixWord, tailWord_2423797, baseEnd_2423797] using wordTrace_append hprefix tailTrace_2423797
  have hstable : (prefixWord ++ tailWord_2423797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423797).length < 2 ^ (prefixWord ++ tailWord_2423797).sum := by decide
  have hdescent : baseEnd_2423797 < baseStart_2423797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423810 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2423810 : Nat := 118140960795 + 2423810 * 2 ^ 59
def prefixEnd_2423810 : Nat := 4983230072969 + 3 ^ 40 * 2423810 * 2
def baseEnd_2423810 : Nat := 414859848391422355309369

theorem tailTrace_2423810 : CollatzResearch.WordTrace tailWord_2423810 prefixEnd_2423810 414859848391422355309369 := by
  unfold tailWord_2423810
  simp only [CollatzResearch.WordTrace]
  refine ⟨22100903337239449659141221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58935742232638532424376589 22100903337239449659141221)
  ·
    refine ⟨4143919375732396811088979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22100903337239449659141221 4143919375732396811088979)
    ·
      refine ⟨6215879063598595216633469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4143919375732396811088979 6215879063598595216633469)
      ·
        refine ⟨2330954648849473206237551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6215879063598595216633469 2330954648849473206237551)
        ·
          refine ⟨3496431973274209809356327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330954648849473206237551 3496431973274209809356327)
          ·
            refine ⟨5244647959911314714034491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496431973274209809356327 5244647959911314714034491)
            ·
              refine ⟨7866971939866972071051737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5244647959911314714034491 7866971939866972071051737)
              ·
                refine ⟨5900228954900229053288803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7866971939866972071051737 5900228954900229053288803)
                ·
                  refine ⟨8850343432350343579933205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900228954900229053288803 8850343432350343579933205)
                  ·
                    refine ⟨414859848391422355309369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8850343432350343579933205 414859848391422355309369)
                    ·
                      rfl

theorem cell23_2423810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2423810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423810 prefixEnd_2423810 := by exact prefixLift 2423810
  have htrace : WordTrace (prefixWord ++ tailWord_2423810) baseStart_2423810 baseEnd_2423810 := by
    simpa [prefixWord, tailWord_2423810, baseEnd_2423810] using wordTrace_append hprefix tailTrace_2423810
  have hstable : (prefixWord ++ tailWord_2423810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423810).length < 2 ^ (prefixWord ++ tailWord_2423810).sum := by decide
  have hdescent : baseEnd_2423810 < baseStart_2423810 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423816 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_2423816 : Nat := 118140960795 + 2423816 * 2 ^ 59
def prefixEnd_2423816 : Nat := 4983230072969 + 3 ^ 40 * 2423816 * 2
def baseEnd_2423816 : Nat := 1244582626058194042453079

theorem tailTrace_2423816 : CollatzResearch.WordTrace tailWord_2423816 prefixEnd_2423816 1244582626058194042453079 := by
  unfold tailWord_2423816
  simp only [CollatzResearch.WordTrace]
  refine ⟨44201916093468030830641651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58935888124624041107522201 44201916093468030830641651)
  ·
    refine ⟨66302874140202046245962477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44201916093468030830641651 66302874140202046245962477)
    ·
      refine ⟨24863577802575767342235929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66302874140202046245962477 24863577802575767342235929)
      ·
        refine ⟨18647683351931825506676947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24863577802575767342235929 18647683351931825506676947)
        ·
          refine ⟨27971525027897738260015421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18647683351931825506676947 27971525027897738260015421)
          ·
            refine ⟨10489321885461651847505783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27971525027897738260015421 10489321885461651847505783)
            ·
              refine ⟨15733982828192477771258675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10489321885461651847505783 15733982828192477771258675)
              ·
                refine ⟨23600974242288716656888013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15733982828192477771258675 23600974242288716656888013)
                ·
                  refine ⟨8850365340858268746333005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23600974242288716656888013 8850365340858268746333005)
                  ·
                    refine ⟨3318887002821850779874877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8850365340858268746333005 3318887002821850779874877)
                    ·
                      refine ⟨1244582626058194042453079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318887002821850779874877 1244582626058194042453079)
                      ·
                        rfl

theorem cell23_2423816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_2423816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423816 prefixEnd_2423816 := by exact prefixLift 2423816
  have htrace : WordTrace (prefixWord ++ tailWord_2423816) baseStart_2423816 baseEnd_2423816 := by
    simpa [prefixWord, tailWord_2423816, baseEnd_2423816] using wordTrace_append hprefix tailTrace_2423816
  have hstable : (prefixWord ++ tailWord_2423816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423816).length < 2 ^ (prefixWord ++ tailWord_2423816).sum := by decide
  have hdescent : baseEnd_2423816 < baseStart_2423816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423820 : List Nat := [2, 2, 1, 2, 3, 3, 3, 1, 1, 2, 3]
def baseStart_2423820 : Nat := 118140960795 + 2423820 * 2 ^ 59
def prefixEnd_2423820 : Nat := 4983230072969 + 3 ^ 40 * 2423820 * 2
def baseEnd_2423820 : Nat := 1244584679980812026803061

theorem tailTrace_2423820 : CollatzResearch.WordTrace tailWord_2423820 prefixEnd_2423820 1244584679980812026803061 := by
  unfold tailWord_2423820
  simp only [CollatzResearch.WordTrace]
  refine ⟨44201989039460785172214457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58935985385947713562952609 44201989039460785172214457)
  ·
    refine ⟨33151491779595588879160843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44201989039460785172214457 33151491779595588879160843)
    ·
      refine ⟨49727237669393383318741265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33151491779595588879160843 49727237669393383318741265)
      ·
        refine ⟨37295428252045037489055949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49727237669393383318741265 37295428252045037489055949)
        ·
          refine ⟨13985785594516889058395981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37295428252045037489055949 13985785594516889058395981)
          ·
            refine ⟨5244669597943833396898493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13985785594516889058395981 5244669597943833396898493)
            ·
              refine ⟨1966751099228937523836935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5244669597943833396898493 1966751099228937523836935)
              ·
                refine ⟨2950126648843406285755403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966751099228937523836935 2950126648843406285755403)
                ·
                  refine ⟨4425189973265109428633105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2950126648843406285755403 4425189973265109428633105)
                  ·
                    refine ⟨3318892479948832071474829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4425189973265109428633105 3318892479948832071474829)
                    ·
                      refine ⟨1244584679980812026803061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318892479948832071474829 1244584679980812026803061)
                      ·
                        rfl

theorem cell23_2423820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_2423820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423820 prefixEnd_2423820 := by exact prefixLift 2423820
  have htrace : WordTrace (prefixWord ++ tailWord_2423820) baseStart_2423820 baseEnd_2423820 := by
    simpa [prefixWord, tailWord_2423820, baseEnd_2423820] using wordTrace_append hprefix tailTrace_2423820
  have hstable : (prefixWord ++ tailWord_2423820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423820).length < 2 ^ (prefixWord ++ tailWord_2423820).sum := by decide
  have hdescent : baseEnd_2423820 < baseStart_2423820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423833 : List Nat := [1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 3]
def baseStart_2423833 : Nat := 118140960795 + 2423833 * 2 ^ 59
def prefixEnd_2423833 : Nat := 4983230072969 + 3 ^ 40 * 2423833 * 2
def baseEnd_2423833 : Nat := 1244591355229320475940501

theorem tailTrace_2423833 : CollatzResearch.WordTrace tailWord_2423833 prefixEnd_2423833 1244591355229320475940501 := by
  unfold tailWord_2423833
  simp only [CollatzResearch.WordTrace]
  refine ⟨88404452227874473564652153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58936301485249649043101435 88404452227874473564652153)
  ·
    refine ⟨66303339170905855173489115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88404452227874473564652153 66303339170905855173489115)
    ·
      refine ⟨99455008756358782760233673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66303339170905855173489115 99455008756358782760233673)
      ·
        refine ⟨74591256567269087070175255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99455008756358782760233673 74591256567269087070175255)
        ·
          refine ⟨111886884850903630605262883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74591256567269087070175255 111886884850903630605262883)
          ·
            refine ⟨167830327276355445907894325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111886884850903630605262883 167830327276355445907894325)
            ·
              refine ⟨15734093182158323053865093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 167830327276355445907894325 15734093182158323053865093)
              ·
                refine ⟨2950142471654685572599705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15734093182158323053865093 2950142471654685572599705)
                ·
                  refine ⟨2212606853741014179449779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2950142471654685572599705 2212606853741014179449779)
                  ·
                    refine ⟨3318910280611521269174669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2212606853741014179449779 3318910280611521269174669)
                    ·
                      refine ⟨1244591355229320475940501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318910280611521269174669 1244591355229320475940501)
                      ·
                        rfl

theorem cell23_2423833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4, 2, 1, 3].length) (baseStart_2423833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423833 prefixEnd_2423833 := by exact prefixLift 2423833
  have htrace : WordTrace (prefixWord ++ tailWord_2423833) baseStart_2423833 baseEnd_2423833 := by
    simpa [prefixWord, tailWord_2423833, baseEnd_2423833] using wordTrace_append hprefix tailTrace_2423833
  have hstable : (prefixWord ++ tailWord_2423833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423833).length < 2 ^ (prefixWord ++ tailWord_2423833).sum := by decide
  have hdescent : baseEnd_2423833 < baseStart_2423833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423840 : List Nat := [2, 1, 1, 7, 2, 1, 1, 8]
def baseStart_2423840 : Nat := 118140960795 + 2423840 * 2 ^ 59
def prefixEnd_2423840 : Nat := 4983230072969 + 3 ^ 40 * 2423840 * 2
def baseEnd_2423840 : Nat := 46096109244218590687147

theorem tailTrace_2423840 : CollatzResearch.WordTrace tailWord_2423840 prefixEnd_2423840 46096109244218590687147 := by
  unfold tailWord_2423840
  simp only [CollatzResearch.WordTrace]
  refine ⟨44202353769424556880078487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58936471692566075840104649 44202353769424556880078487)
  ·
    refine ⟨66303530654136835320117731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44202353769424556880078487 66303530654136835320117731)
    ·
      refine ⟨99455295981205252980176597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66303530654136835320117731 99455295981205252980176597)
      ·
        refine ⟨2330983499559498116722889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 99455295981205252980176597 2330983499559498116722889)
        ·
          refine ⟨1748237624669623587542167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2330983499559498116722889 1748237624669623587542167)
          ·
            refine ⟨2622356437004435381313251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748237624669623587542167 2622356437004435381313251)
            ·
              refine ⟨3933534655506653071969877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622356437004435381313251 3933534655506653071969877)
              ·
                refine ⟨46096109244218590687147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3933534655506653071969877 46096109244218590687147)
                ·
                  rfl

theorem cell23_2423840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 8].length) (baseStart_2423840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423840 prefixEnd_2423840 := by exact prefixLift 2423840
  have htrace : WordTrace (prefixWord ++ tailWord_2423840) baseStart_2423840 baseEnd_2423840 := by
    simpa [prefixWord, tailWord_2423840, baseEnd_2423840] using wordTrace_append hprefix tailTrace_2423840
  have hstable : (prefixWord ++ tailWord_2423840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423840).length < 2 ^ (prefixWord ++ tailWord_2423840).sum := by decide
  have hdescent : baseEnd_2423840 < baseStart_2423840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423843 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 3, 3, 2]
def baseStart_2423843 : Nat := 118140960795 + 2423843 * 2 ^ 59
def prefixEnd_2423843 : Nat := 4983230072969 + 3 ^ 40 * 2423843 * 2
def baseEnd_2423843 : Nat := 1244596490035865436815455

theorem tailTrace_2423843 : CollatzResearch.WordTrace tailWord_2423843 prefixEnd_2423843 1244596490035865436815455 := by
  unfold tailWord_2423843
  simp only [CollatzResearch.WordTrace]
  refine ⟨88404816957838245272516183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58936544638558830181677455 88404816957838245272516183)
  ·
    refine ⟨132607225436757367908774275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88404816957838245272516183 132607225436757367908774275)
    ·
      refine ⟨198910838155136051863161413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 132607225436757367908774275 198910838155136051863161413)
      ·
        refine ⟨37295782154088009724342765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 198910838155136051863161413 37295782154088009724342765)
        ·
          refine ⟨13985918307783003646628537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37295782154088009724342765 13985918307783003646628537)
          ·
            refine ⟨10489438730837252734971403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13985918307783003646628537 10489438730837252734971403)
            ·
              refine ⟨15734158096255879102457105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10489438730837252734971403 15734158096255879102457105)
              ·
                refine ⟨11800618572191909326842829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15734158096255879102457105 11800618572191909326842829)
                ·
                  refine ⟨4425231964571965997566061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11800618572191909326842829 4425231964571965997566061)
                  ·
                    refine ⟨1659461986714487249087273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4425231964571965997566061 1659461986714487249087273)
                    ·
                      refine ⟨1244596490035865436815455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1659461986714487249087273 1244596490035865436815455)
                      ·
                        rfl

theorem cell23_2423843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_2423843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423843 prefixEnd_2423843 := by exact prefixLift 2423843
  have htrace : WordTrace (prefixWord ++ tailWord_2423843) baseStart_2423843 baseEnd_2423843 := by
    simpa [prefixWord, tailWord_2423843, baseEnd_2423843] using wordTrace_append hprefix tailTrace_2423843
  have hstable : (prefixWord ++ tailWord_2423843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423843).length < 2 ^ (prefixWord ++ tailWord_2423843).sum := by decide
  have hdescent : baseEnd_2423843 < baseStart_2423843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423850 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3]
def baseStart_2423850 : Nat := 118140960795 + 2423850 * 2 ^ 59
def prefixEnd_2423850 : Nat := 4983230072969 + 3 ^ 40 * 2423850 * 2
def baseEnd_2423850 : Nat := 1244600084400446909427923

theorem tailTrace_2423850 : CollatzResearch.WordTrace tailWord_2423850 prefixEnd_2423850 1244600084400446909427923 := by
  unfold tailWord_2423850
  simp only [CollatzResearch.WordTrace]
  refine ⟨22101268067203221367005251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58936714845875256978680669 22101268067203221367005251)
  ·
    refine ⟨33151902100804832050507877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22101268067203221367005251 33151902100804832050507877)
    ·
      refine ⟨6215981643900906009470227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33151902100804832050507877 6215981643900906009470227)
      ·
        refine ⟨9323972465851359014205341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6215981643900906009470227 9323972465851359014205341)
        ·
          refine ⟨3496489674694259630327003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9323972465851359014205341 3496489674694259630327003)
          ·
            refine ⟨5244734512041389445490505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3496489674694259630327003 5244734512041389445490505)
            ·
              refine ⟨3933550884031042084117879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5244734512041389445490505 3933550884031042084117879)
              ·
                refine ⟨5900326326046563126176819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933550884031042084117879 5900326326046563126176819)
                ·
                  refine ⟨8850489489069844689265229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5900326326046563126176819 8850489489069844689265229)
                  ·
                    refine ⟨3318933558401191758474461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8850489489069844689265229 3318933558401191758474461)
                    ·
                      refine ⟨1244600084400446909427923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3318933558401191758474461 1244600084400446909427923)
                      ·
                        rfl

theorem cell23_2423850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_2423850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423850 prefixEnd_2423850 := by exact prefixLift 2423850
  have htrace : WordTrace (prefixWord ++ tailWord_2423850) baseStart_2423850 baseEnd_2423850 := by
    simpa [prefixWord, tailWord_2423850, baseEnd_2423850] using wordTrace_append hprefix tailTrace_2423850
  have hstable : (prefixWord ++ tailWord_2423850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423850).length < 2 ^ (prefixWord ++ tailWord_2423850).sum := by decide
  have hdescent : baseEnd_2423850 < baseStart_2423850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423886 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4]
def baseStart_2423886 : Nat := 118140960795 + 2423886 * 2 ^ 59
def prefixEnd_2423886 : Nat := 4983230072969 + 3 ^ 40 * 2423886 * 2
def baseEnd_2423886 : Nat := 1244618569704008768577757

theorem tailTrace_2423886 : CollatzResearch.WordTrace tailWord_2423886 prefixEnd_2423886 1244618569704008768577757 := by
  unfold tailWord_2423886
  simp only [CollatzResearch.WordTrace]
  refine ⟨11050798162085307952041439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58937590197788309077554341 11050798162085307952041439)
  ·
    refine ⟨16576197243127961928062159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11050798162085307952041439 16576197243127961928062159)
    ·
      refine ⟨24864295864691942892093239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16576197243127961928062159 24864295864691942892093239)
      ·
        refine ⟨37296443797037914338139859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24864295864691942892093239 37296443797037914338139859)
        ·
          refine ⟨55944665695556871507209789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37296443797037914338139859 55944665695556871507209789)
          ·
            refine ⟨20979249635833826815203671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55944665695556871507209789 20979249635833826815203671)
            ·
              refine ⟨31468874453750740222805507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20979249635833826815203671 31468874453750740222805507)
              ·
                refine ⟨47203311680626110334208261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31468874453750740222805507 47203311680626110334208261)
                ·
                  refine ⟨8850620940117395687664049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47203311680626110334208261 8850620940117395687664049)
                  ·
                    refine ⟨6637965705088046765748037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8850620940117395687664049 6637965705088046765748037)
                    ·
                      refine ⟨1244618569704008768577757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6637965705088046765748037 1244618569704008768577757)
                      ·
                        rfl

theorem cell23_2423886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_2423886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423886 prefixEnd_2423886 := by exact prefixLift 2423886
  have htrace : WordTrace (prefixWord ++ tailWord_2423886) baseStart_2423886 baseEnd_2423886 := by
    simpa [prefixWord, tailWord_2423886, baseEnd_2423886] using wordTrace_append hprefix tailTrace_2423886
  have hstable : (prefixWord ++ tailWord_2423886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423886).length < 2 ^ (prefixWord ++ tailWord_2423886).sum := by decide
  have hdescent : baseEnd_2423886 < baseStart_2423886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423896 : List Nat := [2, 1, 2, 2, 1, 3, 4, 1, 7]
def baseStart_2423896 : Nat := 118140960795 + 2423896 * 2 ^ 59
def prefixEnd_2423896 : Nat := 4983230072969 + 3 ^ 40 * 2423896 * 2
def baseEnd_2423896 : Nat := 138291522723394858828079

theorem tailTrace_2423896 : CollatzResearch.WordTrace tailWord_2423896 prefixEnd_2423896 138291522723394858828079 := by
  unfold tailWord_2423896
  simp only [CollatzResearch.WordTrace]
  refine ⟨44203375013323117662097771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58937833351097490216130361 44203375013323117662097771)
  ·
    refine ⟨66305062519984676493146657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44203375013323117662097771 66305062519984676493146657)
    ·
      refine ⟨49728796889988507369859993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66305062519984676493146657 49728796889988507369859993)
      ·
        refine ⟨37296597667491380527394995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49728796889988507369859993 37296597667491380527394995)
        ·
          refine ⟨55944896501237070791092493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37296597667491380527394995 55944896501237070791092493)
          ·
            refine ⟨20979336187963901546659685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55944896501237070791092493 20979336187963901546659685)
            ·
              refine ⟨3933625535243231539998691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20979336187963901546659685 3933625535243231539998691)
              ·
                refine ⟨5900438302864847309998037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3933625535243231539998691 5900438302864847309998037)
                ·
                  refine ⟨138291522723394858828079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5900438302864847309998037 138291522723394858828079)
                  ·
                    rfl

theorem cell23_2423896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 4, 1, 7].length) (baseStart_2423896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423896 prefixEnd_2423896 := by exact prefixLift 2423896
  have htrace : WordTrace (prefixWord ++ tailWord_2423896) baseStart_2423896 baseEnd_2423896 := by
    simpa [prefixWord, tailWord_2423896, baseEnd_2423896] using wordTrace_append hprefix tailTrace_2423896
  have hstable : (prefixWord ++ tailWord_2423896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423896).length < 2 ^ (prefixWord ++ tailWord_2423896).sum := by decide
  have hdescent : baseEnd_2423896 < baseStart_2423896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2423983 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 3]
def baseStart_2423983 : Nat := 118140960795 + 2423983 * 2 ^ 59
def prefixEnd_2423983 : Nat := 4983230072969 + 3 ^ 40 * 2423983 * 2
def baseEnd_2423983 : Nat := 1244668377327494889064811

theorem tailTrace_2423983 : CollatzResearch.WordTrace tailWord_2423983 prefixEnd_2423983 1244668377327494889064811 := by
  unfold tailWord_2423983
  simp only [CollatzResearch.WordTrace]
  refine ⟨88409923177331049182612603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58939948784887366121741735 88409923177331049182612603)
  ·
    refine ⟨132614884765996573773918905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88409923177331049182612603 132614884765996573773918905)
    ·
      refine ⟨99461163574497430330439179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132614884765996573773918905 99461163574497430330439179)
      ·
        refine ⟨149191745361746145495658769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99461163574497430330439179 149191745361746145495658769)
        ·
          refine ⟨111893809021309609121744077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149191745361746145495658769 111893809021309609121744077)
          ·
            refine ⟨41960178382991103420654029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 111893809021309609121744077 41960178382991103420654029)
            ·
              refine ⟨15735066893621663782745261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41960178382991103420654029 15735066893621663782745261)
              ·
                refine ⟨5900650085108123918529473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15735066893621663782745261 5900650085108123918529473)
                ·
                  refine ⟨4425487563831092938897105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5900650085108123918529473 4425487563831092938897105)
                  ·
                    refine ⟨3319115672873319704172829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4425487563831092938897105 3319115672873319704172829)
                    ·
                      refine ⟨1244668377327494889064811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3319115672873319704172829 1244668377327494889064811)
                      ·
                        rfl

theorem cell23_2423983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 3].length) (baseStart_2423983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2423983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2423983 prefixEnd_2423983 := by exact prefixLift 2423983
  have htrace : WordTrace (prefixWord ++ tailWord_2423983) baseStart_2423983 baseEnd_2423983 := by
    simpa [prefixWord, tailWord_2423983, baseEnd_2423983] using wordTrace_append hprefix tailTrace_2423983
  have hstable : (prefixWord ++ tailWord_2423983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2423983).length < 2 ^ (prefixWord ++ tailWord_2423983).sum := by decide
  have hdescent : baseEnd_2423983 < baseStart_2423983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2423983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
