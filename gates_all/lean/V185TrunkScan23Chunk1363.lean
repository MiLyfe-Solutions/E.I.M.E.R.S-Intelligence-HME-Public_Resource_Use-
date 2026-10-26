import V185TrunkScan23Chunk1362

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8072218 : List Nat := [3, 1, 1, 3, 1, 2, 5, 7]
def baseStart_8072218 : Nat := 118140960795 + 8072218 * 2 ^ 59
def prefixEnd_8072218 : Nat := 4983230072969 + 3 ^ 40 * 8072218 * 2
def baseEnd_8072218 : Nat := 153515843773155690505613

theorem tailTrace_8072218 : CollatzResearch.WordTrace tailWord_8072218 prefixEnd_8072218 153515843773155690505613 := by
  unfold tailWord_8072218
  simp only [CollatzResearch.WordTrace]
  refine ⟨73604494467435071480390327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196278651913160190614374205 73604494467435071480390327)
  ·
    refine ⟨110406741701152607220585491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73604494467435071480390327 110406741701152607220585491)
    ·
      refine ⟨165610112551728910830878237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110406741701152607220585491 165610112551728910830878237)
      ·
        refine ⟨62103792206898341561579339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165610112551728910830878237 62103792206898341561579339)
        ·
          refine ⟨93155688310347512342369009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62103792206898341561579339 93155688310347512342369009)
          ·
            refine ⟨69866766232760634256776757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93155688310347512342369009 69866766232760634256776757)
            ·
              refine ⟨6550009334321309461572821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69866766232760634256776757 6550009334321309461572821)
              ·
                refine ⟨153515843773155690505613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6550009334321309461572821 153515843773155690505613)
                ·
                  rfl

theorem cell23_8072218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 5, 7].length) (baseStart_8072218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072218 prefixEnd_8072218 := by exact prefixLift 8072218
  have htrace : WordTrace (prefixWord ++ tailWord_8072218) baseStart_8072218 baseEnd_8072218 := by
    simpa [prefixWord, tailWord_8072218, baseEnd_8072218] using wordTrace_append hprefix tailTrace_8072218
  have hstable : (prefixWord ++ tailWord_8072218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072218).length < 2 ^ (prefixWord ++ tailWord_8072218).sum := by decide
  have hdescent : baseEnd_8072218 < baseStart_8072218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072229 : List Nat := [1, 3, 1, 2, 2, 2, 4, 3, 1, 2, 2]
def baseStart_8072229 : Nat := 118140960795 + 8072229 * 2 ^ 59
def prefixEnd_8072229 : Nat := 4983230072969 + 3 ^ 40 * 8072229 * 2
def baseEnd_8072229 : Nat := 4144933430162403100614001

theorem tailTrace_8072229 : CollatzResearch.WordTrace tailWord_8072229 prefixEnd_8072229 4144933430162403100614001 := by
  unfold tailWord_8072229
  simp only [CollatzResearch.WordTrace]
  refine ⟨294418379072700434800211741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196278919381800289866807827 294418379072700434800211741)
  ·
    refine ⟨110406892152262663050079403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294418379072700434800211741 110406892152262663050079403)
    ·
      refine ⟨165610338228393994575119105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110406892152262663050079403 165610338228393994575119105)
      ·
        refine ⟨124207753671295495931339329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165610338228393994575119105 124207753671295495931339329)
        ·
          refine ⟨93155815253471621948504497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124207753671295495931339329 93155815253471621948504497)
          ·
            refine ⟨69866861440103716461378373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93155815253471621948504497 69866861440103716461378373)
            ·
              refine ⟨13100036520019446836508445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69866861440103716461378373 13100036520019446836508445)
              ·
                refine ⟨4912513695007292563690667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13100036520019446836508445 4912513695007292563690667)
                ·
                  refine ⟨7368770542510938845536001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912513695007292563690667 7368770542510938845536001)
                  ·
                    refine ⟨5526577906883204134152001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368770542510938845536001 5526577906883204134152001)
                    ·
                      refine ⟨4144933430162403100614001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526577906883204134152001 4144933430162403100614001)
                      ·
                        rfl

theorem cell23_8072229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 1, 2, 2].length) (baseStart_8072229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072229 prefixEnd_8072229 := by exact prefixLift 8072229
  have htrace : WordTrace (prefixWord ++ tailWord_8072229) baseStart_8072229 baseEnd_8072229 := by
    simpa [prefixWord, tailWord_8072229, baseEnd_8072229] using wordTrace_append hprefix tailTrace_8072229
  have hstable : (prefixWord ++ tailWord_8072229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072229).length < 2 ^ (prefixWord ++ tailWord_8072229).sum := by decide
  have hdescent : baseEnd_8072229 < baseStart_8072229 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072246 : List Nat := [5, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_8072246 : Nat := 118140960795 + 8072246 * 2 ^ 59
def prefixEnd_8072246 : Nat := 4983230072969 + 3 ^ 40 * 8072246 * 2
def baseEnd_8072246 : Nat := 4144942159333529534101423

theorem tailTrace_8072246 : CollatzResearch.WordTrace tailWord_8072246 prefixEnd_8072246 4144942159333529534101423 := by
  unfold tailWord_8072246
  simp only [CollatzResearch.WordTrace]
  refine ⟨18401187444602427918973787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196279332742425897802387061 18401187444602427918973787)
  ·
    refine ⟨27601781166903641878460681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18401187444602427918973787 27601781166903641878460681)
    ·
      refine ⟨20701335875177731408845511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27601781166903641878460681 20701335875177731408845511)
      ·
        refine ⟨31052003812766597113268267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20701335875177731408845511 31052003812766597113268267)
        ·
          refine ⟨46578005719149895669902401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31052003812766597113268267 46578005719149895669902401)
          ·
            refine ⟨34933504289362421752426801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46578005719149895669902401 34933504289362421752426801)
            ·
              refine ⟨26200128217021816314320101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34933504289362421752426801 26200128217021816314320101)
              ·
                refine ⟨4912524040691590558935019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26200128217021816314320101 4912524040691590558935019)
                ·
                  refine ⟨7368786061037385838402529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912524040691590558935019 7368786061037385838402529)
                  ·
                    refine ⟨5526589545778039378801897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7368786061037385838402529 5526589545778039378801897)
                    ·
                      refine ⟨4144942159333529534101423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526589545778039378801897 4144942159333529534101423)
                      ·
                        rfl

theorem cell23_8072246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_8072246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072246 prefixEnd_8072246 := by exact prefixLift 8072246
  have htrace : WordTrace (prefixWord ++ tailWord_8072246) baseStart_8072246 baseEnd_8072246 := by
    simpa [prefixWord, tailWord_8072246, baseEnd_8072246] using wordTrace_append hprefix tailTrace_8072246
  have hstable : (prefixWord ++ tailWord_8072246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072246).length < 2 ^ (prefixWord ++ tailWord_8072246).sum := by decide
  have hdescent : baseEnd_8072246 < baseStart_8072246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072288 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_8072288 : Nat := 118140960795 + 8072288 * 2 ^ 59
def prefixEnd_8072288 : Nat := 4983230072969 + 3 ^ 40 * 8072288 * 2
def baseEnd_8072288 : Nat := 4144963725521018369776229

theorem tailTrace_8072288 : CollatzResearch.WordTrace tailWord_8072288 prefixEnd_8072288 4144963725521018369776229 := by
  unfold tailWord_8072288
  simp only [CollatzResearch.WordTrace]
  refine ⟨147210265489743343938304759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196280353986324458584406345 147210265489743343938304759)
  ·
    refine ⟨220815398234615015907457139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147210265489743343938304759 220815398234615015907457139)
    ·
      refine ⟨331223097351922523861185709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220815398234615015907457139 331223097351922523861185709)
      ·
        refine ⟨124208661506970946447944641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331223097351922523861185709 124208661506970946447944641)
        ·
          refine ⟨93156496130228209835958481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124208661506970946447944641 93156496130228209835958481)
          ·
            refine ⟨69867372097671157376968861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93156496130228209835958481 69867372097671157376968861)
            ·
              refine ⟨26200264536626684016363323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69867372097671157376968861 26200264536626684016363323)
              ·
                refine ⟨39300396804940026024544985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26200264536626684016363323 39300396804940026024544985)
                ·
                  refine ⟨29475297603705019518408739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39300396804940026024544985 29475297603705019518408739)
                  ·
                    refine ⟨44212946405557529277613109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29475297603705019518408739 44212946405557529277613109)
                    ·
                      refine ⟨4144963725521018369776229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44212946405557529277613109 4144963725521018369776229)
                      ·
                        rfl

theorem cell23_8072288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_8072288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072288 prefixEnd_8072288 := by exact prefixLift 8072288
  have htrace : WordTrace (prefixWord ++ tailWord_8072288) baseStart_8072288 baseEnd_8072288 := by
    simpa [prefixWord, tailWord_8072288, baseEnd_8072288] using wordTrace_append hprefix tailTrace_8072288
  have hstable : (prefixWord ++ tailWord_8072288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072288).length < 2 ^ (prefixWord ++ tailWord_8072288).sum := by decide
  have hdescent : baseEnd_8072288 < baseStart_8072288 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072359 : List Nat := [1, 1, 6, 2, 1, 1, 4, 2, 5]
def baseStart_8072359 : Nat := 118140960795 + 8072359 * 2 ^ 59
def prefixEnd_8072359 : Nat := 4983230072969 + 3 ^ 40 * 8072359 * 2
def baseEnd_8072359 : Nat := 460555575849720843554267

theorem tailTrace_8072359 : CollatzResearch.WordTrace tailWord_8072359 prefixEnd_8072359 460555575849720843554267 := by
  unfold tailWord_8072359
  simp only [CollatzResearch.WordTrace]
  refine ⟨294423120562229467002444131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196282080374819644668296087 294423120562229467002444131)
  ·
    refine ⟨441634680843344200503666197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294423120562229467002444131 441634680843344200503666197)
    ·
      refine ⟨20701625664531759398609353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 441634680843344200503666197 20701625664531759398609353)
      ·
        refine ⟨15526219248398819548957015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20701625664531759398609353 15526219248398819548957015)
        ·
          refine ⟨23289328872598229323435523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15526219248398819548957015 23289328872598229323435523)
          ·
            refine ⟨34933993308897343985153285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23289328872598229323435523 34933993308897343985153285)
            ·
              refine ⟨6550123745418251997216241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34933993308897343985153285 6550123745418251997216241)
              ·
                refine ⟨4912592809063688997912181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550123745418251997216241 4912592809063688997912181)
                ·
                  refine ⟨460555575849720843554267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4912592809063688997912181 460555575849720843554267)
                  ·
                    rfl

theorem cell23_8072359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 2, 5].length) (baseStart_8072359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072359 prefixEnd_8072359 := by exact prefixLift 8072359
  have htrace : WordTrace (prefixWord ++ tailWord_8072359) baseStart_8072359 baseEnd_8072359 := by
    simpa [prefixWord, tailWord_8072359, baseEnd_8072359] using wordTrace_append hprefix tailTrace_8072359
  have hstable : (prefixWord ++ tailWord_8072359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072359).length < 2 ^ (prefixWord ++ tailWord_8072359).sum := by decide
  have hdescent : baseEnd_8072359 < baseStart_8072359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072395 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 3]
def baseStart_8072395 : Nat := 118140960795 + 8072395 * 2 ^ 59
def prefixEnd_8072395 : Nat := 4983230072969 + 3 ^ 40 * 8072395 * 2
def baseEnd_8072395 : Nat := 4145018667951049451138237

theorem tailTrace_8072395 : CollatzResearch.WordTrace tailWord_8072395 prefixEnd_8072395 4145018667951049451138237 := by
  unfold tailWord_8072395
  simp only [CollatzResearch.WordTrace]
  refine ⟨294424433590099045150754639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196282955726732696767169759 294424433590099045150754639)
  ·
    refine ⟨441636650385148567726131959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294424433590099045150754639 441636650385148567726131959)
    ·
      refine ⟨662454975577722851589197939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441636650385148567726131959 662454975577722851589197939)
      ·
        refine ⟨993682463366584277383796909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662454975577722851589197939 993682463366584277383796909)
        ·
          refine ⟨372630923762469104018923841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 993682463366584277383796909 372630923762469104018923841)
          ·
            refine ⟨279473192821851828014192881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372630923762469104018923841 279473192821851828014192881)
            ·
              refine ⟨209604894616388871010644661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279473192821851828014192881 209604894616388871010644661)
              ·
                refine ⟨19650458870286456657247937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209604894616388871010644661 19650458870286456657247937)
                ·
                  refine ⟨14737844152714842492935953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19650458870286456657247937 14737844152714842492935953)
                  ·
                    refine ⟨11053383114536131869701965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14737844152714842492935953 11053383114536131869701965)
                    ·
                      refine ⟨4145018667951049451138237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11053383114536131869701965 4145018667951049451138237)
                      ·
                        rfl

theorem cell23_8072395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 2, 2, 3].length) (baseStart_8072395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072395 prefixEnd_8072395 := by exact prefixLift 8072395
  have htrace : WordTrace (prefixWord ++ tailWord_8072395) baseStart_8072395 baseEnd_8072395 := by
    simpa [prefixWord, tailWord_8072395, baseEnd_8072395] using wordTrace_append hprefix tailTrace_8072395
  have hstable : (prefixWord ++ tailWord_8072395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072395).length < 2 ^ (prefixWord ++ tailWord_8072395).sum := by decide
  have hdescent : baseEnd_8072395 < baseStart_8072395 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072405 : List Nat := [1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 6]
def baseStart_8072405 : Nat := 118140960795 + 8072405 * 2 ^ 59
def prefixEnd_8072405 : Nat := 4983230072969 + 3 ^ 40 * 8072405 * 2
def baseEnd_8072405 : Nat := 4145023802757594412013191

theorem tailTrace_8072405 : CollatzResearch.WordTrace tailWord_8072405 prefixEnd_8072405 4145023802757594412013191 := by
  unfold tailWord_8072405
  simp only [CollatzResearch.WordTrace]
  refine ⟨294424798320062816858618669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196283198880041877905745779 294424798320062816858618669)
  ·
    refine ⟨110409299370023556321982001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294424798320062816858618669 110409299370023556321982001)
    ·
      refine ⟨82806974527517667241486501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110409299370023556321982001 82806974527517667241486501)
      ·
        refine ⟨15526307723909562607778719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82806974527517667241486501 15526307723909562607778719)
        ·
          refine ⟨23289461585864343911668079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15526307723909562607778719 23289461585864343911668079)
          ·
            refine ⟨34934192378796515867502119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23289461585864343911668079 34934192378796515867502119)
            ·
              refine ⟨52401288568194773801253179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34934192378796515867502119 52401288568194773801253179)
              ·
                refine ⟨78601932852292160701879769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52401288568194773801253179 78601932852292160701879769)
                ·
                  refine ⟨58951449639219120526409827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78601932852292160701879769 58951449639219120526409827)
                  ·
                    refine ⟨88427174458828680789614741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58951449639219120526409827 88427174458828680789614741)
                    ·
                      refine ⟨4145023802757594412013191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88427174458828680789614741 4145023802757594412013191)
                      ·
                        rfl

theorem cell23_8072405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_8072405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072405 prefixEnd_8072405 := by exact prefixLift 8072405
  have htrace : WordTrace (prefixWord ++ tailWord_8072405) baseStart_8072405 baseEnd_8072405 := by
    simpa [prefixWord, tailWord_8072405, baseEnd_8072405] using wordTrace_append hprefix tailTrace_8072405
  have hstable : (prefixWord ++ tailWord_8072405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072405).length < 2 ^ (prefixWord ++ tailWord_8072405).sum := by decide
  have hdescent : baseEnd_8072405 < baseStart_8072405 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072415 : List Nat := [1, 1, 2, 3, 2, 1, 5, 2, 6]
def baseStart_8072415 : Nat := 118140960795 + 8072415 * 2 ^ 59
def prefixEnd_8072415 : Nat := 4983230072969 + 3 ^ 40 * 8072415 * 2
def baseEnd_8072415 : Nat := 460558770840459930320905

theorem tailTrace_8072415 : CollatzResearch.WordTrace tailWord_8072415 prefixEnd_8072415 460558770840459930320905 := by
  unfold tailWord_8072415
  simp only [CollatzResearch.WordTrace]
  refine ⟨294425163050026588566482699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196283442033351059044321799 294425163050026588566482699)
  ·
    refine ⟨441637744575039882849724049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294425163050026588566482699 441637744575039882849724049)
    ·
      refine ⟨331228308431279912137293037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441637744575039882849724049 331228308431279912137293037)
      ·
        refine ⟨124210615661729967051484889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331228308431279912137293037 124210615661729967051484889)
        ·
          refine ⟨93157961746297475288613667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124210615661729967051484889 93157961746297475288613667)
          ·
            refine ⟨139736942619446212932920501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93157961746297475288613667 139736942619446212932920501)
            ·
              refine ⟨13100338370573082462461297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139736942619446212932920501 13100338370573082462461297)
              ·
                refine ⟨9825253777929811846845973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13100338370573082462461297 9825253777929811846845973)
                ·
                  refine ⟨460558770840459930320905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9825253777929811846845973 460558770840459930320905)
                  ·
                    rfl

theorem cell23_8072415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 5, 2, 6].length) (baseStart_8072415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072415 prefixEnd_8072415 := by exact prefixLift 8072415
  have htrace : WordTrace (prefixWord ++ tailWord_8072415) baseStart_8072415 baseEnd_8072415 := by
    simpa [prefixWord, tailWord_8072415, baseEnd_8072415] using wordTrace_append hprefix tailTrace_8072415
  have hstable : (prefixWord ++ tailWord_8072415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072415).length < 2 ^ (prefixWord ++ tailWord_8072415).sum := by decide
  have hdescent : baseEnd_8072415 < baseStart_8072415 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072442 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3]
def baseStart_8072442 : Nat := 118140960795 + 8072442 * 2 ^ 59
def prefixEnd_8072442 : Nat := 4983230072969 + 3 ^ 40 * 8072442 * 2
def baseEnd_8072442 : Nat := 4145042801541810767250521

theorem tailTrace_8072442 : CollatzResearch.WordTrace tailWord_8072442 prefixEnd_8072442 4145042801541810767250521 := by
  unfold tailWord_8072442
  simp only [CollatzResearch.WordTrace]
  refine ⟨73606536955232193044428895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196284098547285848118477053 73606536955232193044428895)
  ·
    refine ⟨110409805432848289566643343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73606536955232193044428895 110409805432848289566643343)
    ·
      refine ⟨165614708149272434349965015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110409805432848289566643343 165614708149272434349965015)
      ·
        refine ⟨248422062223908651524947523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165614708149272434349965015 248422062223908651524947523)
        ·
          refine ⟨372633093335862977287421285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248422062223908651524947523 372633093335862977287421285)
          ·
            refine ⟨69868705000474308241391491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372633093335862977287421285 69868705000474308241391491)
            ·
              refine ⟨104803057500711462362087237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69868705000474308241391491 104803057500711462362087237)
              ·
                refine ⟨19650573281383399192891357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104803057500711462362087237 19650573281383399192891357)
                ·
                  refine ⟨7368964980518774697334259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19650573281383399192891357 7368964980518774697334259)
                  ·
                    refine ⟨11053447470778162046001389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7368964980518774697334259 11053447470778162046001389)
                    ·
                      refine ⟨4145042801541810767250521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11053447470778162046001389 4145042801541810767250521)
                      ·
                        rfl

theorem cell23_8072442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 3, 1, 3].length) (baseStart_8072442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072442 prefixEnd_8072442 := by exact prefixLift 8072442
  have htrace : WordTrace (prefixWord ++ tailWord_8072442) baseStart_8072442 baseEnd_8072442 := by
    simpa [prefixWord, tailWord_8072442, baseEnd_8072442] using wordTrace_append hprefix tailTrace_8072442
  have hstable : (prefixWord ++ tailWord_8072442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072442).length < 2 ^ (prefixWord ++ tailWord_8072442).sum := by decide
  have hdescent : baseEnd_8072442 < baseStart_8072442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072462 : List Nat := [4, 1, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_8072462 : Nat := 118140960795 + 8072462 * 2 ^ 59
def prefixEnd_8072462 : Nat := 4983230072969 + 3 ^ 40 * 8072462 * 2
def baseEnd_8072462 : Nat := 1381684357051633563000143

theorem tailTrace_8072462 : CollatzResearch.WordTrace tailWord_8072462 prefixEnd_8072462 1381684357051633563000143 := by
  unfold tailWord_8072462
  simp only [CollatzResearch.WordTrace]
  refine ⟨36803359660107039449180455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196284584853904210395629093 36803359660107039449180455)
  ·
    refine ⟨55205039490160559173770683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36803359660107039449180455 55205039490160559173770683)
    ·
      refine ⟨82807559235240838760656025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55205039490160559173770683 82807559235240838760656025)
      ·
        refine ⟨62105669426430629070492019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82807559235240838760656025 62105669426430629070492019)
        ·
          refine ⟨93158504139645943605738029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62105669426430629070492019 93158504139645943605738029)
          ·
            refine ⟨34934439052367228852151761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93158504139645943605738029 34934439052367228852151761)
            ·
              refine ⟨26200829289275421639113821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34934439052367228852151761 26200829289275421639113821)
              ·
                refine ⟨9825310983478283114667683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26200829289275421639113821 9825310983478283114667683)
                ·
                  refine ⟨14737966475217424672001525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9825310983478283114667683 14737966475217424672001525)
                  ·
                    refine ⟨1381684357051633563000143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14737966475217424672001525 1381684357051633563000143)
                    ·
                      rfl

theorem cell23_8072462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_8072462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072462 prefixEnd_8072462 := by exact prefixLift 8072462
  have htrace : WordTrace (prefixWord ++ tailWord_8072462) baseStart_8072462 baseEnd_8072462 := by
    simpa [prefixWord, tailWord_8072462, baseEnd_8072462] using wordTrace_append hprefix tailTrace_8072462
  have hstable : (prefixWord ++ tailWord_8072462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072462).length < 2 ^ (prefixWord ++ tailWord_8072462).sum := by decide
  have hdescent : baseEnd_8072462 < baseStart_8072462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072495 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 4]
def baseStart_8072495 : Nat := 118140960795 + 8072495 * 2 ^ 59
def prefixEnd_8072495 : Nat := 4983230072969 + 3 ^ 40 * 8072495 * 2
def baseEnd_8072495 : Nat := 4145070016016499059887777

theorem tailTrace_8072495 : CollatzResearch.WordTrace tailWord_8072495 prefixEnd_8072495 4145070016016499059887777 := by
  unfold tailWord_8072495
  simp only [CollatzResearch.WordTrace]
  refine ⟨294428080889736762229394939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196285387259824508152929959 294428080889736762229394939)
  ·
    refine ⟨441642121334605143344092409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294428080889736762229394939 441642121334605143344092409)
    ·
      refine ⟨331231591000953857508069307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441642121334605143344092409 331231591000953857508069307)
      ·
        refine ⟨496847386501430786262103961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331231591000953857508069307 496847386501430786262103961)
        ·
          refine ⟨372635539876073089696577971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496847386501430786262103961 372635539876073089696577971)
          ·
            refine ⟨558953309814109634544866957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372635539876073089696577971 558953309814109634544866957)
            ·
              refine ⟨209607491180291112954325109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558953309814109634544866957 209607491180291112954325109)
              ·
                refine ⟨19650702298152291839467979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209607491180291112954325109 19650702298152291839467979)
                ·
                  refine ⟨29476053447228437759201969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19650702298152291839467979 29476053447228437759201969)
                  ·
                    refine ⟨22107040085421328319401477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29476053447228437759201969 22107040085421328319401477)
                    ·
                      refine ⟨4145070016016499059887777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22107040085421328319401477 4145070016016499059887777)
                      ·
                        rfl

theorem cell23_8072495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_8072495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072495 prefixEnd_8072495 := by exact prefixLift 8072495
  have htrace : WordTrace (prefixWord ++ tailWord_8072495) baseStart_8072495 baseEnd_8072495 := by
    simpa [prefixWord, tailWord_8072495, baseEnd_8072495] using wordTrace_append hprefix tailTrace_8072495
  have hstable : (prefixWord ++ tailWord_8072495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072495).length < 2 ^ (prefixWord ++ tailWord_8072495).sum := by decide
  have hdescent : baseEnd_8072495 < baseStart_8072495 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072499 : List Nat := [1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 4]
def baseStart_8072499 : Nat := 118140960795 + 8072499 * 2 ^ 59
def prefixEnd_8072499 : Nat := 4983230072969 + 3 ^ 40 * 8072499 * 2
def baseEnd_8072499 : Nat := 4145072069939117044237759

theorem tailTrace_8072499 : CollatzResearch.WordTrace tailWord_8072499 prefixEnd_8072499 4145072069939117044237759 := by
  unfold tailWord_8072499
  simp only [CollatzResearch.WordTrace]
  refine ⟨294428226781722270912540551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196285484521148180608360367 294428226781722270912540551)
  ·
    refine ⟨441642340172583406368810827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294428226781722270912540551 441642340172583406368810827)
    ·
      refine ⟨662463510258875109553216241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441642340172583406368810827 662463510258875109553216241)
      ·
        refine ⟨496847632694156332164912181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662463510258875109553216241 496847632694156332164912181)
        ·
          refine ⟨46579465565077156140460517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 496847632694156332164912181 46579465565077156140460517)
          ·
            refine ⟨8733649793451966776336347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46579465565077156140460517 8733649793451966776336347)
            ·
              refine ⟨13100474690177950164504521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8733649793451966776336347 13100474690177950164504521)
              ·
                refine ⟨9825356017633462623378391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13100474690177950164504521 9825356017633462623378391)
                ·
                  refine ⟨14738034026450193935067587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9825356017633462623378391 14738034026450193935067587)
                  ·
                    refine ⟨22107051039675290902601381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14738034026450193935067587 22107051039675290902601381)
                    ·
                      refine ⟨4145072069939117044237759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22107051039675290902601381 4145072069939117044237759)
                      ·
                        rfl

theorem cell23_8072499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 2, 1, 1, 4].length) (baseStart_8072499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072499 prefixEnd_8072499 := by exact prefixLift 8072499
  have htrace : WordTrace (prefixWord ++ tailWord_8072499) baseStart_8072499 baseEnd_8072499 := by
    simpa [prefixWord, tailWord_8072499, baseEnd_8072499] using wordTrace_append hprefix tailTrace_8072499
  have hstable : (prefixWord ++ tailWord_8072499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072499).length < 2 ^ (prefixWord ++ tailWord_8072499).sum := by decide
  have hdescent : baseEnd_8072499 < baseStart_8072499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072509 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_8072509 : Nat := 118140960795 + 8072509 * 2 ^ 59
def prefixEnd_8072509 : Nat := 4983230072969 + 3 ^ 40 * 8072509 * 2
def baseEnd_8072509 : Nat := 1381692401581887335037571

theorem tailTrace_8072509 : CollatzResearch.WordTrace tailWord_8072509 prefixEnd_8072509 1381692401581887335037571 := by
  unfold tailWord_8072509
  simp only [CollatzResearch.WordTrace]
  refine ⟨294428591511686042620404581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196285727674457361746936387 294428591511686042620404581)
  ·
    refine ⟨55205360908441132991325859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294428591511686042620404581 55205360908441132991325859)
    ·
      refine ⟨82808041362661699486988789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55205360908441132991325859 82808041362661699486988789)
      ·
        refine ⟨7763253877749534326905199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82808041362661699486988789 7763253877749534326905199)
        ·
          refine ⟨11644880816624301490357799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7763253877749534326905199 11644880816624301490357799)
          ·
            refine ⟨17467321224936452235536699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11644880816624301490357799 17467321224936452235536699)
            ·
              refine ⟨26200981837404678353305049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17467321224936452235536699 26200981837404678353305049)
              ·
                refine ⟨19650736378053508764978787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26200981837404678353305049 19650736378053508764978787)
                ·
                  refine ⟨29476104567080263147468181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19650736378053508764978787 29476104567080263147468181)
                  ·
                    refine ⟨1381692401581887335037571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29476104567080263147468181 1381692401581887335037571)
                    ·
                      rfl

theorem cell23_8072509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_8072509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072509 prefixEnd_8072509 := by exact prefixLift 8072509
  have htrace : WordTrace (prefixWord ++ tailWord_8072509) baseStart_8072509 baseEnd_8072509 := by
    simpa [prefixWord, tailWord_8072509, baseEnd_8072509] using wordTrace_append hprefix tailTrace_8072509
  have hstable : (prefixWord ++ tailWord_8072509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072509).length < 2 ^ (prefixWord ++ tailWord_8072509).sum := by decide
  have hdescent : baseEnd_8072509 < baseStart_8072509 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072532 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 3, 3, 3]
def baseStart_8072532 : Nat := 118140960795 + 8072532 * 2 ^ 59
def prefixEnd_8072532 : Nat := 4983230072969 + 3 ^ 40 * 8072532 * 2
def baseEnd_8072532 : Nat := 4145089014800715415125107

theorem tailTrace_8072532 : CollatzResearch.WordTrace tailWord_8072532 prefixEnd_8072532 4145089014800715415125107 := by
  unfold tailWord_8072532
  simp only [CollatzResearch.WordTrace]
  refine ⟨147214715195301358774245925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196286286927068478365661233 147214715195301358774245925)
  ·
    refine ⟨27602759099119004770171111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147214715195301358774245925 27602759099119004770171111)
    ·
      refine ⟨41404138648678507155256667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27602759099119004770171111 41404138648678507155256667)
      ·
        refine ⟨62106207973017760732885001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41404138648678507155256667 62106207973017760732885001)
        ·
          refine ⟨46579655979763320549663751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62106207973017760732885001 46579655979763320549663751)
          ·
            refine ⟨69869483969644980824495627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46579655979763320549663751 69869483969644980824495627)
            ·
              refine ⟨104804225954467471236743441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69869483969644980824495627 104804225954467471236743441)
              ·
                refine ⟨78603169465850603427557581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104804225954467471236743441 78603169465850603427557581)
                ·
                  refine ⟨29476188549693976285334093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78603169465850603427557581 29476188549693976285334093)
                  ·
                    refine ⟨11053570706135241107000285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29476188549693976285334093 11053570706135241107000285)
                    ·
                      refine ⟨4145089014800715415125107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11053570706135241107000285 4145089014800715415125107)
                      ·
                        rfl

theorem cell23_8072532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_8072532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072532 prefixEnd_8072532 := by exact prefixLift 8072532
  have htrace : WordTrace (prefixWord ++ tailWord_8072532) baseStart_8072532 baseEnd_8072532 := by
    simpa [prefixWord, tailWord_8072532, baseEnd_8072532] using wordTrace_append hprefix tailTrace_8072532
  have hstable : (prefixWord ++ tailWord_8072532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072532).length < 2 ^ (prefixWord ++ tailWord_8072532).sum := by decide
  have hdescent : baseEnd_8072532 < baseStart_8072532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072533 : List Nat := [1, 3, 2, 2, 3, 2, 1, 4, 1, 2, 2]
def baseStart_8072533 : Nat := 118140960795 + 8072533 * 2 ^ 59
def prefixEnd_8072533 : Nat := 4983230072969 + 3 ^ 40 * 8072533 * 2
def baseEnd_8072533 : Nat := 4145089528281369911212603

theorem tailTrace_8072533 : CollatzResearch.WordTrace tailWord_8072533 prefixEnd_8072533 4145089528281369911212603 := by
  unfold tailWord_8072533
  simp only [CollatzResearch.WordTrace]
  refine ⟨294429466863599094719278253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196286311242399396479518835 294429466863599094719278253)
  ·
    refine ⟨110411050073849660519729345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294429466863599094719278253 110411050073849660519729345)
    ·
      refine ⟨82808287555387245389797009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110411050073849660519729345 82808287555387245389797009)
      ·
        refine ⟨62106215666540434042347757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82808287555387245389797009 62106215666540434042347757)
        ·
          refine ⟨23289830874952662765880409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62106215666540434042347757 23289830874952662765880409)
          ·
            refine ⟨17467373156214497074410307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23289830874952662765880409 17467373156214497074410307)
            ·
              refine ⟨26201059734321745611615461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17467373156214497074410307 26201059734321745611615461)
              ·
                refine ⟨4912698700185327302177899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26201059734321745611615461 4912698700185327302177899)
                ·
                  refine ⟨7369048050277990953266849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4912698700185327302177899 7369048050277990953266849)
                  ·
                    refine ⟨5526786037708493214950137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369048050277990953266849 5526786037708493214950137)
                    ·
                      refine ⟨4145089528281369911212603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526786037708493214950137 4145089528281369911212603)
                      ·
                        rfl

theorem cell23_8072533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 4, 1, 2, 2].length) (baseStart_8072533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072533 prefixEnd_8072533 := by exact prefixLift 8072533
  have htrace : WordTrace (prefixWord ++ tailWord_8072533) baseStart_8072533 baseEnd_8072533 := by
    simpa [prefixWord, tailWord_8072533, baseEnd_8072533] using wordTrace_append hprefix tailTrace_8072533
  have hstable : (prefixWord ++ tailWord_8072533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072533).length < 2 ^ (prefixWord ++ tailWord_8072533).sum := by decide
  have hdescent : baseEnd_8072533 < baseStart_8072533 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072535 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 2, 7]
def baseStart_8072535 : Nat := 118140960795 + 8072535 * 2 ^ 59
def prefixEnd_8072535 : Nat := 4983230072969 + 3 ^ 40 * 8072535 * 2
def baseEnd_8072535 : Nat := 1381696851747559634462531

theorem tailTrace_8072535 : CollatzResearch.WordTrace tailWord_8072535 prefixEnd_8072535 1381696851747559634462531 := by
  unfold tailWord_8072535
  simp only [CollatzResearch.WordTrace]
  refine ⟨294429539809591849060851059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196286359873061232707234039 294429539809591849060851059)
  ·
    refine ⟨441644309714387773591276589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294429539809591849060851059 441644309714387773591276589)
    ·
      refine ⟨165616616142895415096728721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441644309714387773591276589 165616616142895415096728721)
      ·
        refine ⟨124212462107171561322546541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165616616142895415096728721 124212462107171561322546541)
        ·
          refine ⟨46579673290189335495954953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124212462107171561322546541 46579673290189335495954953)
          ·
            refine ⟨34934754967642001621966215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46579673290189335495954953 34934754967642001621966215)
            ·
              refine ⟨52402132451463002432949323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34934754967642001621966215 52402132451463002432949323)
              ·
                refine ⟨78603198677194503649423985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52402132451463002432949323 78603198677194503649423985)
                ·
                  refine ⟨58952399007895877737067989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78603198677194503649423985 58952399007895877737067989)
                  ·
                    refine ⟨1381696851747559634462531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58952399007895877737067989 1381696851747559634462531)
                    ·
                      rfl

theorem cell23_8072535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 2, 7].length) (baseStart_8072535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072535 prefixEnd_8072535 := by exact prefixLift 8072535
  have htrace : WordTrace (prefixWord ++ tailWord_8072535) baseStart_8072535 baseEnd_8072535 := by
    simpa [prefixWord, tailWord_8072535, baseEnd_8072535] using wordTrace_append hprefix tailTrace_8072535
  have hstable : (prefixWord ++ tailWord_8072535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072535).length < 2 ^ (prefixWord ++ tailWord_8072535).sum := by decide
  have hdescent : baseEnd_8072535 < baseStart_8072535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072549 : List Nat := [1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 3]
def baseStart_8072549 : Nat := 118140960795 + 8072549 * 2 ^ 59
def prefixEnd_8072549 : Nat := 4983230072969 + 3 ^ 40 * 8072549 * 2
def baseEnd_8072549 : Nat := 4145097743971841848612529

theorem tailTrace_8072549 : CollatzResearch.WordTrace tailWord_8072549 prefixEnd_8072549 4145097743971841848612529 := by
  unfold tailWord_8072549
  simp only [CollatzResearch.WordTrace]
  refine ⟨294430050431541129451860701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196286700287694086301240467 294430050431541129451860701)
  ·
    refine ⟨110411268911827923544447763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294430050431541129451860701 110411268911827923544447763)
    ·
      refine ⟨165616903367741885316671645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110411268911827923544447763 165616903367741885316671645)
      ·
        refine ⟨62106338762903206993751867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165616903367741885316671645 62106338762903206993751867)
        ·
          refine ⟨93159508144354810490627801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62106338762903206993751867 93159508144354810490627801)
          ·
            refine ⟨69869631108266107867970851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93159508144354810490627801 69869631108266107867970851)
            ·
              refine ⟨104804446662399161801956277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69869631108266107867970851 104804446662399161801956277)
              ·
                refine ⟨9825416874599921418933401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104804446662399161801956277 9825416874599921418933401)
                ·
                  refine ⟨7369062655949941064200051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9825416874599921418933401 7369062655949941064200051)
                  ·
                    refine ⟨11053593983924911596300077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7369062655949941064200051 11053593983924911596300077)
                    ·
                      refine ⟨4145097743971841848612529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11053593983924911596300077 4145097743971841848612529)
                      ·
                        rfl

theorem cell23_8072549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_8072549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072549 prefixEnd_8072549 := by exact prefixLift 8072549
  have htrace : WordTrace (prefixWord ++ tailWord_8072549) baseStart_8072549 baseEnd_8072549 := by
    simpa [prefixWord, tailWord_8072549, baseEnd_8072549] using wordTrace_append hprefix tailTrace_8072549
  have hstable : (prefixWord ++ tailWord_8072549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072549).length < 2 ^ (prefixWord ++ tailWord_8072549).sum := by decide
  have hdescent : baseEnd_8072549 < baseStart_8072549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072559 : List Nat := [1, 1, 2, 1, 3, 1, 4, 4, 1, 3, 2]
def baseStart_8072559 : Nat := 118140960795 + 8072559 * 2 ^ 59
def prefixEnd_8072559 : Nat := 4983230072969 + 3 ^ 40 * 8072559 * 2
def baseEnd_8072559 : Nat := 4145102878778386809487483

theorem tailTrace_8072559 : CollatzResearch.WordTrace tailWord_8072559 prefixEnd_8072559 4145102878778386809487483 := by
  unfold tailWord_8072559
  simp only [CollatzResearch.WordTrace]
  refine ⟨294430415161504901159724731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196286943441003267439816487 294430415161504901159724731)
  ·
    refine ⟨441645622742257351739587097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294430415161504901159724731 441645622742257351739587097)
    ·
      refine ⟨331234217056693013804690323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441645622742257351739587097 331234217056693013804690323)
      ·
        refine ⟨496851325585039520707035485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331234217056693013804690323 496851325585039520707035485)
        ·
          refine ⟨186319247094389820265138307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496851325585039520707035485 186319247094389820265138307)
          ·
            refine ⟨279478870641584730397707461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186319247094389820265138307 279478870641584730397707461)
            ·
              refine ⟨52402288245297136949570149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279478870641584730397707461 52402288245297136949570149)
              ·
                refine ⟨9825429045993213178044403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52402288245297136949570149 9825429045993213178044403)
                ·
                  refine ⟨14738143568989819767066605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9825429045993213178044403 14738143568989819767066605)
                  ·
                    refine ⟨5526803838371182412649977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14738143568989819767066605 5526803838371182412649977)
                    ·
                      refine ⟨4145102878778386809487483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5526803838371182412649977 4145102878778386809487483)
                      ·
                        rfl

theorem cell23_8072559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 4, 1, 3, 2].length) (baseStart_8072559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072559 prefixEnd_8072559 := by exact prefixLift 8072559
  have htrace : WordTrace (prefixWord ++ tailWord_8072559) baseStart_8072559 baseEnd_8072559 := by
    simpa [prefixWord, tailWord_8072559, baseEnd_8072559] using wordTrace_append hprefix tailTrace_8072559
  have hstable : (prefixWord ++ tailWord_8072559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072559).length < 2 ^ (prefixWord ++ tailWord_8072559).sum := by decide
  have hdescent : baseEnd_8072559 < baseStart_8072559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072602 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_8072602 : Nat := 118140960795 + 8072602 * 2 ^ 59
def prefixEnd_8072602 : Nat := 4983230072969 + 3 ^ 40 * 8072602 * 2
def baseEnd_8072602 : Nat := 4145124958446530141249785

theorem tailTrace_8072602 : CollatzResearch.WordTrace tailWord_8072602 prefixEnd_8072602 4145124958446530141249785 := by
  unfold tailWord_8072602
  simp only [CollatzResearch.WordTrace]
  refine ⟨73607995875087279875885015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196287989000232746335693373 73607995875087279875885015)
  ·
    refine ⟨110411993812630919813827523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73607995875087279875885015 110411993812630919813827523)
    ·
      refine ⟨165617990718946379720741285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110411993812630919813827523 165617990718946379720741285)
      ·
        refine ⟨31053373259802446197638991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165617990718946379720741285 31053373259802446197638991)
        ·
          refine ⟨46580059889703669296458487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31053373259802446197638991 46580059889703669296458487)
          ·
            refine ⟨69870089834555503944687731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46580059889703669296458487 69870089834555503944687731)
            ·
              refine ⟨104805134751833255917031597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69870089834555503944687731 104805134751833255917031597)
              ·
                refine ⟨39301925531937470968886849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104805134751833255917031597 39301925531937470968886849)
                ·
                  refine ⟨29476444148953103226665137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39301925531937470968886849 29476444148953103226665137)
                  ·
                    refine ⟨22107333111714827419998853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29476444148953103226665137 22107333111714827419998853)
                    ·
                      refine ⟨4145124958446530141249785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22107333111714827419998853 4145124958446530141249785)
                      ·
                        rfl

theorem cell23_8072602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_8072602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072602 prefixEnd_8072602 := by exact prefixLift 8072602
  have htrace : WordTrace (prefixWord ++ tailWord_8072602) baseStart_8072602 baseEnd_8072602 := by
    simpa [prefixWord, tailWord_8072602, baseEnd_8072602] using wordTrace_append hprefix tailTrace_8072602
  have hstable : (prefixWord ++ tailWord_8072602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072602).length < 2 ^ (prefixWord ++ tailWord_8072602).sum := by decide
  have hdescent : baseEnd_8072602 < baseStart_8072602 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072645 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 8]
def baseStart_8072645 : Nat := 118140960795 + 8072645 * 2 ^ 59
def prefixEnd_8072645 : Nat := 4983230072969 + 3 ^ 40 * 8072645 * 2
def baseEnd_8072645 : Nat := 4145147038114673473012087

theorem tailTrace_8072645 : CollatzResearch.WordTrace tailWord_8072645 prefixEnd_8072645 4145147038114673473012087 := by
  unfold tailWord_8072645
  simp only [CollatzResearch.WordTrace]
  refine ⟨294433551839193337847355389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196289034559462225231570259 294433551839193337847355389)
  ·
    refine ⟨110412581939697501692758271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294433551839193337847355389 110412581939697501692758271)
    ·
      refine ⟨165618872909546252539137407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110412581939697501692758271 165618872909546252539137407)
      ·
        refine ⟨248428309364319378808706111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165618872909546252539137407 248428309364319378808706111)
        ·
          refine ⟨372642464046479068213059167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248428309364319378808706111 372642464046479068213059167)
          ·
            refine ⟨558963696069718602319588751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372642464046479068213059167 558963696069718602319588751)
            ·
              refine ⟨838445544104577903479383127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558963696069718602319588751 838445544104577903479383127)
              ·
                refine ⟨1257668316156866855219074691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 838445544104577903479383127 1257668316156866855219074691)
                ·
                  refine ⟨1886502474235300282828612037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257668316156866855219074691 1886502474235300282828612037)
                  ·
                    refine ⟨353719213919118803030364757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1886502474235300282828612037 353719213919118803030364757)
                    ·
                      refine ⟨4145147038114673473012087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 353719213919118803030364757 4145147038114673473012087)
                      ·
                        rfl

theorem cell23_8072645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_8072645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072645 prefixEnd_8072645 := by exact prefixLift 8072645
  have htrace : WordTrace (prefixWord ++ tailWord_8072645) baseStart_8072645 baseEnd_8072645 := by
    simpa [prefixWord, tailWord_8072645, baseEnd_8072645] using wordTrace_append hprefix tailTrace_8072645
  have hstable : (prefixWord ++ tailWord_8072645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072645).length < 2 ^ (prefixWord ++ tailWord_8072645).sum := by decide
  have hdescent : baseEnd_8072645 < baseStart_8072645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072652 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 1, 1, 7]
def baseStart_8072652 : Nat := 118140960795 + 8072652 * 2 ^ 59
def prefixEnd_8072652 : Nat := 4983230072969 + 3 ^ 40 * 8072652 * 2
def baseEnd_8072652 : Nat := 4145150632479254945624555

theorem tailTrace_8072652 : CollatzResearch.WordTrace tailWord_8072652 prefixEnd_8072652 4145150632479254945624555 := by
  unfold tailWord_8072652
  simp only [CollatzResearch.WordTrace]
  refine ⟨147216903575083989021430105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196289204766778652028573473 147216903575083989021430105)
  ·
    refine ⟨110412677681312991766072579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147216903575083989021430105 110412677681312991766072579)
    ·
      refine ⟨165619016521969487649108869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110412677681312991766072579 165619016521969487649108869)
      ·
        refine ⟨31053565597869278934207913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165619016521969487649108869 31053565597869278934207913)
        ·
          refine ⟨23290174198401959200655935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31053565597869278934207913 23290174198401959200655935)
          ·
            refine ⟨34935261297602938800983903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23290174198401959200655935 34935261297602938800983903)
            ·
              refine ⟨52402891946404408201475855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34935261297602938800983903 52402891946404408201475855)
              ·
                refine ⟨78604337919606612302213783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52402891946404408201475855 78604337919606612302213783)
                ·
                  refine ⟨117906506879409918453320675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78604337919606612302213783 117906506879409918453320675)
                  ·
                    refine ⟨176859760319114877679981013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117906506879409918453320675 176859760319114877679981013)
                    ·
                      refine ⟨4145150632479254945624555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176859760319114877679981013 4145150632479254945624555)
                      ·
                        rfl

theorem cell23_8072652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_8072652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072652 prefixEnd_8072652 := by exact prefixLift 8072652
  have htrace : WordTrace (prefixWord ++ tailWord_8072652) baseStart_8072652 baseEnd_8072652 := by
    simpa [prefixWord, tailWord_8072652, baseEnd_8072652] using wordTrace_append hprefix tailTrace_8072652
  have hstable : (prefixWord ++ tailWord_8072652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072652).length < 2 ^ (prefixWord ++ tailWord_8072652).sum := by decide
  have hdescent : baseEnd_8072652 < baseStart_8072652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072679 : List Nat := [1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 4]
def baseStart_8072679 : Nat := 118140960795 + 8072679 * 2 ^ 59
def prefixEnd_8072679 : Nat := 4983230072969 + 3 ^ 40 * 8072679 * 2
def baseEnd_8072679 : Nat := 4145164496456926339986931

theorem tailTrace_8072679 : CollatzResearch.WordTrace tailWord_8072679 prefixEnd_8072679 4145164496456926339986931 := by
  unfold tailWord_8072679
  simp only [CollatzResearch.WordTrace]
  refine ⟨294434791921070161654093091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196289861280713441102728727 294434791921070161654093091)
  ·
    refine ⟨441652187881605242481139637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294434791921070161654093091 441652187881605242481139637)
    ·
      refine ⟨41404892613900491482606841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441652187881605242481139637 41404892613900491482606841)
      ·
        refine ⟨31053669460425368611955131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41404892613900491482606841 31053669460425368611955131)
        ·
          refine ⟨46580504190638052917932697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31053669460425368611955131 46580504190638052917932697)
          ·
            refine ⟨34935378142978539688449523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46580504190638052917932697 34935378142978539688449523)
            ·
              refine ⟨52403067214467809532674285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34935378142978539688449523 52403067214467809532674285)
              ·
                refine ⟨19651150205425428574752857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52403067214467809532674285 19651150205425428574752857)
                ·
                  refine ⟨14738362654069071431064643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19651150205425428574752857 14738362654069071431064643)
                  ·
                    refine ⟨22107543981103607146596965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14738362654069071431064643 22107543981103607146596965)
                    ·
                      refine ⟨4145164496456926339986931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22107543981103607146596965 4145164496456926339986931)
                      ·
                        rfl

theorem cell23_8072679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_8072679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072679 prefixEnd_8072679 := by exact prefixLift 8072679
  have htrace : WordTrace (prefixWord ++ tailWord_8072679) baseStart_8072679 baseEnd_8072679 := by
    simpa [prefixWord, tailWord_8072679, baseEnd_8072679] using wordTrace_append hprefix tailTrace_8072679
  have hstable : (prefixWord ++ tailWord_8072679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072679).length < 2 ^ (prefixWord ++ tailWord_8072679).sum := by decide
  have hdescent : baseEnd_8072679 < baseStart_8072679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072746 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3]
def baseStart_8072746 : Nat := 118140960795 + 8072746 * 2 ^ 59
def prefixEnd_8072746 : Nat := 4983230072969 + 3 ^ 40 * 8072746 * 2
def baseEnd_8072746 : Nat := 4145198899660777577849123

theorem tailTrace_8072746 : CollatzResearch.WordTrace tailWord_8072746 prefixEnd_8072746 4145198899660777577849123 := by
  unfold tailWord_8072746
  simp only [CollatzResearch.WordTrace]
  refine ⟨73609308902956858024195523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196291490407884954731188061 73609308902956858024195523)
  ·
    refine ⟨110413963354435287036293285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73609308902956858024195523 110413963354435287036293285)
    ·
      refine ⟨20702618128956616319304991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110413963354435287036293285 20702618128956616319304991)
      ·
        refine ⟨31053927193434924478957487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20702618128956616319304991 31053927193434924478957487)
        ·
          refine ⟨46580890790152386718436231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31053927193434924478957487 46580890790152386718436231)
          ·
            refine ⟨69871336185228580077654347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46580890790152386718436231 69871336185228580077654347)
            ·
              refine ⟨104807004277842870116481521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69871336185228580077654347 104807004277842870116481521)
              ·
                refine ⟨78605253208382152587361141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104807004277842870116481521 78605253208382152587361141)
                ·
                  refine ⟨7369242488285826805065107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78605253208382152587361141 7369242488285826805065107)
                  ·
                    refine ⟨11053863732428740207597661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7369242488285826805065107 11053863732428740207597661)
                    ·
                      refine ⟨4145198899660777577849123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11053863732428740207597661 4145198899660777577849123)
                      ·
                        rfl

theorem cell23_8072746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 5, 1, 3].length) (baseStart_8072746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072746 prefixEnd_8072746 := by exact prefixLift 8072746
  have htrace : WordTrace (prefixWord ++ tailWord_8072746) baseStart_8072746 baseEnd_8072746 := by
    simpa [prefixWord, tailWord_8072746, baseEnd_8072746] using wordTrace_append hprefix tailTrace_8072746
  have hstable : (prefixWord ++ tailWord_8072746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072746).length < 2 ^ (prefixWord ++ tailWord_8072746).sum := by decide
  have hdescent : baseEnd_8072746 < baseStart_8072746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072786 : List Nat := [3, 2, 2, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_8072786 : Nat := 118140960795 + 8072786 * 2 ^ 59
def prefixEnd_8072786 : Nat := 4983230072969 + 3 ^ 40 * 8072786 * 2
def baseEnd_8072786 : Nat := 4145219438886957421348939

theorem tailTrace_8072786 : CollatzResearch.WordTrace tailWord_8072786 prefixEnd_8072786 4145219438886957421348939 := by
  unfold tailWord_8072786
  simp only [CollatzResearch.WordTrace]
  refine ⟨73609673632920629732059553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196292463021121679285492141 73609673632920629732059553)
  ·
    refine ⟨55207255224690472299044665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73609673632920629732059553 55207255224690472299044665)
    ·
      refine ⟨41405441418517854224283499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55207255224690472299044665 41405441418517854224283499)
      ·
        refine ⟨62108162127776781336425249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41405441418517854224283499 62108162127776781336425249)
        ·
          refine ⟨46581121595832586002318937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62108162127776781336425249 46581121595832586002318937)
          ·
            refine ⟨34935841196874439501739203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46581121595832586002318937 34935841196874439501739203)
            ·
              refine ⟨52403761795311659252608805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34935841196874439501739203 52403761795311659252608805)
              ·
                refine ⟨9825705336620936109864151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52403761795311659252608805 9825705336620936109864151)
                ·
                  refine ⟨14738558004931404164796227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9825705336620936109864151 14738558004931404164796227)
                  ·
                    refine ⟨22107837007397106247194341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14738558004931404164796227 22107837007397106247194341)
                    ·
                      refine ⟨4145219438886957421348939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22107837007397106247194341 4145219438886957421348939)
                      ·
                        rfl

theorem cell23_8072786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_8072786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072786 prefixEnd_8072786 := by exact prefixLift 8072786
  have htrace : WordTrace (prefixWord ++ tailWord_8072786) baseStart_8072786 baseEnd_8072786 := by
    simpa [prefixWord, tailWord_8072786, baseEnd_8072786] using wordTrace_append hprefix tailTrace_8072786
  have hstable : (prefixWord ++ tailWord_8072786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072786).length < 2 ^ (prefixWord ++ tailWord_8072786).sum := by decide
  have hdescent : baseEnd_8072786 < baseStart_8072786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072796 : List Nat := [2, 2, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_8072796 : Nat := 118140960795 + 8072796 * 2 ^ 59
def prefixEnd_8072796 : Nat := 4983230072969 + 3 ^ 40 * 8072796 * 2
def baseEnd_8072796 : Nat := 1381741524564500794074631

theorem tailTrace_8072796 : CollatzResearch.WordTrace tailWord_8072796 prefixEnd_8072796 1381741524564500794074631 := by
  unfold tailWord_8072796
  simp only [CollatzResearch.WordTrace]
  refine ⟨147219529630823145318051121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196292706174430860424068161 147219529630823145318051121)
  ·
    refine ⟨110414647223117358988538341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147219529630823145318051121 110414647223117358988538341)
    ·
      refine ⟨20702746354334504810350939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110414647223117358988538341 20702746354334504810350939)
      ·
        refine ⟨31054119531501757215526409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20702746354334504810350939 31054119531501757215526409)
        ·
          refine ⟨23290589648626317911644807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31054119531501757215526409 23290589648626317911644807)
          ·
            refine ⟨34935884472939476867467211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23290589648626317911644807 34935884472939476867467211)
            ·
              refine ⟨52403826709409215301200817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34935884472939476867467211 52403826709409215301200817)
              ·
                refine ⟨39302870032056911475900613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52403826709409215301200817 39302870032056911475900613)
                ·
                  refine ⟨7369288131010670901731365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39302870032056911475900613 7369288131010670901731365)
                  ·
                    refine ⟨1381741524564500794074631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369288131010670901731365 1381741524564500794074631)
                    ·
                      rfl

theorem cell23_8072796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_8072796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072796 prefixEnd_8072796 := by exact prefixLift 8072796
  have htrace : WordTrace (prefixWord ++ tailWord_8072796) baseStart_8072796 baseEnd_8072796 := by
    simpa [prefixWord, tailWord_8072796, baseEnd_8072796] using wordTrace_append hprefix tailTrace_8072796
  have hstable : (prefixWord ++ tailWord_8072796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072796).length < 2 ^ (prefixWord ++ tailWord_8072796).sum := by decide
  have hdescent : baseEnd_8072796 < baseStart_8072796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072879 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 3]
def baseStart_8072879 : Nat := 118140960795 + 8072879 * 2 ^ 59
def prefixEnd_8072879 : Nat := 4983230072969 + 3 ^ 40 * 8072879 * 2
def baseEnd_8072879 : Nat := 4145267192587825557486011

theorem tailTrace_8072879 : CollatzResearch.WordTrace tailWord_8072879 prefixEnd_8072879 4145267192587825557486011 := by
  unfold tailWord_8072879
  simp only [CollatzResearch.WordTrace]
  refine ⟨294442086520345595811373691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196294724346897063874249127 294442086520345595811373691)
  ·
    refine ⟨441663129780518393717060537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294442086520345595811373691 441663129780518393717060537)
    ·
      refine ⟨331247347335388795287795403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441663129780518393717060537 331247347335388795287795403)
      ·
        refine ⟨496871021003083192931693105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331247347335388795287795403 496871021003083192931693105)
        ·
          refine ⟨372653265752312394698769829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496871021003083192931693105 372653265752312394698769829)
          ·
            refine ⟨69872487328558574006019343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372653265752312394698769829 69872487328558574006019343)
            ·
              refine ⟨104808730992837861009029015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69872487328558574006019343 104808730992837861009029015)
              ·
                refine ⟨157213096489256791513543523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104808730992837861009029015 157213096489256791513543523)
                ·
                  refine ⟨235819644733885187270315285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157213096489256791513543523 235819644733885187270315285)
                  ·
                    refine ⟨11054045846900868153296029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 235819644733885187270315285 11054045846900868153296029)
                    ·
                      refine ⟨4145267192587825557486011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11054045846900868153296029 4145267192587825557486011)
                      ·
                        rfl

theorem cell23_8072879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 6, 3].length) (baseStart_8072879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072879 prefixEnd_8072879 := by exact prefixLift 8072879
  have htrace : WordTrace (prefixWord ++ tailWord_8072879) baseStart_8072879 baseEnd_8072879 := by
    simpa [prefixWord, tailWord_8072879, baseEnd_8072879] using wordTrace_append hprefix tailTrace_8072879
  have hstable : (prefixWord ++ tailWord_8072879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072879).length < 2 ^ (prefixWord ++ tailWord_8072879).sum := by decide
  have hdescent : baseEnd_8072879 < baseStart_8072879 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072889 : List Nat := [1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_8072889 : Nat := 118140960795 + 8072889 * 2 ^ 59
def prefixEnd_8072889 : Nat := 4983230072969 + 3 ^ 40 * 8072889 * 2
def baseEnd_8072889 : Nat := 4145272327394370518360965

theorem tailTrace_8072889 : CollatzResearch.WordTrace tailWord_8072889 prefixEnd_8072889 4145272327394370518360965 := by
  unfold tailWord_8072889
  simp only [CollatzResearch.WordTrace]
  refine ⟨294442451250309367519237721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196294967500206245012825147 294442451250309367519237721)
  ·
    refine ⟨220831838437732025639428291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294442451250309367519237721 220831838437732025639428291)
    ·
      refine ⟨331247757656598038459142437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220831838437732025639428291 331247757656598038459142437)
      ·
        refine ⟨62108954560612132211089207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331247757656598038459142437 62108954560612132211089207)
        ·
          refine ⟨93163431840918198316633811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62108954560612132211089207 93163431840918198316633811)
          ·
            refine ⟨139745147761377297474950717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93163431840918198316633811 139745147761377297474950717)
            ·
              refine ⟨52404430410516486553106519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139745147761377297474950717 52404430410516486553106519)
              ·
                refine ⟨78606645615774729829659779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52404430410516486553106519 78606645615774729829659779)
                ·
                  refine ⟨117909968423662094744489669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78606645615774729829659779 117909968423662094744489669)
                  ·
                    refine ⟨22108119079436642764591813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117909968423662094744489669 22108119079436642764591813)
                    ·
                      refine ⟨4145272327394370518360965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22108119079436642764591813 4145272327394370518360965)
                      ·
                        rfl

theorem cell23_8072889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_8072889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072889 prefixEnd_8072889 := by exact prefixLift 8072889
  have htrace : WordTrace (prefixWord ++ tailWord_8072889) baseStart_8072889 baseEnd_8072889 := by
    simpa [prefixWord, tailWord_8072889, baseEnd_8072889] using wordTrace_append hprefix tailTrace_8072889
  have hstable : (prefixWord ++ tailWord_8072889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072889).length < 2 ^ (prefixWord ++ tailWord_8072889).sum := by decide
  have hdescent : baseEnd_8072889 < baseStart_8072889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072893 : List Nat := [1, 4, 1, 2, 1, 2, 4, 1, 1, 4, 2]
def baseStart_8072893 : Nat := 118140960795 + 8072893 * 2 ^ 59
def prefixEnd_8072893 : Nat := 4983230072969 + 3 ^ 40 * 8072893 * 2
def baseEnd_8072893 : Nat := 4145274381316988502710947

theorem tailTrace_8072893 : CollatzResearch.WordTrace tailWord_8072893 prefixEnd_8072893 4145274381316988502710947 := by
  unfold tailWord_8072893
  simp only [CollatzResearch.WordTrace]
  refine ⟨294442597142294876202383333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196295064761529917468255555 294442597142294876202383333)
  ·
    refine ⟨55207986964180289287946875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294442597142294876202383333 55207986964180289287946875)
    ·
      refine ⟨82811980446270433931920313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55207986964180289287946875 82811980446270433931920313)
      ·
        refine ⟨62108985334702825448940235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82811980446270433931920313 62108985334702825448940235)
        ·
          refine ⟨93163478002054238173410353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62108985334702825448940235 93163478002054238173410353)
          ·
            refine ⟨69872608501540678630057765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93163478002054238173410353 69872608501540678630057765)
            ·
              refine ⟨13101114094038877243135831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69872608501540678630057765 13101114094038877243135831)
              ·
                refine ⟨19651671141058315864703747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13101114094038877243135831 19651671141058315864703747)
                ·
                  refine ⟨29477506711587473797055621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19651671141058315864703747 29477506711587473797055621)
                  ·
                    refine ⟨5527032508422651336947929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29477506711587473797055621 5527032508422651336947929)
                    ·
                      refine ⟨4145274381316988502710947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527032508422651336947929 4145274381316988502710947)
                      ·
                        rfl

theorem cell23_8072893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 4, 1, 1, 4, 2].length) (baseStart_8072893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072893 prefixEnd_8072893 := by exact prefixLift 8072893
  have htrace : WordTrace (prefixWord ++ tailWord_8072893) baseStart_8072893 baseEnd_8072893 := by
    simpa [prefixWord, tailWord_8072893, baseEnd_8072893] using wordTrace_append hprefix tailTrace_8072893
  have hstable : (prefixWord ++ tailWord_8072893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072893).length < 2 ^ (prefixWord ++ tailWord_8072893).sum := by decide
  have hdescent : baseEnd_8072893 < baseStart_8072893 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072939 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5]
def baseStart_8072939 : Nat := 118140960795 + 8072939 * 2 ^ 59
def prefixEnd_8072939 : Nat := 4983230072969 + 3 ^ 40 * 8072939 * 2
def baseEnd_8072939 : Nat := 4145298001427095322735735

theorem tailTrace_8072939 : CollatzResearch.WordTrace tailWord_8072939 prefixEnd_8072939 4145298001427095322735735 := by
  unfold tailWord_8072939
  simp only [CollatzResearch.WordTrace]
  refine ⟨294444274900128226058557871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196296183266752150705705247 294444274900128226058557871)
  ·
    refine ⟨441666412350192339087836807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294444274900128226058557871 441666412350192339087836807)
    ·
      refine ⟨662499618525288508631755211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441666412350192339087836807 662499618525288508631755211)
      ·
        refine ⟨993749427787932762947632817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662499618525288508631755211 993749427787932762947632817)
        ·
          refine ⟨745312070840949572210724613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993749427787932762947632817 745312070840949572210724613)
          ·
            refine ⟨139746013282678044789510865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 745312070840949572210724613 139746013282678044789510865)
            ·
              refine ⟨104809509962008533592133149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139746013282678044789510865 104809509962008533592133149)
              ·
                refine ⟨39303566235753200097049931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104809509962008533592133149 39303566235753200097049931)
                ·
                  refine ⟨58955349353629800145574897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39303566235753200097049931 58955349353629800145574897)
                  ·
                    refine ⟨44216512015222350109181173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58955349353629800145574897 44216512015222350109181173)
                    ·
                      refine ⟨4145298001427095322735735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44216512015222350109181173 4145298001427095322735735)
                      ·
                        rfl

theorem cell23_8072939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 5].length) (baseStart_8072939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072939 prefixEnd_8072939 := by exact prefixLift 8072939
  have htrace : WordTrace (prefixWord ++ tailWord_8072939) baseStart_8072939 baseEnd_8072939 := by
    simpa [prefixWord, tailWord_8072939, baseEnd_8072939] using wordTrace_append hprefix tailTrace_8072939
  have hstable : (prefixWord ++ tailWord_8072939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072939).length < 2 ^ (prefixWord ++ tailWord_8072939).sum := by decide
  have hdescent : baseEnd_8072939 < baseStart_8072939 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072967 : List Nat := [1, 1, 4, 4, 3, 1, 1, 3, 5]
def baseStart_8072967 : Nat := 118140960795 + 8072967 * 2 ^ 59
def prefixEnd_8072967 : Nat := 4983230072969 + 3 ^ 40 * 8072967 * 2
def baseEnd_8072967 : Nat := 460590264320602357020623

theorem tailTrace_8072967 : CollatzResearch.WordTrace tailWord_8072967 prefixEnd_8072967 460590264320602357020623 := by
  unfold tailWord_8072967
  simp only [CollatzResearch.WordTrace]
  refine ⟨294445296144026786840577155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196296864096017857893718103 294445296144026786840577155)
  ·
    refine ⟨441667944216040180260865733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294445296144026786840577155 441667944216040180260865733)
    ·
      refine ⟨82812739540507533798912325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441667944216040180260865733 82812739540507533798912325)
      ·
        refine ⟨15527388663845162587296061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82812739540507533798912325 15527388663845162587296061)
        ·
          refine ⟨5822770748941935970236023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15527388663845162587296061 5822770748941935970236023)
          ·
            refine ⟨8734156123412903955354035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822770748941935970236023 8734156123412903955354035)
            ·
              refine ⟨13101234185119355933031053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734156123412903955354035 13101234185119355933031053)
              ·
                refine ⟨4912962819419758474886645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13101234185119355933031053 4912962819419758474886645)
                ·
                  refine ⟨460590264320602357020623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4912962819419758474886645 460590264320602357020623)
                  ·
                    rfl

theorem cell23_8072967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 3, 5].length) (baseStart_8072967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072967 prefixEnd_8072967 := by exact prefixLift 8072967
  have htrace : WordTrace (prefixWord ++ tailWord_8072967) baseStart_8072967 baseEnd_8072967 := by
    simpa [prefixWord, tailWord_8072967, baseEnd_8072967] using wordTrace_append hprefix tailTrace_8072967
  have hstable : (prefixWord ++ tailWord_8072967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072967).length < 2 ^ (prefixWord ++ tailWord_8072967).sum := by decide
  have hdescent : baseEnd_8072967 < baseStart_8072967 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072969 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_8072969 : Nat := 118140960795 + 8072969 * 2 ^ 59
def prefixEnd_8072969 : Nat := 4983230072969 + 3 ^ 40 * 8072969 * 2
def baseEnd_8072969 : Nat := 4145313405846730205360597

theorem tailTrace_8072969 : CollatzResearch.WordTrace tailWord_8072969 prefixEnd_8072969 4145313405846730205360597 := by
  unfold tailWord_8072969
  simp only [CollatzResearch.WordTrace]
  refine ⟨294445369090019541182149961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196296912726679694121433307 294445369090019541182149961)
  ·
    refine ⟨220834026817514655886612471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294445369090019541182149961 220834026817514655886612471)
    ·
      refine ⟨331251040226271983829918707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220834026817514655886612471 331251040226271983829918707)
      ·
        refine ⟨496876560339407975744878061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331251040226271983829918707 496876560339407975744878061)
        ·
          refine ⟨186328710127277990904329273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496876560339407975744878061 186328710127277990904329273)
          ·
            refine ⟨139746532595458493178246955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186328710127277990904329273 139746532595458493178246955)
            ·
              refine ⟨209619798893187739767370433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139746532595458493178246955 209619798893187739767370433)
              ·
                refine ⟨157214849169890804825527825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209619798893187739767370433 157214849169890804825527825)
                ·
                  refine ⟨117911136877418103619145869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157214849169890804825527825 117911136877418103619145869)
                  ·
                    refine ⟨44216676329031788857179701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117911136877418103619145869 44216676329031788857179701)
                    ·
                      refine ⟨4145313405846730205360597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44216676329031788857179701 4145313405846730205360597)
                      ·
                        rfl

theorem cell23_8072969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_8072969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072969 prefixEnd_8072969 := by exact prefixLift 8072969
  have htrace : WordTrace (prefixWord ++ tailWord_8072969) baseStart_8072969 baseEnd_8072969 := by
    simpa [prefixWord, tailWord_8072969, baseEnd_8072969] using wordTrace_append hprefix tailTrace_8072969
  have hstable : (prefixWord ++ tailWord_8072969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072969).length < 2 ^ (prefixWord ++ tailWord_8072969).sum := by decide
  have hdescent : baseEnd_8072969 < baseStart_8072969 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072979 : List Nat := [1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6]
def baseStart_8072979 : Nat := 118140960795 + 8072979 * 2 ^ 59
def prefixEnd_8072979 : Nat := 4983230072969 + 3 ^ 40 * 8072979 * 2
def baseEnd_8072979 : Nat := 4145318540653275166235551

theorem tailTrace_8072979 : CollatzResearch.WordTrace tailWord_8072979 prefixEnd_8072979 4145318540653275166235551 := by
  unfold tailWord_8072979
  simp only [CollatzResearch.WordTrace]
  refine ⟨294445733819983312890013991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196297155879988875260009327 294445733819983312890013991)
  ·
    refine ⟨441668600729974969335020987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294445733819983312890013991 441668600729974969335020987)
    ·
      refine ⟨662502901094962454002531481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441668600729974969335020987 662502901094962454002531481)
      ·
        refine ⟨496877175821221840501898611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662502901094962454002531481 496877175821221840501898611)
        ·
          refine ⟨745315763731832760752847917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496877175821221840501898611 745315763731832760752847917)
          ·
            refine ⟨279493411399437285282317969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745315763731832760752847917 279493411399437285282317969)
            ·
              refine ⟨209620058549577963961738477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279493411399437285282317969 209620058549577963961738477)
              ·
                refine ⟨78607521956091736485651929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209620058549577963961738477 78607521956091736485651929)
                ·
                  refine ⟨58955641467068802364238947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78607521956091736485651929 58955641467068802364238947)
                  ·
                    refine ⟨88433462200603203546358421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58955641467068802364238947 88433462200603203546358421)
                    ·
                      refine ⟨4145318540653275166235551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88433462200603203546358421 4145318540653275166235551)
                      ·
                        rfl

theorem cell23_8072979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 6].length) (baseStart_8072979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072979 prefixEnd_8072979 := by exact prefixLift 8072979
  have htrace : WordTrace (prefixWord ++ tailWord_8072979) baseStart_8072979 baseEnd_8072979 := by
    simpa [prefixWord, tailWord_8072979, baseEnd_8072979] using wordTrace_append hprefix tailTrace_8072979
  have hstable : (prefixWord ++ tailWord_8072979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072979).length < 2 ^ (prefixWord ++ tailWord_8072979).sum := by decide
  have hdescent : baseEnd_8072979 < baseStart_8072979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072983 : List Nat := [1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 4]
def baseStart_8072983 : Nat := 118140960795 + 8072983 * 2 ^ 59
def prefixEnd_8072983 : Nat := 4983230072969 + 3 ^ 40 * 8072983 * 2
def baseEnd_8072983 : Nat := 4145320594575893150585533

theorem tailTrace_8072983 : CollatzResearch.WordTrace tailWord_8072983 prefixEnd_8072983 4145320594575893150585533 := by
  unfold tailWord_8072983
  simp only [CollatzResearch.WordTrace]
  refine ⟨294445879711968821573159603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196297253141312547715439735 294445879711968821573159603)
  ·
    refine ⟨441668819567953232359739405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294445879711968821573159603 441668819567953232359739405)
    ·
      refine ⟨165625807337982462134902277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441668819567953232359739405 165625807337982462134902277)
      ·
        refine ⟨31054838875871711650294177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165625807337982462134902277 31054838875871711650294177)
        ·
          refine ⟨23291129156903783737720633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31054838875871711650294177 23291129156903783737720633)
          ·
            refine ⟨17468346867677837803290475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23291129156903783737720633 17468346867677837803290475)
            ·
              refine ⟨26202520301516756704935713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17468346867677837803290475 26202520301516756704935713)
              ·
                refine ⟨19651890226137567528701785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26202520301516756704935713 19651890226137567528701785)
                ·
                  refine ⟨14738917669603175646526339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19651890226137567528701785 14738917669603175646526339)
                  ·
                    refine ⟨22108376504404763469789509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14738917669603175646526339 22108376504404763469789509)
                    ·
                      refine ⟨4145320594575893150585533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22108376504404763469789509 4145320594575893150585533)
                      ·
                        rfl

theorem cell23_8072983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_8072983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072983 prefixEnd_8072983 := by exact prefixLift 8072983
  have htrace : WordTrace (prefixWord ++ tailWord_8072983) baseStart_8072983 baseEnd_8072983 := by
    simpa [prefixWord, tailWord_8072983, baseEnd_8072983] using wordTrace_append hprefix tailTrace_8072983
  have hstable : (prefixWord ++ tailWord_8072983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072983).length < 2 ^ (prefixWord ++ tailWord_8072983).sum := by decide
  have hdescent : baseEnd_8072983 < baseStart_8072983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8072993 : List Nat := [1, 2, 3, 2, 1, 3, 3, 1, 3, 4]
def baseStart_8072993 : Nat := 118140960795 + 8072993 * 2 ^ 59
def prefixEnd_8072993 : Nat := 4983230072969 + 3 ^ 40 * 8072993 * 2
def baseEnd_8072993 : Nat := 1381775243127479370486829

theorem tailTrace_8072993 : CollatzResearch.WordTrace tailWord_8072993 prefixEnd_8072993 1381775243127479370486829 := by
  unfold tailWord_8072993
  simp only [CollatzResearch.WordTrace]
  refine ⟨294446244441932593281023633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196297496294621728854015755 294446244441932593281023633)
  ·
    refine ⟨220834683331449444960767725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294446244441932593281023633 220834683331449444960767725)
    ·
      refine ⟨82813006249293541860287897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220834683331449444960767725 82813006249293541860287897)
      ·
        refine ⟨62109754686970156395215923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82813006249293541860287897 62109754686970156395215923)
        ·
          refine ⟨93164632030455234592823885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62109754686970156395215923 93164632030455234592823885)
          ·
            refine ⟨34936737011420712972308957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93164632030455234592823885 34936737011420712972308957)
            ·
              refine ⟨13101276379282767364615859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34936737011420712972308957 13101276379282767364615859)
              ·
                refine ⟨19651914568924151046923789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13101276379282767364615859 19651914568924151046923789)
                ·
                  refine ⟨7369467963346556642596421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19651914568924151046923789 7369467963346556642596421)
                  ·
                    refine ⟨1381775243127479370486829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369467963346556642596421 1381775243127479370486829)
                    ·
                      rfl

theorem cell23_8072993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_8072993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8072993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8072993 prefixEnd_8072993 := by exact prefixLift 8072993
  have htrace : WordTrace (prefixWord ++ tailWord_8072993) baseStart_8072993 baseEnd_8072993 := by
    simpa [prefixWord, tailWord_8072993, baseEnd_8072993] using wordTrace_append hprefix tailTrace_8072993
  have hstable : (prefixWord ++ tailWord_8072993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8072993).length < 2 ^ (prefixWord ++ tailWord_8072993).sum := by decide
  have hdescent : baseEnd_8072993 < baseStart_8072993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8072993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073044 : List Nat := [2, 4, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_8073044 : Nat := 118140960795 + 8073044 * 2 ^ 59
def prefixEnd_8073044 : Nat := 4983230072969 + 3 ^ 40 * 8073044 * 2
def baseEnd_8073044 : Nat := 1381783972298605803974251

theorem tailTrace_8073044 : CollatzResearch.WordTrace tailWord_8073044 prefixEnd_8073044 1381783972298605803974251 := by
  unfold tailWord_8073044
  simp only [CollatzResearch.WordTrace]
  refine ⟨147224052282373914495565093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196298736376498552660753457 147224052282373914495565093)
  ·
    refine ⟨27604509802945108967918455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147224052282373914495565093 27604509802945108967918455)
    ·
      refine ⟨41406764704417663451877683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27604509802945108967918455 41406764704417663451877683)
      ·
        refine ⟨62110147056626495177816525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41406764704417663451877683 62110147056626495177816525)
        ·
          refine ⟨23291305146234935691681197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62110147056626495177816525 23291305146234935691681197)
          ·
            refine ⟨8734239429838100884380449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23291305146234935691681197 8734239429838100884380449)
            ·
              refine ⟨6550679572378575663285337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8734239429838100884380449 6550679572378575663285337)
              ·
                refine ⟨4913009679283931747464003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6550679572378575663285337 4913009679283931747464003)
                ·
                  refine ⟨7369514518925897621196005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913009679283931747464003 7369514518925897621196005)
                  ·
                    refine ⟨1381783972298605803974251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369514518925897621196005 1381783972298605803974251)
                    ·
                      rfl

theorem cell23_8073044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_8073044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073044 prefixEnd_8073044 := by exact prefixLift 8073044
  have htrace : WordTrace (prefixWord ++ tailWord_8073044) baseStart_8073044 baseEnd_8073044 := by
    simpa [prefixWord, tailWord_8073044, baseEnd_8073044] using wordTrace_append hprefix tailTrace_8073044
  have hstable : (prefixWord ++ tailWord_8073044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073044).length < 2 ^ (prefixWord ++ tailWord_8073044).sum := by decide
  have hdescent : baseEnd_8073044 < baseStart_8073044 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073073 : List Nat := [1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_8073073 : Nat := 118140960795 + 8073073 * 2 ^ 59
def prefixEnd_8073073 : Nat := 4983230072969 + 3 ^ 40 * 8073073 * 2
def baseEnd_8073073 : Nat := 4145366807834797798460119

theorem tailTrace_8073073 : CollatzResearch.WordTrace tailWord_8073073 prefixEnd_8073073 4145366807834797798460119 := by
  unfold tailWord_8073073
  simp only [CollatzResearch.WordTrace]
  refine ⟨294449162281642766943935873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196299441521095177962623915 294449162281642766943935873)
  ·
    refine ⟨220836871711232075207951905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294449162281642766943935873 220836871711232075207951905)
    ·
      refine ⟨165627653783424056405963929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220836871711232075207951905 165627653783424056405963929)
      ·
        refine ⟨124220740337568042304472947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165627653783424056405963929 124220740337568042304472947)
        ·
          refine ⟨186331110506352063456709421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124220740337568042304472947 186331110506352063456709421)
          ·
            refine ⟨69874166439882023796266033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186331110506352063456709421 69874166439882023796266033)
            ·
              refine ⟨52405624829911517847199525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69874166439882023796266033 52405624829911517847199525)
              ·
                refine ⟨9826054655608409596349911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52405624829911517847199525 9826054655608409596349911)
                ·
                  refine ⟨14739081983412614394524867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9826054655608409596349911 14739081983412614394524867)
                  ·
                    refine ⟨22108622975118921591787301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14739081983412614394524867 22108622975118921591787301)
                    ·
                      refine ⟨4145366807834797798460119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22108622975118921591787301 4145366807834797798460119)
                      ·
                        rfl

theorem cell23_8073073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_8073073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073073 prefixEnd_8073073 := by exact prefixLift 8073073
  have htrace : WordTrace (prefixWord ++ tailWord_8073073) baseStart_8073073 baseEnd_8073073 := by
    simpa [prefixWord, tailWord_8073073, baseEnd_8073073] using wordTrace_append hprefix tailTrace_8073073
  have hstable : (prefixWord ++ tailWord_8073073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073073).length < 2 ^ (prefixWord ++ tailWord_8073073).sum := by decide
  have hdescent : baseEnd_8073073 < baseStart_8073073 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073117 : List Nat := [1, 4, 2, 1, 2, 3, 3, 1, 2, 4]
def baseStart_8073117 : Nat := 118140960795 + 8073117 * 2 ^ 59
def prefixEnd_8073117 : Nat := 4983230072969 + 3 ^ 40 * 8073117 * 2
def baseEnd_8073117 : Nat := 1381796466994531875436639

theorem tailTrace_8073117 : CollatzResearch.WordTrace tailWord_8073117 prefixEnd_8073117 1381796466994531875436639 := by
  unfold tailWord_8073117
  simp only [CollatzResearch.WordTrace]
  refine ⟨294450767093483362458537605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196300511395655574972358403 294450767093483362458537605)
  ·
    refine ⟨55209518830028130460975801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294450767093483362458537605 55209518830028130460975801)
    ·
      refine ⟨41407139122521097845731851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55209518830028130460975801 41407139122521097845731851)
      ·
        refine ⟨62110708683781646768597777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41407139122521097845731851 62110708683781646768597777)
        ·
          refine ⟨46583031512836235076448333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62110708683781646768597777 46583031512836235076448333)
          ·
            refine ⟨17468636817313588153668125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46583031512836235076448333 17468636817313588153668125)
            ·
              refine ⟨6550738806492595557625547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17468636817313588153668125 6550738806492595557625547)
              ·
                refine ⟨9826108209738893336438321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6550738806492595557625547 9826108209738893336438321)
                ·
                  refine ⟨7369581157304170002328741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9826108209738893336438321 7369581157304170002328741)
                  ·
                    refine ⟨1381796466994531875436639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369581157304170002328741 1381796466994531875436639)
                    ·
                      rfl

theorem cell23_8073117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_8073117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073117 prefixEnd_8073117 := by exact prefixLift 8073117
  have htrace : WordTrace (prefixWord ++ tailWord_8073117) baseStart_8073117 baseEnd_8073117 := by
    simpa [prefixWord, tailWord_8073117, baseEnd_8073117] using wordTrace_append hprefix tailTrace_8073117
  have hstable : (prefixWord ++ tailWord_8073117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073117).length < 2 ^ (prefixWord ++ tailWord_8073117).sum := by decide
  have hdescent : baseEnd_8073117 < baseStart_8073117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073127 : List Nat := [1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 3]
def baseStart_8073127 : Nat := 118140960795 + 8073127 * 2 ^ 59
def prefixEnd_8073127 : Nat := 4983230072969 + 3 ^ 40 * 8073127 * 2
def baseEnd_8073127 : Nat := 4145394535790140587184871

theorem tailTrace_8073127 : CollatzResearch.WordTrace tailWord_8073127 prefixEnd_8073127 4145394535790140587184871 := by
  unfold tailWord_8073127
  simp only [CollatzResearch.WordTrace]
  refine ⟨294451131823447134166401635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196300754548964756110934423 294451131823447134166401635)
  ·
    refine ⟨441676697735170701249602453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294451131823447134166401635 441676697735170701249602453)
    ·
      refine ⟨20703595206336126621075115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 441676697735170701249602453 20703595206336126621075115)
      ·
        refine ⟨31055392809504189931612673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20703595206336126621075115 31055392809504189931612673)
        ·
          refine ⟨23291544607128142448709505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31055392809504189931612673 23291544607128142448709505)
          ·
            refine ⟨17468658455346106836532129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23291544607128142448709505 17468658455346106836532129)
            ·
              refine ⟨13101493841509580127399097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17468658455346106836532129 13101493841509580127399097)
              ·
                refine ⟨9826120381132185095549323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13101493841509580127399097 9826120381132185095549323)
                ·
                  refine ⟨14739180571698277643323985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9826120381132185095549323 14739180571698277643323985)
                  ·
                    refine ⟨11054385428773708232492989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14739180571698277643323985 11054385428773708232492989)
                    ·
                      refine ⟨4145394535790140587184871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11054385428773708232492989 4145394535790140587184871)
                      ·
                        rfl

theorem cell23_8073127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_8073127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073127 prefixEnd_8073127 := by exact prefixLift 8073127
  have htrace : WordTrace (prefixWord ++ tailWord_8073127) baseStart_8073127 baseEnd_8073127 := by
    simpa [prefixWord, tailWord_8073127, baseEnd_8073127] using wordTrace_append hprefix tailTrace_8073127
  have hstable : (prefixWord ++ tailWord_8073127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073127).length < 2 ^ (prefixWord ++ tailWord_8073127).sum := by decide
  have hdescent : baseEnd_8073127 < baseStart_8073127 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073141 : List Nat := [1, 3, 3, 2, 1, 4, 1, 3, 1, 2, 2]
def baseStart_8073141 : Nat := 118140960795 + 8073141 * 2 ^ 59
def prefixEnd_8073141 : Nat := 4983230072969 + 3 ^ 40 * 8073141 * 2
def baseEnd_8073141 : Nat := 4145401724519303532409807

theorem tailTrace_8073141 : CollatzResearch.WordTrace tailWord_8073141 prefixEnd_8073141 4145401724519303532409807 := by
  unfold tailWord_8073141
  simp only [CollatzResearch.WordTrace]
  refine ⟨294451642445396414557411277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196301094963597609704940851 294451642445396414557411277)
  ·
    refine ⟨110419365917023655459029229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294451642445396414557411277 110419365917023655459029229)
    ·
      refine ⟨41407262218883870797135961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110419365917023655459029229 41407262218883870797135961)
      ·
        refine ⟨31055446664162903097851971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41407262218883870797135961 31055446664162903097851971)
        ·
          refine ⟨46583169996244354646777957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31055446664162903097851971 46583169996244354646777957)
          ·
            refine ⟨8734344374295816496270867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46583169996244354646777957 8734344374295816496270867)
            ·
              refine ⟨13101516561443724744406301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8734344374295816496270867 13101516561443724744406301)
              ·
                refine ⟨4913068710541396779152363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13101516561443724744406301 4913068710541396779152363)
                ·
                  refine ⟨7369603065812095168728545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913068710541396779152363 7369603065812095168728545)
                  ·
                    refine ⟨5527202299359071376546409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369603065812095168728545 5527202299359071376546409)
                    ·
                      refine ⟨4145401724519303532409807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527202299359071376546409 4145401724519303532409807)
                      ·
                        rfl

theorem cell23_8073141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_8073141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073141 prefixEnd_8073141 := by exact prefixLift 8073141
  have htrace : WordTrace (prefixWord ++ tailWord_8073141) baseStart_8073141 baseEnd_8073141 := by
    simpa [prefixWord, tailWord_8073141, baseEnd_8073141] using wordTrace_append hprefix tailTrace_8073141
  have hstable : (prefixWord ++ tailWord_8073141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073141).length < 2 ^ (prefixWord ++ tailWord_8073141).sum := by decide
  have hdescent : baseEnd_8073141 < baseStart_8073141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073183 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 5]
def baseStart_8073183 : Nat := 118140960795 + 8073183 * 2 ^ 59
def prefixEnd_8073183 : Nat := 4983230072969 + 3 ^ 40 * 8073183 * 2
def baseEnd_8073183 : Nat := 4145423290706792368084613

theorem tailTrace_8073183 : CollatzResearch.WordTrace tailWord_8073183 prefixEnd_8073183 4145423290706792368084613 := by
  unfold tailWord_8073183
  simp only [CollatzResearch.WordTrace]
  refine ⟨294453174311244255730440203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196302116207496170486960135 294453174311244255730440203)
  ·
    refine ⟨441679761466866383595660305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294453174311244255730440203 441679761466866383595660305)
    ·
      refine ⟨331259821100149787696745229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441679761466866383595660305 331259821100149787696745229)
      ·
        refine ⟨124222432912556170386279461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331259821100149787696745229 124222432912556170386279461)
        ·
          refine ⟨23291706171104281947427399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124222432912556170386279461 23291706171104281947427399)
          ·
            refine ⟨34937559256656422921141099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23291706171104281947427399 34937559256656422921141099)
            ·
              refine ⟨52406338884984634381711649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34937559256656422921141099 52406338884984634381711649)
              ·
                refine ⟨39304754163738475786283737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52406338884984634381711649 39304754163738475786283737)
                ·
                  refine ⟨29478565622803856839712803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39304754163738475786283737 29478565622803856839712803)
                  ·
                    refine ⟨44217848434205785259569205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29478565622803856839712803 44217848434205785259569205)
                    ·
                      refine ⟨4145423290706792368084613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44217848434205785259569205 4145423290706792368084613)
                      ·
                        rfl

theorem cell23_8073183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_8073183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073183 prefixEnd_8073183 := by exact prefixLift 8073183
  have htrace : WordTrace (prefixWord ++ tailWord_8073183) baseStart_8073183 baseEnd_8073183 := by
    simpa [prefixWord, tailWord_8073183, baseEnd_8073183] using wordTrace_append hprefix tailTrace_8073183
  have hstable : (prefixWord ++ tailWord_8073183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073183).length < 2 ^ (prefixWord ++ tailWord_8073183).sum := by decide
  have hdescent : baseEnd_8073183 < baseStart_8073183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073230 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_8073230 : Nat := 118140960795 + 8073230 * 2 ^ 59
def prefixEnd_8073230 : Nat := 4983230072969 + 3 ^ 40 * 8073230 * 2
def baseEnd_8073230 : Nat := 4145447424297553684196897

theorem tailTrace_8073230 : CollatzResearch.WordTrace tailWord_8073230 prefixEnd_8073230 4145447424297553684196897 := by
  unfold tailWord_8073230
  simp only [CollatzResearch.WordTrace]
  refine ⟨36806861067759247844675143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196303259028049321838267429 36806861067759247844675143)
  ·
    refine ⟨55210291601638871767012715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36806861067759247844675143 55210291601638871767012715)
    ·
      refine ⟨82815437402458307650519073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55210291601638871767012715 82815437402458307650519073)
      ·
        refine ⟨62111578051843730737889305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82815437402458307650519073 62111578051843730737889305)
        ·
          refine ⟨46583683538882798053416979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62111578051843730737889305 46583683538882798053416979)
          ·
            refine ⟨69875525308324197080125469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46583683538882798053416979 69875525308324197080125469)
            ·
              refine ⟨26203321990621573905047051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69875525308324197080125469 26203321990621573905047051)
              ·
                refine ⟨39304982985932360857570577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26203321990621573905047051 39304982985932360857570577)
                ·
                  refine ⟨29478737239449270643177933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39304982985932360857570577 29478737239449270643177933)
                  ·
                    refine ⟨11054526464793476491191725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29478737239449270643177933 11054526464793476491191725)
                    ·
                      refine ⟨4145447424297553684196897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11054526464793476491191725 4145447424297553684196897)
                      ·
                        rfl

theorem cell23_8073230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_8073230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073230 prefixEnd_8073230 := by exact prefixLift 8073230
  have htrace : WordTrace (prefixWord ++ tailWord_8073230) baseStart_8073230 baseEnd_8073230 := by
    simpa [prefixWord, tailWord_8073230, baseEnd_8073230] using wordTrace_append hprefix tailTrace_8073230
  have hstable : (prefixWord ++ tailWord_8073230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073230).length < 2 ^ (prefixWord ++ tailWord_8073230).sum := by decide
  have hdescent : baseEnd_8073230 < baseStart_8073230 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073240 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 2, 5, 2]
def baseStart_8073240 : Nat := 118140960795 + 8073240 * 2 ^ 59
def prefixEnd_8073240 : Nat := 4983230072969 + 3 ^ 40 * 8073240 * 2
def baseEnd_8073240 : Nat := 4145452559104098645071851

theorem tailTrace_8073240 : CollatzResearch.WordTrace tailWord_8073240 prefixEnd_8073240 4145452559104098645071851 := by
  unfold tailWord_8073240
  simp only [CollatzResearch.WordTrace]
  refine ⟨147227626636018877232632587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196303502181358502976843449 147227626636018877232632587)
  ·
    refine ⟨220841439954028315848948881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147227626636018877232632587 220841439954028315848948881)
    ·
      refine ⟨165631079965521236886711661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220841439954028315848948881 165631079965521236886711661)
      ·
        refine ⟨62111654987070463832516873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165631079965521236886711661 62111654987070463832516873)
        ·
          refine ⟨46583741240302847874387655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62111654987070463832516873 46583741240302847874387655)
          ·
            refine ⟨69875611860454271811581483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46583741240302847874387655 69875611860454271811581483)
            ·
              refine ⟨104813417790681407717372225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69875611860454271811581483 104813417790681407717372225)
              ·
                refine ⟨78610063343011055788029169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104813417790681407717372225 78610063343011055788029169)
                ·
                  refine ⟨58957547507258291841021877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78610063343011055788029169 58957547507258291841021877)
                  ·
                    refine ⟨5527270078805464860095801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58957547507258291841021877 5527270078805464860095801)
                    ·
                      refine ⟨4145452559104098645071851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527270078805464860095801 4145452559104098645071851)
                      ·
                        rfl

theorem cell23_8073240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_8073240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073240 prefixEnd_8073240 := by exact prefixLift 8073240
  have htrace : WordTrace (prefixWord ++ tailWord_8073240) baseStart_8073240 baseEnd_8073240 := by
    simpa [prefixWord, tailWord_8073240, baseEnd_8073240] using wordTrace_append hprefix tailTrace_8073240
  have hstable : (prefixWord ++ tailWord_8073240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073240).length < 2 ^ (prefixWord ++ tailWord_8073240).sum := by decide
  have hdescent : baseEnd_8073240 < baseStart_8073240 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073280 : List Nat := [2, 1, 1, 2, 2, 4, 1, 3, 3, 4]
def baseStart_8073280 : Nat := 118140960795 + 8073280 * 2 ^ 59
def prefixEnd_8073280 : Nat := 4983230072969 + 3 ^ 40 * 8073280 * 2
def baseEnd_8073280 : Nat := 1381824366110092829523889

theorem tailTrace_8073280 : CollatzResearch.WordTrace tailWord_8073280 prefixEnd_8073280 1381824366110092829523889 := by
  unfold tailWord_8073280
  simp only [CollatzResearch.WordTrace]
  refine ⟨147228356095946420648360647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196304474794595227531147529 147228356095946420648360647)
  ·
    refine ⟨220842534143919630972540971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147228356095946420648360647 220842534143919630972540971)
    ·
      refine ⟨331263801215879446458811457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220842534143919630972540971 331263801215879446458811457)
      ·
        refine ⟨248447850911909584844108593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331263801215879446458811457 248447850911909584844108593)
        ·
          refine ⟨186335888183932188633081445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248447850911909584844108593 186335888183932188633081445)
          ·
            refine ⟨34937979034487285368702771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186335888183932188633081445 34937979034487285368702771)
            ·
              refine ⟨52406968551730928053054157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34937979034487285368702771 52406968551730928053054157)
              ·
                refine ⟨19652613206899098019895309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52406968551730928053054157 19652613206899098019895309)
                ·
                  refine ⟨7369729952587161757460741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19652613206899098019895309 7369729952587161757460741)
                  ·
                    refine ⟨1381824366110092829523889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7369729952587161757460741 1381824366110092829523889)
                    ·
                      rfl

theorem cell23_8073280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 3, 3, 4].length) (baseStart_8073280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073280 prefixEnd_8073280 := by exact prefixLift 8073280
  have htrace : WordTrace (prefixWord ++ tailWord_8073280) baseStart_8073280 baseEnd_8073280 := by
    simpa [prefixWord, tailWord_8073280, baseEnd_8073280] using wordTrace_append hprefix tailTrace_8073280
  have hstable : (prefixWord ++ tailWord_8073280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073280).length < 2 ^ (prefixWord ++ tailWord_8073280).sum := by decide
  have hdescent : baseEnd_8073280 < baseStart_8073280 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073360 : List Nat := [2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_8073360 : Nat := 118140960795 + 8073360 * 2 ^ 59
def prefixEnd_8073360 : Nat := 4983230072969 + 3 ^ 40 * 8073360 * 2
def baseEnd_8073360 : Nat := 4145514176782638175571299

theorem tailTrace_8073360 : CollatzResearch.WordTrace tailWord_8073360 prefixEnd_8073360 4145514176782638175571299 := by
  unfold tailWord_8073360
  simp only [CollatzResearch.WordTrace]
  refine ⟨147229815015801507479816767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196306420021068676639755689 147229815015801507479816767)
  ·
    refine ⟨220844722523702261219725151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147229815015801507479816767 220844722523702261219725151)
    ·
      refine ⟨331267083785553391829587727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220844722523702261219725151 331267083785553391829587727)
      ·
        refine ⟨496900625678330087744381591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331267083785553391829587727 496900625678330087744381591)
        ·
          refine ⟨745350938517495131616572387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496900625678330087744381591 745350938517495131616572387)
          ·
            refine ⟨1118026407776242697424858581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745350938517495131616572387 1118026407776242697424858581)
            ·
              refine ⟨26203743932255688220895123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1118026407776242697424858581 26203743932255688220895123)
              ·
                refine ⟨39305615898383532331342685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26203743932255688220895123 39305615898383532331342685)
                ·
                  refine ⟨14739605961893824624253507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39305615898383532331342685 14739605961893824624253507)
                  ·
                    refine ⟨22109408942840736936380261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14739605961893824624253507 22109408942840736936380261)
                    ·
                      refine ⟨4145514176782638175571299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22109408942840736936380261 4145514176782638175571299)
                      ·
                        rfl

theorem cell23_8073360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_8073360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073360 prefixEnd_8073360 := by exact prefixLift 8073360
  have htrace : WordTrace (prefixWord ++ tailWord_8073360) baseStart_8073360 baseEnd_8073360 := by
    simpa [prefixWord, tailWord_8073360, baseEnd_8073360] using wordTrace_append hprefix tailTrace_8073360
  have hstable : (prefixWord ++ tailWord_8073360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073360).length < 2 ^ (prefixWord ++ tailWord_8073360).sum := by decide
  have hdescent : baseEnd_8073360 < baseStart_8073360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073394 : List Nat := [3, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2]
def baseStart_8073394 : Nat := 118140960795 + 8073394 * 2 ^ 59
def prefixEnd_8073394 : Nat := 4983230072969 + 3 ^ 40 * 8073394 * 2
def baseEnd_8073394 : Nat := 4145531635124891042546143

theorem tailTrace_8073394 : CollatzResearch.WordTrace tailWord_8073394 prefixEnd_8073394 4145531635124891042546143 := by
  unfold tailWord_8073394
  simp only [CollatzResearch.WordTrace]
  refine ⟨73615217528369959691592809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196307246742319892510914157 73615217528369959691592809)
  ·
    refine ⟨55211413146277469768694607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73615217528369959691592809 55211413146277469768694607)
    ·
      refine ⟨82817119719416204653041911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55211413146277469768694607 82817119719416204653041911)
      ·
        refine ⟨124225679579124306979562867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82817119719416204653041911 124225679579124306979562867)
        ·
          refine ⟨186338519368686460469344301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124225679579124306979562867 186338519368686460469344301)
          ·
            refine ⟨69876944763257422676004113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186338519368686460469344301 69876944763257422676004113)
            ·
              refine ⟨52407708572443067007003085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69876944763257422676004113 52407708572443067007003085)
              ·
                refine ⟨19652890714666150127626157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52407708572443067007003085 19652890714666150127626157)
                ·
                  refine ⟨7369834017999806297859809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19652890714666150127626157 7369834017999806297859809)
                  ·
                    refine ⟨5527375513499854723394857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369834017999806297859809 5527375513499854723394857)
                    ·
                      refine ⟨4145531635124891042546143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527375513499854723394857 4145531635124891042546143)
                      ·
                        rfl

theorem cell23_8073394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 3, 3, 2, 2].length) (baseStart_8073394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073394 prefixEnd_8073394 := by exact prefixLift 8073394
  have htrace : WordTrace (prefixWord ++ tailWord_8073394) baseStart_8073394 baseEnd_8073394 := by
    simpa [prefixWord, tailWord_8073394, baseEnd_8073394] using wordTrace_append hprefix tailTrace_8073394
  have hstable : (prefixWord ++ tailWord_8073394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073394).length < 2 ^ (prefixWord ++ tailWord_8073394).sum := by decide
  have hdescent : baseEnd_8073394 < baseStart_8073394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073484 : List Nat := [2, 2, 1, 2, 2, 2, 1, 1, 6, 2, 2]
def baseStart_8073484 : Nat := 118140960795 + 8073484 * 2 ^ 59
def prefixEnd_8073484 : Nat := 4983230072969 + 3 ^ 40 * 8073484 * 2
def baseEnd_8073484 : Nat := 4145577848383795690420729

theorem tailTrace_8073484 : CollatzResearch.WordTrace tailWord_8073484 prefixEnd_8073484 4145577848383795690420729 := by
  unfold tailWord_8073484
  simp only [CollatzResearch.WordTrace]
  refine ⟨147232076341576892068573753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196309435122102522758098337 147232076341576892068573753)
  ·
    refine ⟨110424057256182669051430315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147232076341576892068573753 110424057256182669051430315)
    ·
      refine ⟨165636085884274003577145473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110424057256182669051430315 165636085884274003577145473)
      ·
        refine ⟨124227064413205502682859105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165636085884274003577145473 124227064413205502682859105)
        ·
          refine ⟨93170298309904127012144329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124227064413205502682859105 93170298309904127012144329)
          ·
            refine ⟨69877723732428095259108247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93170298309904127012144329 69877723732428095259108247)
            ·
              refine ⟨104816585598642142888662371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69877723732428095259108247 104816585598642142888662371)
              ·
                refine ⟨157224878397963214332993557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104816585598642142888662371 157224878397963214332993557)
                ·
                  refine ⟨7369916174904525671859073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157224878397963214332993557 7369916174904525671859073)
                  ·
                    refine ⟨5527437131178394253894305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7369916174904525671859073 5527437131178394253894305)
                    ·
                      refine ⟨4145577848383795690420729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527437131178394253894305 4145577848383795690420729)
                      ·
                        rfl

theorem cell23_8073484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_8073484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073484 prefixEnd_8073484 := by exact prefixLift 8073484
  have htrace : WordTrace (prefixWord ++ tailWord_8073484) baseStart_8073484 baseEnd_8073484 := by
    simpa [prefixWord, tailWord_8073484, baseEnd_8073484] using wordTrace_append hprefix tailTrace_8073484
  have hstable : (prefixWord ++ tailWord_8073484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073484).length < 2 ^ (prefixWord ++ tailWord_8073484).sum := by decide
  have hdescent : baseEnd_8073484 < baseStart_8073484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073500 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_8073500 : Nat := 118140960795 + 8073500 * 2 ^ 59
def prefixEnd_8073500 : Nat := 4983230072969 + 3 ^ 40 * 8073500 * 2
def baseEnd_8073500 : Nat := 4145586064074267627820655

theorem tailTrace_8073500 : CollatzResearch.WordTrace tailWord_8073500 prefixEnd_8073500 4145586064074267627820655 := by
  unfold tailWord_8073500
  simp only [CollatzResearch.WordTrace]
  refine ⟨147232368125547909434864977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196309824167397212579819969 147232368125547909434864977)
  ·
    refine ⟨110424276094160932076148733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147232368125547909434864977 110424276094160932076148733)
    ·
      refine ⟨41409103535310349528555775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110424276094160932076148733 41409103535310349528555775)
      ·
        refine ⟨62113655302965524292833663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41409103535310349528555775 62113655302965524292833663)
        ·
          refine ⟨93170482954448286439250495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62113655302965524292833663 93170482954448286439250495)
          ·
            refine ⟨139755724431672429658875743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93170482954448286439250495 139755724431672429658875743)
            ·
              refine ⟨209633586647508644488313615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139755724431672429658875743 209633586647508644488313615)
              ·
                refine ⟨314450379971262966732470423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209633586647508644488313615 314450379971262966732470423)
                ·
                  refine ⟨471675569956894450098705635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314450379971262966732470423 471675569956894450098705635)
                  ·
                    refine ⟨707513354935341675148058453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 471675569956894450098705635 707513354935341675148058453)
                    ·
                      refine ⟨4145586064074267627820655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 707513354935341675148058453 4145586064074267627820655)
                      ·
                        rfl

theorem cell23_8073500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_8073500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073500 prefixEnd_8073500 := by exact prefixLift 8073500
  have htrace : WordTrace (prefixWord ++ tailWord_8073500) baseStart_8073500 baseEnd_8073500 := by
    simpa [prefixWord, tailWord_8073500, baseEnd_8073500] using wordTrace_append hprefix tailTrace_8073500
  have hstable : (prefixWord ++ tailWord_8073500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073500).length < 2 ^ (prefixWord ++ tailWord_8073500).sum := by decide
  have hdescent : baseEnd_8073500 < baseStart_8073500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073520 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 1, 7]
def baseStart_8073520 : Nat := 118140960795 + 8073520 * 2 ^ 59
def prefixEnd_8073520 : Nat := 4983230072969 + 3 ^ 40 * 8073520 * 2
def baseEnd_8073520 : Nat := 1381865444562452516523521

theorem tailTrace_8073520 : CollatzResearch.WordTrace tailWord_8073520 prefixEnd_8073520 1381865444562452516523521 := by
  unfold tailWord_8073520
  simp only [CollatzResearch.WordTrace]
  refine ⟨147232732855511681142729007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196310310474015574856972009 147232732855511681142729007)
  ·
    refine ⟨220849099283267521714093511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147232732855511681142729007 220849099283267521714093511)
    ·
      refine ⟨331273648924901282571140267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220849099283267521714093511 331273648924901282571140267)
      ·
        refine ⟨496910473387351923856710401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331273648924901282571140267 496910473387351923856710401)
        ·
          refine ⟨372682855040513942892532801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496910473387351923856710401 372682855040513942892532801)
          ·
            refine ⟨279512141280385457169399601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372682855040513942892532801 279512141280385457169399601)
            ·
              refine ⟨209634105960289092877049701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279512141280385457169399601 209634105960289092877049701)
              ·
                refine ⟨39306394867554204914446819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209634105960289092877049701 39306394867554204914446819)
                ·
                  refine ⟨58959592301331307371670229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39306394867554204914446819 58959592301331307371670229)
                  ·
                    refine ⟨1381865444562452516523521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58959592301331307371670229 1381865444562452516523521)
                    ·
                      rfl

theorem cell23_8073520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_8073520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073520 prefixEnd_8073520 := by exact prefixLift 8073520
  have htrace : WordTrace (prefixWord ++ tailWord_8073520) baseStart_8073520 baseEnd_8073520 := by
    simpa [prefixWord, tailWord_8073520, baseEnd_8073520] using wordTrace_append hprefix tailTrace_8073520
  have hstable : (prefixWord ++ tailWord_8073520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073520).length < 2 ^ (prefixWord ++ tailWord_8073520).sum := by decide
  have hdescent : baseEnd_8073520 < baseStart_8073520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073577 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 3]
def baseStart_8073577 : Nat := 118140960795 + 8073577 * 2 ^ 59
def prefixEnd_8073577 : Nat := 4983230072969 + 3 ^ 40 * 8073577 * 2
def baseEnd_8073577 : Nat := 4145625602084663826557801

theorem tailTrace_8073577 : CollatzResearch.WordTrace tailWord_8073577 prefixEnd_8073577 4145625602084663826557801 := by
  unfold tailWord_8073577
  simp only [CollatzResearch.WordTrace]
  refine ⟨294467544671816861020282985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196311696447877907346855323 294467544671816861020282985)
  ·
    refine ⟨220850658503862645765212239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294467544671816861020282985 220850658503862645765212239)
    ·
      refine ⟨331275987755793968647818359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220850658503862645765212239 331275987755793968647818359)
      ·
        refine ⟨496913981633690952971727539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331275987755793968647818359 496913981633690952971727539)
        ·
          refine ⟨745370972450536429457591309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496913981633690952971727539 745370972450536429457591309)
          ·
            refine ⟨279514114668951161046596741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745370972450536429457591309 279514114668951161046596741)
            ·
              refine ⟨52408896500428342696236889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279514114668951161046596741 52408896500428342696236889)
              ·
                refine ⟨39306672375321257022177667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52408896500428342696236889 39306672375321257022177667)
                ·
                  refine ⟨58960008562981885533266501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39306672375321257022177667 58960008562981885533266501)
                  ·
                    refine ⟨11055001605559103537487469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58960008562981885533266501 11055001605559103537487469)
                    ·
                      refine ⟨4145625602084663826557801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11055001605559103537487469 4145625602084663826557801)
                      ·
                        rfl

theorem cell23_8073577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 4, 3].length) (baseStart_8073577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073577 prefixEnd_8073577 := by exact prefixLift 8073577
  have htrace : WordTrace (prefixWord ++ tailWord_8073577) baseStart_8073577 baseEnd_8073577 := by
    simpa [prefixWord, tailWord_8073577, baseEnd_8073577] using wordTrace_append hprefix tailTrace_8073577
  have hstable : (prefixWord ++ tailWord_8073577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073577).length < 2 ^ (prefixWord ++ tailWord_8073577).sum := by decide
  have hdescent : baseEnd_8073577 < baseStart_8073577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073584 : List Nat := [2, 1, 1, 1, 4, 4, 1, 2, 3, 4]
def baseStart_8073584 : Nat := 118140960795 + 8073584 * 2 ^ 59
def prefixEnd_8073584 : Nat := 4983230072969 + 3 ^ 40 * 8073584 * 2
def baseEnd_8073584 : Nat := 1381876398816415099723423

theorem tailTrace_8073584 : CollatzResearch.WordTrace tailWord_8073584 prefixEnd_8073584 1381876398816415099723423 := by
  unfold tailWord_8073584
  simp only [CollatzResearch.WordTrace]
  refine ⟨147233899991395750607893903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196311866655194334143858537 147233899991395750607893903)
  ·
    refine ⟨220850849987093625911840855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147233899991395750607893903 220850849987093625911840855)
    ·
      refine ⟨331276274980640438867761283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220850849987093625911840855 331276274980640438867761283)
      ·
        refine ⟨496914412470960658301641925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331276274980640438867761283 496914412470960658301641925)
        ·
          refine ⟨93171452338305123431557861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496914412470960658301641925 93171452338305123431557861)
          ·
            refine ⟨17469647313432210643417099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93171452338305123431557861 17469647313432210643417099)
            ·
              refine ⟨26204470970148315965125649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17469647313432210643417099 26204470970148315965125649)
              ·
                refine ⟨19653353227611236973844237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26204470970148315965125649 19653353227611236973844237)
                ·
                  refine ⟨7370007460354213865191589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19653353227611236973844237 7370007460354213865191589)
                  ·
                    refine ⟨1381876398816415099723423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370007460354213865191589 1381876398816415099723423)
                    ·
                      rfl

theorem cell23_8073584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 3, 4].length) (baseStart_8073584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073584 prefixEnd_8073584 := by exact prefixLift 8073584
  have htrace : WordTrace (prefixWord ++ tailWord_8073584) baseStart_8073584 baseEnd_8073584 := by
    simpa [prefixWord, tailWord_8073584, baseEnd_8073584] using wordTrace_append hprefix tailTrace_8073584
  have hstable : (prefixWord ++ tailWord_8073584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073584).length < 2 ^ (prefixWord ++ tailWord_8073584).sum := by decide
  have hdescent : baseEnd_8073584 < baseStart_8073584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073614 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 8]
def baseStart_8073614 : Nat := 118140960795 + 8073614 * 2 ^ 59
def prefixEnd_8073614 : Nat := 4983230072969 + 3 ^ 40 * 8073614 * 2
def baseEnd_8073614 : Nat := 460627177874320020199459

theorem tailTrace_8073614 : CollatzResearch.WordTrace tailWord_8073614 prefixEnd_8073614 460627177874320020199459 := by
  unfold tailWord_8073614
  simp only [CollatzResearch.WordTrace]
  refine ⟨36808611771585352042422487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196312596115121877559586597 36808611771585352042422487)
  ·
    refine ⟨55212917657378028063633731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36808611771585352042422487 55212917657378028063633731)
    ·
      refine ⟨82819376486067042095450597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55212917657378028063633731 82819376486067042095450597)
      ·
        refine ⟨15528633091137570392896987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82819376486067042095450597 15528633091137570392896987)
        ·
          refine ⟨23292949636706355589345481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15528633091137570392896987 23292949636706355589345481)
          ·
            refine ⟨17469712227529766692009111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23292949636706355589345481 17469712227529766692009111)
            ·
              refine ⟨26204568341294650038013667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17469712227529766692009111 26204568341294650038013667)
              ·
                refine ⟨39306852511941975057020501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26204568341294650038013667 39306852511941975057020501)
                ·
                  refine ⟨460627177874320020199459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39306852511941975057020501 460627177874320020199459)
                  ·
                    rfl

theorem cell23_8073614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_8073614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073614 prefixEnd_8073614 := by exact prefixLift 8073614
  have htrace : WordTrace (prefixWord ++ tailWord_8073614) baseStart_8073614 baseEnd_8073614 := by
    simpa [prefixWord, tailWord_8073614, baseEnd_8073614] using wordTrace_append hprefix tailTrace_8073614
  have hstable : (prefixWord ++ tailWord_8073614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073614).length < 2 ^ (prefixWord ++ tailWord_8073614).sum := by decide
  have hdescent : baseEnd_8073614 < baseStart_8073614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073674 : List Nat := [3, 1, 2, 1, 2, 2, 1, 3, 4, 4]
def baseStart_8073674 : Nat := 118140960795 + 8073674 * 2 ^ 59
def prefixEnd_8073674 : Nat := 4983230072969 + 3 ^ 40 * 8073674 * 2
def baseEnd_8073674 : Nat := 1381891803236049982348285

theorem tailTrace_8073674 : CollatzResearch.WordTrace tailWord_8073674 prefixEnd_8073674 1381891803236049982348285 := by
  unfold tailWord_8073674
  simp only [CollatzResearch.WordTrace]
  refine ⟨73617770638116361646641019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196314055034976964391042717 73617770638116361646641019)
  ·
    refine ⟨110426655957174542469961529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73617770638116361646641019 110426655957174542469961529)
    ·
      refine ⟨82819991967880906852471147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110426655957174542469961529 82819991967880906852471147)
      ·
        refine ⟨124229987951821360278706721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82819991967880906852471147 124229987951821360278706721)
        ·
          refine ⟨93172490963866020209030041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124229987951821360278706721 93172490963866020209030041)
          ·
            refine ⟨69879368222899515156772531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93172490963866020209030041 69879368222899515156772531)
            ·
              refine ⟨104819052334349272735158797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69879368222899515156772531 104819052334349272735158797)
              ·
                refine ⟨39307144625380977275684549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104819052334349272735158797 39307144625380977275684549)
                ·
                  refine ⟨7370089617258933239190853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39307144625380977275684549 7370089617258933239190853)
                  ·
                    refine ⟨1381891803236049982348285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370089617258933239190853 1381891803236049982348285)
                    ·
                      rfl

theorem cell23_8073674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_8073674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073674 prefixEnd_8073674 := by exact prefixLift 8073674
  have htrace : WordTrace (prefixWord ++ tailWord_8073674) baseStart_8073674 baseEnd_8073674 := by
    simpa [prefixWord, tailWord_8073674, baseEnd_8073674] using wordTrace_append hprefix tailTrace_8073674
  have hstable : (prefixWord ++ tailWord_8073674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073674).length < 2 ^ (prefixWord ++ tailWord_8073674).sum := by decide
  have hdescent : baseEnd_8073674 < baseStart_8073674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073732 : List Nat := [2, 3, 2, 3, 1, 2, 1, 4, 1, 2, 2]
def baseStart_8073732 : Nat := 118140960795 + 8073732 * 2 ^ 59
def prefixEnd_8073732 : Nat := 4983230072969 + 3 ^ 40 * 8073732 * 2
def baseEnd_8073732 : Nat := 4145705191586110720119589

theorem tailTrace_8073732 : CollatzResearch.WordTrace tailWord_8073732 prefixEnd_8073732 4145705191586110720119589 := by
  unfold tailWord_8073732
  simp only [CollatzResearch.WordTrace]
  refine ⟨147236598993127661246087725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196315465324170214994783633 147236598993127661246087725)
  ·
    refine ⟨55213724622422872967282897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147236598993127661246087725 55213724622422872967282897)
    ·
      refine ⟨41410293466817154725462173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55213724622422872967282897 41410293466817154725462173)
      ·
        refine ⟨15528860050056433022048315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41410293466817154725462173 15528860050056433022048315)
        ·
          refine ⟨23293290075084649533072473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15528860050056433022048315 23293290075084649533072473)
          ·
            refine ⟨17469967556313487149804355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23293290075084649533072473 17469967556313487149804355)
            ·
              refine ⟨26204951334470230724706533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17469967556313487149804355 26204951334470230724706533)
              ·
                refine ⟨4913428375213168260882475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26204951334470230724706533 4913428375213168260882475)
                ·
                  refine ⟨7370142562819752391323713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913428375213168260882475 7370142562819752391323713)
                  ·
                    refine ⟨5527606922114814293492785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7370142562819752391323713 5527606922114814293492785)
                    ·
                      refine ⟨4145705191586110720119589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527606922114814293492785 4145705191586110720119589)
                      ·
                        rfl

theorem cell23_8073732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_8073732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073732 prefixEnd_8073732 := by exact prefixLift 8073732
  have htrace : WordTrace (prefixWord ++ tailWord_8073732) baseStart_8073732 baseEnd_8073732 := by
    simpa [prefixWord, tailWord_8073732, baseEnd_8073732] using wordTrace_append hprefix tailTrace_8073732
  have hstable : (prefixWord ++ tailWord_8073732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073732).length < 2 ^ (prefixWord ++ tailWord_8073732).sum := by decide
  have hdescent : baseEnd_8073732 < baseStart_8073732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073748 : List Nat := [2, 4, 3, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_8073748 : Nat := 118140960795 + 8073748 * 2 ^ 59
def prefixEnd_8073748 : Nat := 4983230072969 + 3 ^ 40 * 8073748 * 2
def baseEnd_8073748 : Nat := 4145713407276582657519515

theorem tailTrace_8073748 : CollatzResearch.WordTrace tailWord_8073748 prefixEnd_8073748 4145713407276582657519515 := by
  unfold tailWord_8073748
  simp only [CollatzResearch.WordTrace]
  refine ⟨147236890777098678612378949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196315854369464904816505265 147236890777098678612378949)
  ·
    refine ⟨27606917020706002239821053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147236890777098678612378949 27606917020706002239821053)
    ·
      refine ⟨10352593882764750839932895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27606917020706002239821053 10352593882764750839932895)
      ·
        refine ⟨15528890824147126259899343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10352593882764750839932895 15528890824147126259899343)
        ·
          refine ⟨23293336236220689389849015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15528890824147126259899343 23293336236220689389849015)
          ·
            refine ⟨34940004354331034084773523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23293336236220689389849015 34940004354331034084773523)
            ·
              refine ⟨52410006531496551127160285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34940004354331034084773523 52410006531496551127160285)
              ·
                refine ⟨19653752449311206672685107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52410006531496551127160285 19653752449311206672685107)
                ·
                  refine ⟨29480628673966810009027661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19653752449311206672685107 29480628673966810009027661)
                  ·
                    refine ⟨11055235752737553753385373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29480628673966810009027661 11055235752737553753385373)
                    ·
                      refine ⟨4145713407276582657519515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11055235752737553753385373 4145713407276582657519515)
                      ·
                        rfl

theorem cell23_8073748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_8073748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073748 prefixEnd_8073748 := by exact prefixLift 8073748
  have htrace : WordTrace (prefixWord ++ tailWord_8073748) baseStart_8073748 baseEnd_8073748 := by
    simpa [prefixWord, tailWord_8073748, baseEnd_8073748] using wordTrace_append hprefix tailTrace_8073748
  have hstable : (prefixWord ++ tailWord_8073748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073748).length < 2 ^ (prefixWord ++ tailWord_8073748).sum := by decide
  have hdescent : baseEnd_8073748 < baseStart_8073748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073782 : List Nat := [5, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_8073782 : Nat := 118140960795 + 8073782 * 2 ^ 59
def prefixEnd_8073782 : Nat := 4983230072969 + 3 ^ 40 * 8073782 * 2
def baseEnd_8073782 : Nat := 4145730865618835524494359

theorem tailTrace_8073782 : CollatzResearch.WordTrace tailWord_8073782 prefixEnd_8073782 4145730865618835524494359 := by
  unfold tailWord_8073782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18404688852254636314468475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196316681090716120687663733 18404688852254636314468475)
  ·
    refine ⟨27607033278381954471702713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18404688852254636314468475 27607033278381954471702713)
    ·
      refine ⟨20705274958786465853777035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27607033278381954471702713 20705274958786465853777035)
      ·
        refine ⟨31057912438179698780665553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20705274958786465853777035 31057912438179698780665553)
        ·
          refine ⟨23293434328634774085499165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31057912438179698780665553 23293434328634774085499165)
          ·
            refine ⟨8735037873238040282062187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23293434328634774085499165 8735037873238040282062187)
            ·
              refine ⟨13102556809857060423093281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735037873238040282062187 13102556809857060423093281)
              ·
                refine ⟨9826917607392795317319961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13102556809857060423093281 9826917607392795317319961)
                ·
                  refine ⟨7370188205544596487989971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9826917607392795317319961 7370188205544596487989971)
                  ·
                    refine ⟨11055282308316894731984957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7370188205544596487989971 11055282308316894731984957)
                    ·
                      refine ⟨4145730865618835524494359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11055282308316894731984957 4145730865618835524494359)
                      ·
                        rfl

theorem cell23_8073782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_8073782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073782 prefixEnd_8073782 := by exact prefixLift 8073782
  have htrace : WordTrace (prefixWord ++ tailWord_8073782) baseStart_8073782 baseEnd_8073782 := by
    simpa [prefixWord, tailWord_8073782, baseEnd_8073782] using wordTrace_append hprefix tailTrace_8073782
  have hstable : (prefixWord ++ tailWord_8073782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073782).length < 2 ^ (prefixWord ++ tailWord_8073782).sum := by decide
  have hdescent : baseEnd_8073782 < baseStart_8073782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073784 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_8073784 : Nat := 118140960795 + 8073784 * 2 ^ 59
def prefixEnd_8073784 : Nat := 4983230072969 + 3 ^ 40 * 8073784 * 2
def baseEnd_8073784 : Nat := 4145731892580144516669349

theorem tailTrace_8073784 : CollatzResearch.WordTrace tailWord_8073784 prefixEnd_8073784 4145731892580144516669349 := by
  unfold tailWord_8073784
  simp only [CollatzResearch.WordTrace]
  refine ⟨147237547291033467686534203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196316729721377956915378937 147237547291033467686534203)
  ·
    refine ⟨220856320936550201529801305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147237547291033467686534203 220856320936550201529801305)
    ·
      refine ⟨165642240702412651147350979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220856320936550201529801305 165642240702412651147350979)
      ·
        refine ⟨248463361053618976721026469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165642240702412651147350979 248463361053618976721026469)
        ·
          refine ⟨46586880197553558135192463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248463361053618976721026469 46586880197553558135192463)
          ·
            refine ⟨69880320296330337202788695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46586880197553558135192463 69880320296330337202788695)
            ·
              refine ⟨104820480444495505804183043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69880320296330337202788695 104820480444495505804183043)
              ·
                refine ⟨157230720666743258706274565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104820480444495505804183043 157230720666743258706274565)
                ·
                  refine ⟨29480760125014361007426481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157230720666743258706274565 29480760125014361007426481)
                  ·
                    refine ⟨22110570093760770755569861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29480760125014361007426481 22110570093760770755569861)
                    ·
                      refine ⟨4145731892580144516669349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22110570093760770755569861 4145731892580144516669349)
                      ·
                        rfl

theorem cell23_8073784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_8073784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073784 prefixEnd_8073784 := by exact prefixLift 8073784
  have htrace : WordTrace (prefixWord ++ tailWord_8073784) baseStart_8073784 baseEnd_8073784 := by
    simpa [prefixWord, tailWord_8073784, baseEnd_8073784] using wordTrace_append hprefix tailTrace_8073784
  have hstable : (prefixWord ++ tailWord_8073784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073784).length < 2 ^ (prefixWord ++ tailWord_8073784).sum := by decide
  have hdescent : baseEnd_8073784 < baseStart_8073784 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073798 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_8073798 : Nat := 118140960795 + 8073798 * 2 ^ 59
def prefixEnd_8073798 : Nat := 4983230072969 + 3 ^ 40 * 8073798 * 2
def baseEnd_8073798 : Nat := 1381913027103102487298095

theorem tailTrace_8073798 : CollatzResearch.WordTrace tailWord_8073798 prefixEnd_8073798 1381913027103102487298095 := by
  unfold tailWord_8073798
  simp only [CollatzResearch.WordTrace]
  refine ⟨9202362662625506742627439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196317070136010810509385365 9202362662625506742627439)
  ·
    refine ⟨13803543993938260113941159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9202362662625506742627439 13803543993938260113941159)
    ·
      refine ⟨20705315990907390170911739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13803543993938260113941159 20705315990907390170911739)
      ·
        refine ⟨31057973986361085256367609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20705315990907390170911739 31057973986361085256367609)
        ·
          refine ⟨23293480489770813942275707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31057973986361085256367609 23293480489770813942275707)
          ·
            refine ⟨34940220734656220913413561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23293480489770813942275707 34940220734656220913413561)
            ·
              refine ⟨26205165550992165685060171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34940220734656220913413561 26205165550992165685060171)
              ·
                refine ⟨39307748326488248527590257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26205165550992165685060171 39307748326488248527590257)
                ·
                  refine ⟨29480811244866186395692693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39307748326488248527590257 29480811244866186395692693)
                  ·
                    refine ⟨1381913027103102487298095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29480811244866186395692693 1381913027103102487298095)
                    ·
                      rfl

theorem cell23_8073798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_8073798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073798 prefixEnd_8073798 := by exact prefixLift 8073798
  have htrace : WordTrace (prefixWord ++ tailWord_8073798) baseStart_8073798 baseEnd_8073798 := by
    simpa [prefixWord, tailWord_8073798, baseEnd_8073798] using wordTrace_append hprefix tailTrace_8073798
  have hstable : (prefixWord ++ tailWord_8073798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073798).length < 2 ^ (prefixWord ++ tailWord_8073798).sum := by decide
  have hdescent : baseEnd_8073798 < baseStart_8073798 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073805 : List Nat := [1, 6, 1, 1, 2, 1, 3, 1, 1, 4, 2]
def baseStart_8073805 : Nat := 118140960795 + 8073805 * 2 ^ 59
def prefixEnd_8073805 : Nat := 4983230072969 + 3 ^ 40 * 8073805 * 2
def baseEnd_8073805 : Nat := 4145742675673888934506753

theorem tailTrace_8073805 : CollatzResearch.WordTrace tailWord_8073805 prefixEnd_8073805 4145742675673888934506753 := by
  unfold tailWord_8073805
  simp only [CollatzResearch.WordTrace]
  refine ⟨294475860514990855959582869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196317240343327237306388579 294475860514990855959582869)
  ·
    refine ⟨13803555961640196373105447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 294475860514990855959582869 13803555961640196373105447)
    ·
      refine ⟨20705333942460294559658171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13803555961640196373105447 20705333942460294559658171)
      ·
        refine ⟨31058000913690441839487257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20705333942460294559658171 31058000913690441839487257)
        ·
          refine ⟨23293500685267831379615443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31058000913690441839487257 23293500685267831379615443)
          ·
            refine ⟨34940251027901747069423165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23293500685267831379615443 34940251027901747069423165)
            ·
              refine ⟨13102594135463155151033687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34940251027901747069423165 13102594135463155151033687)
              ·
                refine ⟨19653891203194732726550531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13102594135463155151033687 19653891203194732726550531)
                ·
                  refine ⟨29480836804792099089825797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19653891203194732726550531 29480836804792099089825797)
                  ·
                    refine ⟨5527656900898518579342337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29480836804792099089825797 5527656900898518579342337)
                    ·
                      refine ⟨4145742675673888934506753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527656900898518579342337 4145742675673888934506753)
                      ·
                        rfl

theorem cell23_8073805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_8073805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073805 prefixEnd_8073805 := by exact prefixLift 8073805
  have htrace : WordTrace (prefixWord ++ tailWord_8073805) baseStart_8073805 baseEnd_8073805 := by
    simpa [prefixWord, tailWord_8073805, baseEnd_8073805] using wordTrace_append hprefix tailTrace_8073805
  have hstable : (prefixWord ++ tailWord_8073805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073805).length < 2 ^ (prefixWord ++ tailWord_8073805).sum := by decide
  have hdescent : baseEnd_8073805 < baseStart_8073805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073824 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 1, 7]
def baseStart_8073824 : Nat := 118140960795 + 8073824 * 2 ^ 59
def prefixEnd_8073824 : Nat := 4983230072969 + 3 ^ 40 * 8073824 * 2
def baseEnd_8073824 : Nat := 1381917477268774786723055

theorem tailTrace_8073824 : CollatzResearch.WordTrace tailWord_8073824 prefixEnd_8073824 1381917477268774786723055 := by
  unfold tailWord_8073824
  simp only [CollatzResearch.WordTrace]
  refine ⟨147238276750961011102262263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196317702334614681469683017 147238276750961011102262263)
  ·
    refine ⟨220857415126441516653393395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147238276750961011102262263 220857415126441516653393395)
    ·
      refine ⟨331286122689662274980090093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220857415126441516653393395 331286122689662274980090093)
      ·
        refine ⟨124232296008623353117533785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331286122689662274980090093 124232296008623353117533785)
        ·
          refine ⟨93174222006467514838150339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124232296008623353117533785 93174222006467514838150339)
          ·
            refine ⟨139761333009701272257225509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93174222006467514838150339 139761333009701272257225509)
            ·
              refine ⟨26205249939318988548229783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139761333009701272257225509 26205249939318988548229783)
              ·
                refine ⟨39307874908978482822344675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26205249939318988548229783 39307874908978482822344675)
                ·
                  refine ⟨58961812363467724233517013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39307874908978482822344675 58961812363467724233517013)
                  ·
                    refine ⟨1381917477268774786723055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58961812363467724233517013 1381917477268774786723055)
                    ·
                      rfl

theorem cell23_8073824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_8073824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073824 prefixEnd_8073824 := by exact prefixLift 8073824
  have htrace : WordTrace (prefixWord ++ tailWord_8073824) baseStart_8073824 baseEnd_8073824 := by
    simpa [prefixWord, tailWord_8073824, baseEnd_8073824] using wordTrace_append hprefix tailTrace_8073824
  have hstable : (prefixWord ++ tailWord_8073824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073824).length < 2 ^ (prefixWord ++ tailWord_8073824).sum := by decide
  have hdescent : baseEnd_8073824 < baseStart_8073824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073831 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 7, 2]
def baseStart_8073831 : Nat := 118140960795 + 8073831 * 2 ^ 59
def prefixEnd_8073831 : Nat := 4983230072969 + 3 ^ 40 * 8073831 * 2
def baseEnd_8073831 : Nat := 4145756026170905832781633

theorem tailTrace_8073831 : CollatzResearch.WordTrace tailWord_8073831 prefixEnd_8073831 4145756026170905832781633 := by
  unfold tailWord_8073831
  simp only [CollatzResearch.WordTrace]
  refine ⟨294476808812896662400029347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196317872541931108266686231 294476808812896662400029347)
  ·
    refine ⟨441715213219344993600044021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294476808812896662400029347 441715213219344993600044021)
    ·
      refine ⟨41410801239313593150004127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441715213219344993600044021 41410801239313593150004127)
      ·
        refine ⟨62116201858970389725006191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41410801239313593150004127 62116201858970389725006191)
        ·
          refine ⟨93174302788455584587509287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62116201858970389725006191 93174302788455584587509287)
          ·
            refine ⟨139761454182683376881263931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93174302788455584587509287 139761454182683376881263931)
            ·
              refine ⟨209642181274025065321895897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139761454182683376881263931 209642181274025065321895897)
              ·
                refine ⟨157231635955518798991421923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209642181274025065321895897 157231635955518798991421923)
                ·
                  refine ⟨235847453933278198487132885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157231635955518798991421923 235847453933278198487132885)
                  ·
                    refine ⟨5527674701561207777042177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235847453933278198487132885 5527674701561207777042177)
                    ·
                      refine ⟨4145756026170905832781633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527674701561207777042177 4145756026170905832781633)
                      ·
                        rfl

theorem cell23_8073831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_8073831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073831 prefixEnd_8073831 := by exact prefixLift 8073831
  have htrace : WordTrace (prefixWord ++ tailWord_8073831) baseStart_8073831 baseEnd_8073831 := by
    simpa [prefixWord, tailWord_8073831, baseEnd_8073831] using wordTrace_append hprefix tailTrace_8073831
  have hstable : (prefixWord ++ tailWord_8073831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073831).length < 2 ^ (prefixWord ++ tailWord_8073831).sum := by decide
  have hdescent : baseEnd_8073831 < baseStart_8073831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073845 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 7]
def baseStart_8073845 : Nat := 118140960795 + 8073845 * 2 ^ 59
def prefixEnd_8073845 : Nat := 4983230072969 + 3 ^ 40 * 8073845 * 2
def baseEnd_8073845 : Nat := 460640357211118753111841

theorem tailTrace_8073845 : CollatzResearch.WordTrace tailWord_8073845 prefixEnd_8073845 460640357211118753111841 := by
  unfold tailWord_8073845
  simp only [CollatzResearch.WordTrace]
  refine ⟨294477319434845942791038989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196318212956563961860692659 294477319434845942791038989)
  ·
    refine ⟨110428994788067228546639621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294477319434845942791038989 110428994788067228546639621)
    ·
      refine ⟨20705436522762605352494929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110428994788067228546639621 20705436522762605352494929)
      ·
        refine ⟨15529077392071954014371197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20705436522762605352494929 15529077392071954014371197)
        ·
          refine ⟨5823404022026982755389199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15529077392071954014371197 5823404022026982755389199)
          ·
            refine ⟨8735106033040474133083799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5823404022026982755389199 8735106033040474133083799)
            ·
              refine ⟨13102659049560711199625699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735106033040474133083799 13102659049560711199625699)
              ·
                refine ⟨19653988574341066799438549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13102659049560711199625699 19653988574341066799438549)
                ·
                  refine ⟨460640357211118753111841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19653988574341066799438549 460640357211118753111841)
                  ·
                    rfl

theorem cell23_8073845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 7].length) (baseStart_8073845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073845 prefixEnd_8073845 := by exact prefixLift 8073845
  have htrace : WordTrace (prefixWord ++ tailWord_8073845) baseStart_8073845 baseEnd_8073845 := by
    simpa [prefixWord, tailWord_8073845, baseEnd_8073845] using wordTrace_append hprefix tailTrace_8073845
  have hstable : (prefixWord ++ tailWord_8073845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073845).length < 2 ^ (prefixWord ++ tailWord_8073845).sum := by decide
  have hdescent : baseEnd_8073845 < baseStart_8073845 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073904 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_8073904 : Nat := 118140960795 + 8073904 * 2 ^ 59
def prefixEnd_8073904 : Nat := 4983230072969 + 3 ^ 40 * 8073904 * 2
def baseEnd_8073904 : Nat := 4145793510258684047168797

theorem tailTrace_8073904 : CollatzResearch.WordTrace tailWord_8073904 prefixEnd_8073904 4145793510258684047168797 := by
  unfold tailWord_8073904
  simp only [CollatzResearch.WordTrace]
  refine ⟨147239735670816097933718383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196319647561088130578291177 147239735670816097933718383)
  ·
    refine ⟨220859603506224146900577575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147239735670816097933718383 220859603506224146900577575)
    ·
      refine ⟨331289405259336220350866363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220859603506224146900577575 331289405259336220350866363)
      ·
        refine ⟨496934107889004330526299545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331289405259336220350866363 496934107889004330526299545)
        ·
          refine ⟨372700580916753247894724659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496934107889004330526299545 372700580916753247894724659)
          ·
            refine ⟨559050871375129871842086989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372700580916753247894724659 559050871375129871842086989)
            ·
              refine ⟨209644076765673701940782621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559050871375129871842086989 209644076765673701940782621)
              ·
                refine ⟨78616528787127638227793483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209644076765673701940782621 78616528787127638227793483)
                ·
                  refine ⟨117924793180691457341690225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78616528787127638227793483 117924793180691457341690225)
                  ·
                    refine ⟨88443594885518593006267669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117924793180691457341690225 88443594885518593006267669)
                    ·
                      refine ⟨4145793510258684047168797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88443594885518593006267669 4145793510258684047168797)
                      ·
                        rfl

theorem cell23_8073904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_8073904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073904 prefixEnd_8073904 := by exact prefixLift 8073904
  have htrace : WordTrace (prefixWord ++ tailWord_8073904) baseStart_8073904 baseEnd_8073904 := by
    simpa [prefixWord, tailWord_8073904, baseEnd_8073904] using wordTrace_append hprefix tailTrace_8073904
  have hstable : (prefixWord ++ tailWord_8073904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073904).length < 2 ^ (prefixWord ++ tailWord_8073904).sum := by decide
  have hdescent : baseEnd_8073904 < baseStart_8073904 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073928 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_8073928 : Nat := 118140960795 + 8073928 * 2 ^ 59
def prefixEnd_8073928 : Nat := 4983230072969 + 3 ^ 40 * 8073928 * 2
def baseEnd_8073928 : Nat := 4145805833794391953268687

theorem tailTrace_8073928 : CollatzResearch.WordTrace tailWord_8073928 prefixEnd_8073928 4145805833794391953268687 := by
  unfold tailWord_8073928
  simp only [CollatzResearch.WordTrace]
  refine ⟨147240173346772623983155219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196320231129030165310873625 147240173346772623983155219)
  ·
    refine ⟨220860260020158935974732829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147240173346772623983155219 220860260020158935974732829)
    ·
      refine ⟨82822597507559600990524811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220860260020158935974732829 82822597507559600990524811)
      ·
        refine ⟨124233896261339401485787217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82822597507559600990524811 124233896261339401485787217)
        ·
          refine ⟨93175422196004551114340413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124233896261339401485787217 93175422196004551114340413)
          ·
            refine ⟨34940783323501706667877655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93175422196004551114340413 34940783323501706667877655)
            ·
              refine ⟨52411174985252560001816483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34940783323501706667877655 52411174985252560001816483)
              ·
                refine ⟨78616762477878840002724725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52411174985252560001816483 78616762477878840002724725)
                ·
                  refine ⟨7370321482301141250255443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78616762477878840002724725 7370321482301141250255443)
                  ·
                    refine ⟨11055482223451711875383165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7370321482301141250255443 11055482223451711875383165)
                    ·
                      refine ⟨4145805833794391953268687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11055482223451711875383165 4145805833794391953268687)
                      ·
                        rfl

theorem cell23_8073928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_8073928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073928 prefixEnd_8073928 := by exact prefixLift 8073928
  have htrace : WordTrace (prefixWord ++ tailWord_8073928) baseStart_8073928 baseEnd_8073928 := by
    simpa [prefixWord, tailWord_8073928, baseEnd_8073928] using wordTrace_append hprefix tailTrace_8073928
  have hstable : (prefixWord ++ tailWord_8073928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073928).length < 2 ^ (prefixWord ++ tailWord_8073928).sum := by decide
  have hdescent : baseEnd_8073928 < baseStart_8073928 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073978 : List Nat := [3, 1, 1, 1, 1, 3, 2, 5, 2, 4]
def baseStart_8073978 : Nat := 118140960795 + 8073978 * 2 ^ 59
def prefixEnd_8073978 : Nat := 4983230072969 + 3 ^ 40 * 8073978 * 2
def baseEnd_8073978 : Nat := 1381943835942372252547819

theorem tailTrace_8073978 : CollatzResearch.WordTrace tailWord_8073978 prefixEnd_8073978 1381943835942372252547819 := by
  unfold tailWord_8073978
  simp only [CollatzResearch.WordTrace]
  refine ⟨73620542585841026626407647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196321446895576071003753725 73620542585841026626407647)
  ·
    refine ⟨110430813878761539939611471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73620542585841026626407647 110430813878761539939611471)
    ·
      refine ⟨165646220818142309909417207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110430813878761539939611471 165646220818142309909417207)
      ·
        refine ⟨248469331227213464864125811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165646220818142309909417207 248469331227213464864125811)
        ·
          refine ⟨372703996840820197296188717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248469331227213464864125811 372703996840820197296188717)
          ·
            refine ⟨139763998815307573986070769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372703996840820197296188717 139763998815307573986070769)
            ·
              refine ⟨104822999111480680489553077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139763998815307573986070769 104822999111480680489553077)
              ·
                refine ⟨9827156166701313795895601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104822999111480680489553077 9827156166701313795895601)
                ·
                  refine ⟨7370367125025985346921701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9827156166701313795895601 7370367125025985346921701)
                  ·
                    refine ⟨1381943835942372252547819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370367125025985346921701 1381943835942372252547819)
                    ·
                      rfl

theorem cell23_8073978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 5, 2, 4].length) (baseStart_8073978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073978 prefixEnd_8073978 := by exact prefixLift 8073978
  have htrace : WordTrace (prefixWord ++ tailWord_8073978) baseStart_8073978 baseEnd_8073978 := by
    simpa [prefixWord, tailWord_8073978, baseEnd_8073978] using wordTrace_append hprefix tailTrace_8073978
  have hstable : (prefixWord ++ tailWord_8073978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073978).length < 2 ^ (prefixWord ++ tailWord_8073978).sum := by decide
  have hdescent : baseEnd_8073978 < baseStart_8073978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8073981 : List Nat := [1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 6]
def baseStart_8073981 : Nat := 118140960795 + 8073981 * 2 ^ 59
def prefixEnd_8073981 : Nat := 4983230072969 + 3 ^ 40 * 8073981 * 2
def baseEnd_8073981 : Nat := 4145833048269080245905943

theorem tailTrace_8073981 : CollatzResearch.WordTrace tailWord_8073981 prefixEnd_8073981 4145833048269080245905943 := by
  unfold tailWord_8073981
  simp only [CollatzResearch.WordTrace]
  refine ⟨294482279762353238017989797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196321519841568825345326531 294482279762353238017989797)
  ·
    refine ⟨55215427455441232128373087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294482279762353238017989797 55215427455441232128373087)
    ·
      refine ⟨82823141183161848192559631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55215427455441232128373087 82823141183161848192559631)
      ·
        refine ⟨124234711774742772288839447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82823141183161848192559631 124234711774742772288839447)
        ·
          refine ⟨186352067662114158433259171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124234711774742772288839447 186352067662114158433259171)
          ·
            refine ⟨279528101493171237649888757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186352067662114158433259171 279528101493171237649888757)
            ·
              refine ⟨26205759514984803529677071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279528101493171237649888757 26205759514984803529677071)
              ·
                refine ⟨39308639272477205294515607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26205759514984803529677071 39308639272477205294515607)
                ·
                  refine ⟨58962958908715807941773411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39308639272477205294515607 58962958908715807941773411)
                  ·
                    refine ⟨88444438363073711912660117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58962958908715807941773411 88444438363073711912660117)
                    ·
                      refine ⟨4145833048269080245905943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88444438363073711912660117 4145833048269080245905943)
                      ·
                        rfl

theorem cell23_8073981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 1, 6].length) (baseStart_8073981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8073981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8073981 prefixEnd_8073981 := by exact prefixLift 8073981
  have htrace : WordTrace (prefixWord ++ tailWord_8073981) baseStart_8073981 baseEnd_8073981 := by
    simpa [prefixWord, tailWord_8073981, baseEnd_8073981] using wordTrace_append hprefix tailTrace_8073981
  have hstable : (prefixWord ++ tailWord_8073981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8073981).length < 2 ^ (prefixWord ++ tailWord_8073981).sum := by decide
  have hdescent : baseEnd_8073981 < baseStart_8073981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8073981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074021 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 2, 7]
def baseStart_8074021 : Nat := 118140960795 + 8074021 * 2 ^ 59
def prefixEnd_8074021 : Nat := 4983230072969 + 3 ^ 40 * 8074021 * 2
def baseEnd_8074021 : Nat := 1381951195831753363135253

theorem tailTrace_8074021 : CollatzResearch.WordTrace tailWord_8074021 prefixEnd_8074021 1381951195831753363135253 := by
  unfold tailWord_8074021
  simp only [CollatzResearch.WordTrace]
  refine ⟨294483738682208324849445917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196322492454805549899630611 294483738682208324849445917)
  ·
    refine ⟨110431402005828121818542219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294483738682208324849445917 110431402005828121818542219)
    ·
      refine ⟨165647103008742182727813329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110431402005828121818542219 165647103008742182727813329)
      ·
        refine ⟨124235327256556637045859997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165647103008742182727813329 124235327256556637045859997)
        ·
          refine ⟨46588247721208738892197499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124235327256556637045859997 46588247721208738892197499)
          ·
            refine ⟨69882371581813108338296249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46588247721208738892197499 69882371581813108338296249)
            ·
              refine ⟨52411778686359831253722187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69882371581813108338296249 52411778686359831253722187)
              ·
                refine ⟨78617668029539746880583281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52411778686359831253722187 78617668029539746880583281)
                ·
                  refine ⟨58963251022154810160437461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78617668029539746880583281 58963251022154810160437461)
                  ·
                    refine ⟨1381951195831753363135253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58963251022154810160437461 1381951195831753363135253)
                    ·
                      rfl

theorem cell23_8074021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_8074021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074021 prefixEnd_8074021 := by exact prefixLift 8074021
  have htrace : WordTrace (prefixWord ++ tailWord_8074021) baseStart_8074021 baseEnd_8074021 := by
    simpa [prefixWord, tailWord_8074021, baseEnd_8074021] using wordTrace_append hprefix tailTrace_8074021
  have hstable : (prefixWord ++ tailWord_8074021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074021).length < 2 ^ (prefixWord ++ tailWord_8074021).sum := by decide
  have hdescent : baseEnd_8074021 < baseStart_8074021 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074029 : List Nat := [1, 5, 3, 2, 1, 1, 1, 3, 2, 4]
def baseStart_8074029 : Nat := 118140960795 + 8074029 * 2 ^ 59
def prefixEnd_8074029 : Nat := 4983230072969 + 3 ^ 40 * 8074029 * 2
def baseEnd_8074029 : Nat := 1381952565113498686035241

theorem tailTrace_8074029 : CollatzResearch.WordTrace tailWord_8074029 prefixEnd_8074029 1381952565113498686035241 := by
  unfold tailWord_8074029
  simp only [CollatzResearch.WordTrace]
  refine ⟨294484030466179342215737141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196322686977452894810491427 294484030466179342215737141)
  ·
    refine ⟨27607877856204313332725357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294484030466179342215737141 27607877856204313332725357)
    ·
      refine ⟨10352954196076617499772009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27607877856204313332725357 10352954196076617499772009)
      ·
        refine ⟨7764715647057463124829007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10352954196076617499772009 7764715647057463124829007)
        ·
          refine ⟨11647073470586194687243511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7764715647057463124829007 11647073470586194687243511)
          ·
            refine ⟨17470610205879292030865267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11647073470586194687243511 17470610205879292030865267)
            ·
              refine ⟨26205915308818938046297901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17470610205879292030865267 26205915308818938046297901)
              ·
                refine ⟨9827218240807101767361713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26205915308818938046297901 9827218240807101767361713)
                ·
                  refine ⟨7370413680605326325521285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9827218240807101767361713 7370413680605326325521285)
                  ·
                    refine ⟨1381952565113498686035241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370413680605326325521285 1381952565113498686035241)
                    ·
                      rfl

theorem cell23_8074029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_8074029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074029 prefixEnd_8074029 := by exact prefixLift 8074029
  have htrace : WordTrace (prefixWord ++ tailWord_8074029) baseStart_8074029 baseEnd_8074029 := by
    simpa [prefixWord, tailWord_8074029, baseEnd_8074029] using wordTrace_append hprefix tailTrace_8074029
  have hstable : (prefixWord ++ tailWord_8074029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074029).length < 2 ^ (prefixWord ++ tailWord_8074029).sum := by decide
  have hdescent : baseEnd_8074029 < baseStart_8074029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074088 : List Nat := [2, 1, 4, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_8074088 : Nat := 118140960795 + 8074088 * 2 ^ 59
def prefixEnd_8074088 : Nat := 4983230072969 + 3 ^ 40 * 8074088 * 2
def baseEnd_8074088 : Nat := 4145887990699111327267951

theorem tailTrace_8074088 : CollatzResearch.WordTrace tailWord_8074088 prefixEnd_8074088 4145887990699111327267951 := by
  unfold tailWord_8074088
  simp only [CollatzResearch.WordTrace]
  refine ⟨147243091186482797646067459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196324121581977063528089945 147243091186482797646067459)
  ·
    refine ⟨220864636779724196469101189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147243091186482797646067459 220864636779724196469101189)
    ·
      refine ⟨41412119396198286837956473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220864636779724196469101189 41412119396198286837956473)
      ·
        refine ⟨31059089547148715128467355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41412119396198286837956473 31059089547148715128467355)
        ·
          refine ⟨46588634320723072692701033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31059089547148715128467355 46588634320723072692701033)
          ·
            refine ⟨34941475740542304519525775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46588634320723072692701033 34941475740542304519525775)
            ·
              refine ⟨52412213610813456779288663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34941475740542304519525775 52412213610813456779288663)
              ·
                refine ⟨78618320416220185168932995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52412213610813456779288663 78618320416220185168932995)
                ·
                  refine ⟨117927480624330277753399493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78618320416220185168932995 117927480624330277753399493)
                  ·
                    refine ⟨22111402617061927078762405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117927480624330277753399493 22111402617061927078762405)
                    ·
                      refine ⟨4145887990699111327267951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22111402617061927078762405 4145887990699111327267951)
                      ·
                        rfl

theorem cell23_8074088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_8074088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074088 prefixEnd_8074088 := by exact prefixLift 8074088
  have htrace : WordTrace (prefixWord ++ tailWord_8074088) baseStart_8074088 baseEnd_8074088 := by
    simpa [prefixWord, tailWord_8074088, baseEnd_8074088] using wordTrace_append hprefix tailTrace_8074088
  have hstable : (prefixWord ++ tailWord_8074088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074088).length < 2 ^ (prefixWord ++ tailWord_8074088).sum := by decide
  have hdescent : baseEnd_8074088 < baseStart_8074088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074092 : List Nat := [2, 2, 1, 1, 4, 1, 1, 5, 2, 2, 2]
def baseStart_8074092 : Nat := 118140960795 + 8074092 * 2 ^ 59
def prefixEnd_8074092 : Nat := 4983230072969 + 3 ^ 40 * 8074092 * 2
def baseEnd_8074092 : Nat := 4145890044621729311617933

theorem tailTrace_8074092 : CollatzResearch.WordTrace tailWord_8074092 prefixEnd_8074092 4145890044621729311617933 := by
  unfold tailWord_8074092
  simp only [CollatzResearch.WordTrace]
  refine ⟨147243164132475551987640265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196324218843300735983520353 147243164132475551987640265)
  ·
    refine ⟨110432373099356663990730199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147243164132475551987640265 110432373099356663990730199)
    ·
      refine ⟨165648559649034995986095299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110432373099356663990730199 165648559649034995986095299)
      ·
        refine ⟨248472839473552493979142949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165648559649034995986095299 248472839473552493979142949)
        ·
          refine ⟨46588657401291092621089303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248472839473552493979142949 46588657401291092621089303)
          ·
            refine ⟨69882986101936638931633955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46588657401291092621089303 69882986101936638931633955)
            ·
              refine ⟨104824479152904958397450933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69882986101936638931633955 104824479152904958397450933)
              ·
                refine ⟨9827294920584839849761025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104824479152904958397450933 9827294920584839849761025)
                ·
                  refine ⟨7370471190438629887320769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9827294920584839849761025 7370471190438629887320769)
                  ·
                    refine ⟨5527853392828972415490577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7370471190438629887320769 5527853392828972415490577)
                    ·
                      refine ⟨4145890044621729311617933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527853392828972415490577 4145890044621729311617933)
                      ·
                        rfl

theorem cell23_8074092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 2, 2].length) (baseStart_8074092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074092 prefixEnd_8074092 := by exact prefixLift 8074092
  have htrace : WordTrace (prefixWord ++ tailWord_8074092) baseStart_8074092 baseEnd_8074092 := by
    simpa [prefixWord, tailWord_8074092, baseEnd_8074092] using wordTrace_append hprefix tailTrace_8074092
  have hstable : (prefixWord ++ tailWord_8074092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074092).length < 2 ^ (prefixWord ++ tailWord_8074092).sum := by decide
  have hdescent : baseEnd_8074092 < baseStart_8074092 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074115 : List Nat := [1, 1, 1, 3, 4, 1, 4, 3, 5]
def baseStart_8074115 : Nat := 118140960795 + 8074115 * 2 ^ 59
def prefixEnd_8074115 : Nat := 4983230072969 + 3 ^ 40 * 8074115 * 2
def baseEnd_8074115 : Nat := 460655761630753635736703

theorem tailTrace_8074115 : CollatzResearch.WordTrace tailWord_8074115 prefixEnd_8074115 460655761630753635736703 := by
  unfold tailWord_8074115
  simp only [CollatzResearch.WordTrace]
  refine ⟨294487167143867778903367799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196324778095911852602245199 294487167143867778903367799)
  ·
    refine ⟨441730750715801668355051699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294487167143867778903367799 441730750715801668355051699)
    ·
      refine ⟨662596126073702502532577549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441730750715801668355051699 662596126073702502532577549)
      ·
        refine ⟨248473547277638438449716581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662596126073702502532577549 248473547277638438449716581)
        ·
          refine ⟨46588790114557207209321859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248473547277638438449716581 46588790114557207209321859)
          ·
            refine ⟨69883185171835810813982789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46588790114557207209321859 69883185171835810813982789)
            ·
              refine ⟨13103097219719214527621773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69883185171835810813982789 13103097219719214527621773)
              ·
                refine ⟨4913661457394705447858165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13103097219719214527621773 4913661457394705447858165)
                ·
                  refine ⟨460655761630753635736703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913661457394705447858165 460655761630753635736703)
                  ·
                    rfl

theorem cell23_8074115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 3, 5].length) (baseStart_8074115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074115 prefixEnd_8074115 := by exact prefixLift 8074115
  have htrace : WordTrace (prefixWord ++ tailWord_8074115) baseStart_8074115 baseEnd_8074115 := by
    simpa [prefixWord, tailWord_8074115, baseEnd_8074115] using wordTrace_append hprefix tailTrace_8074115
  have hstable : (prefixWord ++ tailWord_8074115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074115).length < 2 ^ (prefixWord ++ tailWord_8074115).sum := by decide
  have hdescent : baseEnd_8074115 < baseStart_8074115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074148 : List Nat := [2, 3, 1, 2, 1, 2, 1, 1, 3, 3, 4]
def baseStart_8074148 : Nat := 118140960795 + 8074148 * 2 ^ 59
def prefixEnd_8074148 : Nat := 4983230072969 + 3 ^ 40 * 8074148 * 2
def baseEnd_8074148 : Nat := 4145918799538381092517675

theorem tailTrace_8074148 : CollatzResearch.WordTrace tailWord_8074148 prefixEnd_8074148 4145918799538381092517675 := by
  unfold tailWord_8074148
  simp only [CollatzResearch.WordTrace]
  refine ⟨147244185376374112769659549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196325580501832150359546065 147244185376374112769659549)
  ·
    refine ⟨55216569516140292288622331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147244185376374112769659549 55216569516140292288622331)
    ·
      refine ⟨82824854274210438432933497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55216569516140292288622331 82824854274210438432933497)
      ·
        refine ⟨62118640705657828824700123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82824854274210438432933497 62118640705657828824700123)
        ·
          refine ⟨93177961058486743237050185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62118640705657828824700123 93177961058486743237050185)
          ·
            refine ⟨69883470793865057427787639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93177961058486743237050185 69883470793865057427787639)
            ·
              refine ⟨104825206190797586141681459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69883470793865057427787639 104825206190797586141681459)
              ·
                refine ⟨157237809286196379212522189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104825206190797586141681459 157237809286196379212522189)
                ·
                  refine ⟨58964178482323642204695821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157237809286196379212522189 58964178482323642204695821)
                  ·
                    refine ⟨22111566930871365826760933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58964178482323642204695821 22111566930871365826760933)
                    ·
                      refine ⟨4145918799538381092517675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22111566930871365826760933 4145918799538381092517675)
                      ·
                        rfl

theorem cell23_8074148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_8074148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074148 prefixEnd_8074148 := by exact prefixLift 8074148
  have htrace : WordTrace (prefixWord ++ tailWord_8074148) baseStart_8074148 baseEnd_8074148 := by
    simpa [prefixWord, tailWord_8074148, baseEnd_8074148] using wordTrace_append hprefix tailTrace_8074148
  have hstable : (prefixWord ++ tailWord_8074148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074148).length < 2 ^ (prefixWord ++ tailWord_8074148).sum := by decide
  have hdescent : baseEnd_8074148 < baseStart_8074148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074165 : List Nat := [1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 4]
def baseStart_8074165 : Nat := 118140960795 + 8074165 * 2 ^ 59
def prefixEnd_8074165 : Nat := 4983230072969 + 3 ^ 40 * 8074165 * 2
def baseEnd_8074165 : Nat := 4145927528709507526005097

theorem tailTrace_8074165 : CollatzResearch.WordTrace tailWord_8074165 prefixEnd_8074165 4145927528709507526005097 := by
  unfold tailWord_8074165
  simp only [CollatzResearch.WordTrace]
  refine ⟨294488990793686637442687949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196325993862457758295125299 294488990793686637442687949)
  ·
    refine ⟨110433371547632489041007981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294488990793686637442687949 110433371547632489041007981)
    ·
      refine ⟨41412514330362183390377993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110433371547632489041007981 41412514330362183390377993)
      ·
        refine ⟨31059385747771637542783495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41412514330362183390377993 31059385747771637542783495)
        ·
          refine ⟨46589078621657456314175243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31059385747771637542783495 46589078621657456314175243)
          ·
            refine ⟨69883617932486184471262865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46589078621657456314175243 69883617932486184471262865)
            ·
              refine ⟨52412713449364638353447149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69883617932486184471262865 52412713449364638353447149)
              ·
                refine ⟨19654767543511739382542681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52412713449364638353447149 19654767543511739382542681)
                ·
                  refine ⟨14741075657633804536907011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19654767543511739382542681 14741075657633804536907011)
                  ·
                    refine ⟨22111613486450706805360517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14741075657633804536907011 22111613486450706805360517)
                    ·
                      refine ⟨4145927528709507526005097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22111613486450706805360517 4145927528709507526005097)
                      ·
                        rfl

theorem cell23_8074165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_8074165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074165 prefixEnd_8074165 := by exact prefixLift 8074165
  have htrace : WordTrace (prefixWord ++ tailWord_8074165) baseStart_8074165 baseEnd_8074165 := by
    simpa [prefixWord, tailWord_8074165, baseEnd_8074165] using wordTrace_append hprefix tailTrace_8074165
  have hstable : (prefixWord ++ tailWord_8074165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074165).length < 2 ^ (prefixWord ++ tailWord_8074165).sum := by decide
  have hdescent : baseEnd_8074165 < baseStart_8074165 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074188 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 8]
def baseStart_8074188 : Nat := 118140960795 + 8074188 * 2 ^ 59
def prefixEnd_8074188 : Nat := 4983230072969 + 3 ^ 40 * 8074188 * 2
def baseEnd_8074188 : Nat := 460659926529395659557499

theorem tailTrace_8074188 : CollatzResearch.WordTrace tailWord_8074188 prefixEnd_8074188 460659926529395659557499 := by
  unfold tailWord_8074188
  simp only [CollatzResearch.WordTrace]
  refine ⟨147244914836301656185387609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196326553115068874913850145 147244914836301656185387609)
  ·
    refine ⟨110433686127226242139040707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147244914836301656185387609 110433686127226242139040707)
    ·
      refine ⟨165650529190839363208561061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110433686127226242139040707 165650529190839363208561061)
      ·
        refine ⟨31059474223282380601605199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165650529190839363208561061 31059474223282380601605199)
        ·
          refine ⟨46589211334923570902407799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31059474223282380601605199 46589211334923570902407799)
          ·
            refine ⟨69883817002385356353611699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46589211334923570902407799 69883817002385356353611699)
            ·
              refine ⟨104825725503578034530417549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69883817002385356353611699 104825725503578034530417549)
              ·
                refine ⟨39309647063841762948906581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104825725503578034530417549 39309647063841762948906581)
                ·
                  refine ⟨460659926529395659557499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39309647063841762948906581 460659926529395659557499)
                  ·
                    rfl

theorem cell23_8074188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 8].length) (baseStart_8074188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074188 prefixEnd_8074188 := by exact prefixLift 8074188
  have htrace : WordTrace (prefixWord ++ tailWord_8074188) baseStart_8074188 baseEnd_8074188 := by
    simpa [prefixWord, tailWord_8074188, baseEnd_8074188] using wordTrace_append hprefix tailTrace_8074188
  have hstable : (prefixWord ++ tailWord_8074188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074188).length < 2 ^ (prefixWord ++ tailWord_8074188).sum := by decide
  have hdescent : baseEnd_8074188 < baseStart_8074188 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074276 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 2, 3, 2]
def baseStart_8074276 : Nat := 118140960795 + 8074276 * 2 ^ 59
def prefixEnd_8074276 : Nat := 4983230072969 + 3 ^ 40 * 8074276 * 2
def baseEnd_8074276 : Nat := 4145984525062156591717087

theorem tailTrace_8074276 : CollatzResearch.WordTrace tailWord_8074276 prefixEnd_8074276 4145984525062156591717087 := by
  unfold tailWord_8074276
  simp only [CollatzResearch.WordTrace]
  refine ⟨147246519648142251699989341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196328692864189668933319121 147246519648142251699989341)
  ·
    refine ⟨55217444868053344387496003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147246519648142251699989341 55217444868053344387496003)
    ·
      refine ⟨82826167302080016581244005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55217444868053344387496003 82826167302080016581244005)
      ·
        refine ⟨15529906369140003108983251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82826167302080016581244005 15529906369140003108983251)
        ·
          refine ⟨23294859553710004663474877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15529906369140003108983251 23294859553710004663474877)
          ·
            refine ⟨8735572332641251748803079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23294859553710004663474877 8735572332641251748803079)
            ·
              refine ⟨13103358498961877623204619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735572332641251748803079 13103358498961877623204619)
              ·
                refine ⟨19655037748442816434806929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13103358498961877623204619 19655037748442816434806929)
                ·
                  refine ⟨14741278311332112326105197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19655037748442816434806929 14741278311332112326105197)
                  ·
                    refine ⟨5527979366749542122289449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14741278311332112326105197 5527979366749542122289449)
                    ·
                      refine ⟨4145984525062156591717087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5527979366749542122289449 4145984525062156591717087)
                      ·
                        rfl

theorem cell23_8074276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_8074276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074276 prefixEnd_8074276 := by exact prefixLift 8074276
  have htrace : WordTrace (prefixWord ++ tailWord_8074276) baseStart_8074276 baseEnd_8074276 := by
    simpa [prefixWord, tailWord_8074276, baseEnd_8074276] using wordTrace_append hprefix tailTrace_8074276
  have hstable : (prefixWord ++ tailWord_8074276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074276).length < 2 ^ (prefixWord ++ tailWord_8074276).sum := by decide
  have hdescent : baseEnd_8074276 < baseStart_8074276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074357 : List Nat := [1, 3, 4, 3, 1, 1, 3, 2, 1, 2, 2]
def baseStart_8074357 : Nat := 118140960795 + 8074357 * 2 ^ 59
def prefixEnd_8074357 : Nat := 4983230072969 + 3 ^ 40 * 8074357 * 2
def baseEnd_8074357 : Nat := 4146026116995170774804215

theorem tailTrace_8074357 : CollatzResearch.WordTrace tailWord_8074357 prefixEnd_8074357 4146026116995170774804215 := by
  unfold tailWord_8074357
  simp only [CollatzResearch.WordTrace]
  refine ⟨294495993608991054233677325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196330662405994036155784883 294495993608991054233677325)
  ·
    refine ⟨110435997603371645337628997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294495993608991054233677325 110435997603371645337628997)
    ·
      refine ⟨20706749550632183500805437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110435997603371645337628997 20706749550632183500805437)
      ·
        refine ⟨7765031081487068812802039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20706749550632183500805437 7765031081487068812802039)
        ·
          refine ⟨11647546622230603219203059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765031081487068812802039 11647546622230603219203059)
          ·
            refine ⟨17471319933345904828804589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11647546622230603219203059 17471319933345904828804589)
            ·
              refine ⟨6551744975004714310801721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17471319933345904828804589 6551744975004714310801721)
              ·
                refine ⟨4913808731253535733101291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6551744975004714310801721 4913808731253535733101291)
                ·
                  refine ⟨7370713096880303599651937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913808731253535733101291 7370713096880303599651937)
                  ·
                    refine ⟨5528034822660227699738953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7370713096880303599651937 5528034822660227699738953)
                    ·
                      refine ⟨4146026116995170774804215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528034822660227699738953 4146026116995170774804215)
                      ·
                        rfl

theorem cell23_8074357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_8074357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074357 prefixEnd_8074357 := by exact prefixLift 8074357
  have htrace : WordTrace (prefixWord ++ tailWord_8074357) baseStart_8074357 baseEnd_8074357 := by
    simpa [prefixWord, tailWord_8074357, baseEnd_8074357] using wordTrace_append hprefix tailTrace_8074357
  have hstable : (prefixWord ++ tailWord_8074357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074357).length < 2 ^ (prefixWord ++ tailWord_8074357).sum := by decide
  have hdescent : baseEnd_8074357 < baseStart_8074357 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074365 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 5]
def baseStart_8074365 : Nat := 118140960795 + 8074365 * 2 ^ 59
def prefixEnd_8074365 : Nat := 4983230072969 + 3 ^ 40 * 8074365 * 2
def baseEnd_8074365 : Nat := 4146030224840406743504177

theorem tailTrace_8074365 : CollatzResearch.WordTrace tailWord_8074365 prefixEnd_8074365 4146030224840406743504177 := by
  unfold tailWord_8074365
  simp only [CollatzResearch.WordTrace]
  refine ⟨294496285392962071599968549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196330856928641381066645699 294496285392962071599968549)
  ·
    refine ⟨55218053511180388424994103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294496285392962071599968549 55218053511180388424994103)
    ·
      refine ⟨82827080266770582637491155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55218053511180388424994103 82827080266770582637491155)
      ·
        refine ⟨124240620400155873956236733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82827080266770582637491155 124240620400155873956236733)
        ·
          refine ⟨46590232650058452733588775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124240620400155873956236733 46590232650058452733588775)
          ·
            refine ⟨69885348975087679100383163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46590232650058452733588775 69885348975087679100383163)
            ·
              refine ⟨104828023462631518650574745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69885348975087679100383163 104828023462631518650574745)
              ·
                refine ⟨78621017596973638987931059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104828023462631518650574745 78621017596973638987931059)
                ·
                  refine ⟨117931526395460458481896589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78621017596973638987931059 117931526395460458481896589)
                  ·
                    refine ⟨44224322398297671930711221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117931526395460458481896589 44224322398297671930711221)
                    ·
                      refine ⟨4146030224840406743504177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44224322398297671930711221 4146030224840406743504177)
                      ·
                        rfl

theorem cell23_8074365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_8074365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074365 prefixEnd_8074365 := by exact prefixLift 8074365
  have htrace : WordTrace (prefixWord ++ tailWord_8074365) baseStart_8074365 baseEnd_8074365 := by
    simpa [prefixWord, tailWord_8074365, baseEnd_8074365] using wordTrace_append hprefix tailTrace_8074365
  have hstable : (prefixWord ++ tailWord_8074365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074365).length < 2 ^ (prefixWord ++ tailWord_8074365).sum := by decide
  have hdescent : baseEnd_8074365 < baseStart_8074365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074373 : List Nat := [1, 3, 1, 1, 6, 2, 2, 1, 2, 1, 3]
def baseStart_8074373 : Nat := 118140960795 + 8074373 * 2 ^ 59
def prefixEnd_8074373 : Nat := 4983230072969 + 3 ^ 40 * 8074373 * 2
def baseEnd_8074373 : Nat := 4146034332685642712204141

theorem tailTrace_8074373 : CollatzResearch.WordTrace tailWord_8074373 prefixEnd_8074373 4146034332685642712204141 := by
  unfold tailWord_8074373
  simp only [CollatzResearch.WordTrace]
  refine ⟨294496577176933088966259773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196331051451288725977506515 294496577176933088966259773)
  ·
    refine ⟨110436216441349908362347415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294496577176933088966259773 110436216441349908362347415)
    ·
      refine ⟨165654324662024862543521123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110436216441349908362347415 165654324662024862543521123)
      ·
        refine ⟨248481486993037293815281685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165654324662024862543521123 248481486993037293815281685)
        ·
          refine ⟨11647569702798623147591329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248481486993037293815281685 11647569702798623147591329)
          ·
            refine ⟨8735677277098967360693497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11647569702798623147591329 8735677277098967360693497)
            ·
              refine ⟨6551757957824225520520123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8735677277098967360693497 6551757957824225520520123)
              ·
                refine ⟨9827636936736338280780185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551757957824225520520123 9827636936736338280780185)
                ·
                  refine ⟨7370727702552253710585139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9827636936736338280780185 7370727702552253710585139)
                  ·
                    refine ⟨11056091553828380565877709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7370727702552253710585139 11056091553828380565877709)
                    ·
                      refine ⟨4146034332685642712204141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11056091553828380565877709 4146034332685642712204141)
                      ·
                        rfl

theorem cell23_8074373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 2, 1, 3].length) (baseStart_8074373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074373 prefixEnd_8074373 := by exact prefixLift 8074373
  have htrace : WordTrace (prefixWord ++ tailWord_8074373) baseStart_8074373 baseEnd_8074373 := by
    simpa [prefixWord, tailWord_8074373, baseEnd_8074373] using wordTrace_append hprefix tailTrace_8074373
  have hstable : (prefixWord ++ tailWord_8074373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074373).length < 2 ^ (prefixWord ++ tailWord_8074373).sum := by decide
  have hdescent : baseEnd_8074373 < baseStart_8074373 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074375 : List Nat := [1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_8074375 : Nat := 118140960795 + 8074375 * 2 ^ 59
def prefixEnd_8074375 : Nat := 4983230072969 + 3 ^ 40 * 8074375 * 2
def baseEnd_8074375 : Nat := 4146035359646951704379131

theorem tailTrace_8074375 : CollatzResearch.WordTrace tailWord_8074375 prefixEnd_8074375 4146035359646951704379131 := by
  unfold tailWord_8074375
  simp only [CollatzResearch.WordTrace]
  refine ⟨294496650122925843307832579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196331100081950562205221719 294496650122925843307832579)
  ·
    refine ⟨441744975184388764961748869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294496650122925843307832579 441744975184388764961748869)
    ·
      refine ⟨82827182847072893430327913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441744975184388764961748869 82827182847072893430327913)
      ·
        refine ⟨62120387135304670072745935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82827182847072893430327913 62120387135304670072745935)
        ·
          refine ⟨93180580702957005109118903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62120387135304670072745935 93180580702957005109118903)
          ·
            refine ⟨139770871054435507663678355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93180580702957005109118903 139770871054435507663678355)
            ·
              refine ⟨209656306581653261495517533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139770871054435507663678355 209656306581653261495517533)
              ·
                refine ⟨78621114968119973060819075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209656306581653261495517533 78621114968119973060819075)
                ·
                  refine ⟨117931672452179959591228613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78621114968119973060819075 117931672452179959591228613)
                  ·
                    refine ⟨22112188584783742423355365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117931672452179959591228613 22112188584783742423355365)
                    ·
                      refine ⟨4146035359646951704379131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22112188584783742423355365 4146035359646951704379131)
                      ·
                        rfl

theorem cell23_8074375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_8074375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074375 prefixEnd_8074375 := by exact prefixLift 8074375
  have htrace : WordTrace (prefixWord ++ tailWord_8074375) baseStart_8074375 baseEnd_8074375 := by
    simpa [prefixWord, tailWord_8074375, baseEnd_8074375] using wordTrace_append hprefix tailTrace_8074375
  have hstable : (prefixWord ++ tailWord_8074375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074375).length < 2 ^ (prefixWord ++ tailWord_8074375).sum := by decide
  have hdescent : baseEnd_8074375 < baseStart_8074375 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074382 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_8074382 : Nat := 118140960795 + 8074382 * 2 ^ 59
def prefixEnd_8074382 : Nat := 4983230072969 + 3 ^ 40 * 8074382 * 2
def baseEnd_8074382 : Nat := 4146038954011533176991599

theorem tailTrace_8074382 : CollatzResearch.WordTrace tailWord_8074382 prefixEnd_8074382 4146038954011533176991599 := by
  unfold tailWord_8074382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36812113179237560437917175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196331270289266989002224933 36812113179237560437917175)
  ·
    refine ⟨55218169768856340656875763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36812113179237560437917175 55218169768856340656875763)
    ·
      refine ⟨82827254653284510985313645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55218169768856340656875763 82827254653284510985313645)
      ·
        refine ⟨31060220494981691619492617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82827254653284510985313645 31060220494981691619492617)
        ·
          refine ⟨23295165371236268714619463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31060220494981691619492617 23295165371236268714619463)
          ·
            refine ⟨34942748056854403071929195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23295165371236268714619463 34942748056854403071929195)
            ·
              refine ⟨52414122085281604607893793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34942748056854403071929195 52414122085281604607893793)
              ·
                refine ⟨39310591563961203455920345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52414122085281604607893793 39310591563961203455920345)
                ·
                  refine ⟨29482943672970902591940259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39310591563961203455920345 29482943672970902591940259)
                  ·
                    refine ⟨44224415509456353887910389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29482943672970902591940259 44224415509456353887910389)
                    ·
                      refine ⟨4146038954011533176991599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44224415509456353887910389 4146038954011533176991599)
                      ·
                        rfl

theorem cell23_8074382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_8074382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074382 prefixEnd_8074382 := by exact prefixLift 8074382
  have htrace : WordTrace (prefixWord ++ tailWord_8074382) baseStart_8074382 baseEnd_8074382 := by
    simpa [prefixWord, tailWord_8074382, baseEnd_8074382] using wordTrace_append hprefix tailTrace_8074382
  have hstable : (prefixWord ++ tailWord_8074382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074382).length < 2 ^ (prefixWord ++ tailWord_8074382).sum := by decide
  have hdescent : baseEnd_8074382 < baseStart_8074382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074419 : List Nat := [1, 1, 1, 2, 3, 2, 6, 2, 5]
def baseStart_8074419 : Nat := 118140960795 + 8074419 * 2 ^ 59
def prefixEnd_8074419 : Nat := 4983230072969 + 3 ^ 40 * 8074419 * 2
def baseEnd_8074419 : Nat := 460673105866194392469881

theorem tailTrace_8074419 : CollatzResearch.WordTrace tailWord_8074419 prefixEnd_8074419 460673105866194392469881 := by
  unfold tailWord_8074419
  simp only [CollatzResearch.WordTrace]
  refine ⟨294498254934766438822434311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196332169956510959214956207 294498254934766438822434311)
  ·
    refine ⟨441747382402149658233651467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294498254934766438822434311 441747382402149658233651467)
    ·
      refine ⟨662621073603224487350477201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441747382402149658233651467 662621073603224487350477201)
      ·
        refine ⟨496965805202418365512857901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662621073603224487350477201 496965805202418365512857901)
        ·
          refine ⟨186362176950906887067321713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496965805202418365512857901 186362176950906887067321713)
          ·
            refine ⟨139771632713180165300491285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186362176950906887067321713 139771632713180165300491285)
            ·
              refine ⟨6551795283430320248460529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139771632713180165300491285 6551795283430320248460529)
              ·
                refine ⟨4913846462572740186345397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6551795283430320248460529 4913846462572740186345397)
                ·
                  refine ⟨460673105866194392469881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4913846462572740186345397 460673105866194392469881)
                  ·
                    rfl

theorem cell23_8074419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 2, 5].length) (baseStart_8074419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074419 prefixEnd_8074419 := by exact prefixLift 8074419
  have htrace : WordTrace (prefixWord ++ tailWord_8074419) baseStart_8074419 baseEnd_8074419 := by
    simpa [prefixWord, tailWord_8074419, baseEnd_8074419] using wordTrace_append hprefix tailTrace_8074419
  have hstable : (prefixWord ++ tailWord_8074419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074419).length < 2 ^ (prefixWord ++ tailWord_8074419).sum := by decide
  have hdescent : baseEnd_8074419 < baseStart_8074419 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074530 : List Nat := [3, 3, 1, 1, 4, 1, 3, 2, 1, 4]
def baseStart_8074530 : Nat := 118140960795 + 8074530 * 2 ^ 59
def prefixEnd_8074530 : Nat := 4983230072969 + 3 ^ 40 * 8074530 * 2
def baseEnd_8074530 : Nat := 1382038316382799532646973

theorem tailTrace_8074530 : CollatzResearch.WordTrace tailWord_8074530 prefixEnd_8074530 1382038316382799532646973 := by
  unfold tailWord_8074530
  simp only [CollatzResearch.WordTrace]
  refine ⟨73625575859341076194931261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196334868958242869853150029 73625575859341076194931261)
  ·
    refine ⟨27609590947252903573099223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73625575859341076194931261 27609590947252903573099223)
    ·
      refine ⟨41414386420879355359648835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27609590947252903573099223 41414386420879355359648835)
      ·
        refine ⟨62121579631319033039473253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41414386420879355359648835 62121579631319033039473253)
        ·
          refine ⟨11647796180872318694901235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62121579631319033039473253 11647796180872318694901235)
          ·
            refine ⟨17471694271308478042351853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11647796180872318694901235 17471694271308478042351853)
            ·
              refine ⟨6551885351740679265881945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17471694271308478042351853 6551885351740679265881945)
              ·
                refine ⟨4913914013805509449411459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6551885351740679265881945 4913914013805509449411459)
                ·
                  refine ⟨7370871020708264174117189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4913914013805509449411459 7370871020708264174117189)
                  ·
                    refine ⟨1382038316382799532646973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7370871020708264174117189 1382038316382799532646973)
                    ·
                      rfl

theorem cell23_8074530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_8074530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074530 prefixEnd_8074530 := by exact prefixLift 8074530
  have htrace : WordTrace (prefixWord ++ tailWord_8074530) baseStart_8074530 baseEnd_8074530 := by
    simpa [prefixWord, tailWord_8074530, baseEnd_8074530] using wordTrace_append hprefix tailTrace_8074530
  have hstable : (prefixWord ++ tailWord_8074530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074530).length < 2 ^ (prefixWord ++ tailWord_8074530).sum := by decide
  have hdescent : baseEnd_8074530 < baseStart_8074530 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074552 : List Nat := [2, 1, 2, 1, 3, 1, 1, 5, 1, 6]
def baseStart_8074552 : Nat := 118140960795 + 8074552 * 2 ^ 59
def prefixEnd_8074552 : Nat := 4983230072969 + 3 ^ 40 * 8074552 * 2
def baseEnd_8074552 : Nat := 1382042081907599170621939

theorem tailTrace_8074552 : CollatzResearch.WordTrace tailWord_8074552 prefixEnd_8074552 1382042081907599170621939 := by
  unfold tailWord_8074552
  simp only [CollatzResearch.WordTrace]
  refine ⟨147251552921642301268512955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196335403895523068358017273 147251552921642301268512955)
  ·
    refine ⟨220877329382463451902769433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147251552921642301268512955 220877329382463451902769433)
    ·
      refine ⟨165657997036847588927077075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220877329382463451902769433 165657997036847588927077075)
      ·
        refine ⟨248486995555271383390615613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165657997036847588927077075 248486995555271383390615613)
        ·
          refine ⟨93182623333226768771480855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248486995555271383390615613 93182623333226768771480855)
          ·
            refine ⟨139773934999840153157221283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93182623333226768771480855 139773934999840153157221283)
            ·
              refine ⟨209660902499760229735831925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139773934999840153157221283 209660902499760229735831925)
              ·
                refine ⟨19655709609352521537734243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209660902499760229735831925 19655709609352521537734243)
                ·
                  refine ⟨29483564414028782306601365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19655709609352521537734243 29483564414028782306601365)
                  ·
                    refine ⟨1382042081907599170621939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29483564414028782306601365 1382042081907599170621939)
                    ·
                      rfl

theorem cell23_8074552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_8074552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074552 prefixEnd_8074552 := by exact prefixLift 8074552
  have htrace : WordTrace (prefixWord ++ tailWord_8074552) baseStart_8074552 baseEnd_8074552 := by
    simpa [prefixWord, tailWord_8074552, baseEnd_8074552] using wordTrace_append hprefix tailTrace_8074552
  have hstable : (prefixWord ++ tailWord_8074552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074552).length < 2 ^ (prefixWord ++ tailWord_8074552).sum := by decide
  have hdescent : baseEnd_8074552 < baseStart_8074552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074556 : List Nat := [2, 2, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_8074556 : Nat := 118140960795 + 8074556 * 2 ^ 59
def prefixEnd_8074556 : Nat := 4983230072969 + 3 ^ 40 * 8074556 * 2
def baseEnd_8074556 : Nat := 1382042766548471832071933

theorem tailTrace_8074556 : CollatzResearch.WordTrace tailWord_8074556 prefixEnd_8074556 1382042766548471832071933 := by
  unfold tailWord_8074556
  simp only [CollatzResearch.WordTrace]
  refine ⟨147251625867635055610085761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196335501156846740813447681 147251625867635055610085761)
  ·
    refine ⟨110438719400726291707564321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147251625867635055610085761 110438719400726291707564321)
    ·
      refine ⟨82829039550544718780673241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110438719400726291707564321 82829039550544718780673241)
      ·
        refine ⟨62121779662908539085504931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82829039550544718780673241 62121779662908539085504931)
        ·
          refine ⟨93182669494362808628257397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62121779662908539085504931 93182669494362808628257397)
          ·
            refine ⟨8735875265096513308899131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93182669494362808628257397 8735875265096513308899131)
            ·
              refine ⟨13103812897644769963348697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8735875265096513308899131 13103812897644769963348697)
              ·
                refine ⟨9827859673233577472511523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13103812897644769963348697 9827859673233577472511523)
                ·
                  refine ⟨14741789509850366208767285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9827859673233577472511523 14741789509850366208767285)
                  ·
                    refine ⟨1382042766548471832071933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14741789509850366208767285 1382042766548471832071933)
                    ·
                      rfl

theorem cell23_8074556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_8074556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074556 prefixEnd_8074556 := by exact prefixLift 8074556
  have htrace : WordTrace (prefixWord ++ tailWord_8074556) baseStart_8074556 baseEnd_8074556 := by
    simpa [prefixWord, tailWord_8074556, baseEnd_8074556] using wordTrace_append hprefix tailTrace_8074556
  have hstable : (prefixWord ++ tailWord_8074556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074556).length < 2 ^ (prefixWord ++ tailWord_8074556).sum := by decide
  have hdescent : baseEnd_8074556 < baseStart_8074556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074559 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_8074559 : Nat := 118140960795 + 8074559 * 2 ^ 59
def prefixEnd_8074559 : Nat := 4983230072969 + 3 ^ 40 * 8074559 * 2
def baseEnd_8074559 : Nat := 4146129840087378984478285

theorem tailTrace_8074559 : CollatzResearch.WordTrace tailWord_8074559 prefixEnd_8074559 4146129840087378984478285 := by
  unfold tailWord_8074559
  simp only [CollatzResearch.WordTrace]
  refine ⟨294503361154259242732530731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196335574102839495155020487 294503361154259242732530731)
  ·
    refine ⟨441755041731388864098796097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294503361154259242732530731 441755041731388864098796097)
    ·
      refine ⟨331316281298541648074097073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441755041731388864098796097 331316281298541648074097073)
      ·
        refine ⟨248487210973906236055572805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331316281298541648074097073 248487210973906236055572805)
        ·
          refine ⟨46591352057607419260419901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248487210973906236055572805 46591352057607419260419901)
          ·
            refine ⟨17471757021602782222657463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46591352057607419260419901 17471757021602782222657463)
            ·
              refine ⟨26207635532404173333986195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17471757021602782222657463 26207635532404173333986195)
              ·
                refine ⟨39311453298606260000979293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26207635532404173333986195 39311453298606260000979293)
                ·
                  refine ⟨14741794986977347500367235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39311453298606260000979293 14741794986977347500367235)
                  ·
                    refine ⟨22112692480466021250550853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14741794986977347500367235 22112692480466021250550853)
                    ·
                      refine ⟨4146129840087378984478285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22112692480466021250550853 4146129840087378984478285)
                      ·
                        rfl

theorem cell23_8074559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_8074559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074559 prefixEnd_8074559 := by exact prefixLift 8074559
  have htrace : WordTrace (prefixWord ++ tailWord_8074559) baseStart_8074559 baseEnd_8074559 := by
    simpa [prefixWord, tailWord_8074559, baseEnd_8074559] using wordTrace_append hprefix tailTrace_8074559
  have hstable : (prefixWord ++ tailWord_8074559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074559).length < 2 ^ (prefixWord ++ tailWord_8074559).sum := by decide
  have hdescent : baseEnd_8074559 < baseStart_8074559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074576 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 1, 1, 4]
def baseStart_8074576 : Nat := 118140960795 + 8074576 * 2 ^ 59
def prefixEnd_8074576 : Nat := 4983230072969 + 3 ^ 40 * 8074576 * 2
def baseEnd_8074576 : Nat := 4146138569258505417965707

theorem tailTrace_8074576 : CollatzResearch.WordTrace tailWord_8074576 prefixEnd_8074576 4146138569258505417965707 := by
  unfold tailWord_8074576
  simp only [CollatzResearch.WordTrace]
  refine ⟨147251990597598827317949791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196335987463465103090599721 147251990597598827317949791)
  ·
    refine ⟨220877985896398240976924687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147251990597598827317949791 220877985896398240976924687)
    ·
      refine ⟨331316978844597361465387031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220877985896398240976924687 331316978844597361465387031)
      ·
        refine ⟨496975468266896042198080547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331316978844597361465387031 496975468266896042198080547)
        ·
          refine ⟨745463202400344063297120821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496975468266896042198080547 745463202400344063297120821)
          ·
            refine ⟨69887175225032255934105077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 745463202400344063297120821 69887175225032255934105077)
            ·
              refine ⟨6551922677346773993822351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69887175225032255934105077 6551922677346773993822351)
              ·
                refine ⟨9827884016020160990733527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6551922677346773993822351 9827884016020160990733527)
                ·
                  refine ⟨14741826024030241486100291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9827884016020160990733527 14741826024030241486100291)
                  ·
                    refine ⟨22112739036045362229150437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14741826024030241486100291 22112739036045362229150437)
                    ·
                      refine ⟨4146138569258505417965707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22112739036045362229150437 4146138569258505417965707)
                      ·
                        rfl

theorem cell23_8074576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 1, 1, 4].length) (baseStart_8074576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074576 prefixEnd_8074576 := by exact prefixLift 8074576
  have htrace : WordTrace (prefixWord ++ tailWord_8074576) baseStart_8074576 baseEnd_8074576 := by
    simpa [prefixWord, tailWord_8074576, baseEnd_8074576] using wordTrace_append hprefix tailTrace_8074576
  have hstable : (prefixWord ++ tailWord_8074576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074576).length < 2 ^ (prefixWord ++ tailWord_8074576).sum := by decide
  have hdescent : baseEnd_8074576 < baseStart_8074576 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074609 : List Nat := [1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_8074609 : Nat := 118140960795 + 8074609 * 2 ^ 59
def prefixEnd_8074609 : Nat := 4983230072969 + 3 ^ 40 * 8074609 * 2
def baseEnd_8074609 : Nat := 4146155514120103788853055

theorem tailTrace_8074609 : CollatzResearch.WordTrace tailWord_8074609 prefixEnd_8074609 4146155514120103788853055 := by
  unfold tailWord_8074609
  simp only [CollatzResearch.WordTrace]
  refine ⟨294505184804078101271850881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196336789869385400847900587 294505184804078101271850881)
  ·
    refine ⟨220878888603058575953888161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294505184804078101271850881 220878888603058575953888161)
    ·
      refine ⟨165659166452293931965416121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220878888603058575953888161 165659166452293931965416121)
      ·
        refine ⟨124244374839220448974062091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165659166452293931965416121 124244374839220448974062091)
        ·
          refine ⟨186366562258830673461093137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124244374839220448974062091 186366562258830673461093137)
          ·
            refine ⟨139774921694123005095819853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186366562258830673461093137 139774921694123005095819853)
            ·
              refine ⟨52415595635296126910932445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139774921694123005095819853 52415595635296126910932445)
              ·
                refine ⟨19655848363236047591599667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52415595635296126910932445 19655848363236047591599667)
                ·
                  refine ⟨29483772544854071387399501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19655848363236047591599667 29483772544854071387399501)
                  ·
                    refine ⟨11056414704320276770274813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29483772544854071387399501 11056414704320276770274813)
                    ·
                      refine ⟨4146155514120103788853055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11056414704320276770274813 4146155514120103788853055)
                      ·
                        rfl

theorem cell23_8074609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_8074609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074609 prefixEnd_8074609 := by exact prefixLift 8074609
  have htrace : WordTrace (prefixWord ++ tailWord_8074609) baseStart_8074609 baseEnd_8074609 := by
    simpa [prefixWord, tailWord_8074609, baseEnd_8074609] using wordTrace_append hprefix tailTrace_8074609
  have hstable : (prefixWord ++ tailWord_8074609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074609).length < 2 ^ (prefixWord ++ tailWord_8074609).sum := by decide
  have hdescent : baseEnd_8074609 < baseStart_8074609 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074672 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 9]
def baseStart_8074672 : Nat := 118140960795 + 8074672 * 2 ^ 59
def prefixEnd_8074672 : Nat := 4983230072969 + 3 ^ 40 * 8074672 * 2
def baseEnd_8074672 : Nat := 460687540377926338040585

theorem tailTrace_8074672 : CollatzResearch.WordTrace tailWord_8074672 prefixEnd_8074672 460687540377926338040585 := by
  unfold tailWord_8074672
  simp only [CollatzResearch.WordTrace]
  refine ⟨147253741301424931515697135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196338321735233242020929513 147253741301424931515697135)
  ·
    refine ⟨220880611952137397273545703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147253741301424931515697135 220880611952137397273545703)
    ·
      refine ⟨331320917928206095910318555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220880611952137397273545703 331320917928206095910318555)
      ·
        refine ⟨496981376892309143865477833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331320917928206095910318555 496981376892309143865477833)
        ·
          refine ⟨372736032669231857899108375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496981376892309143865477833 372736032669231857899108375)
          ·
            refine ⟨559104049003847786848662563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372736032669231857899108375 559104049003847786848662563)
            ·
              refine ⟨838656073505771680272993845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559104049003847786848662563 838656073505771680272993845)
              ·
                refine ⟨78624006891166095025593173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 838656073505771680272993845 78624006891166095025593173)
                ·
                  refine ⟨460687540377926338040585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78624006891166095025593173 460687540377926338040585)
                  ·
                    rfl

theorem cell23_8074672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_8074672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074672 prefixEnd_8074672 := by exact prefixLift 8074672
  have htrace : WordTrace (prefixWord ++ tailWord_8074672) baseStart_8074672 baseEnd_8074672 := by
    simpa [prefixWord, tailWord_8074672, baseEnd_8074672] using wordTrace_append hprefix tailTrace_8074672
  have hstable : (prefixWord ++ tailWord_8074672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074672).length < 2 ^ (prefixWord ++ tailWord_8074672).sum := by decide
  have hdescent : baseEnd_8074672 < baseStart_8074672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074699 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 3]
def baseStart_8074699 : Nat := 118140960795 + 8074699 * 2 ^ 59
def prefixEnd_8074699 : Nat := 4983230072969 + 3 ^ 40 * 8074699 * 2
def baseEnd_8074699 : Nat := 4146201727379008436727641

theorem tailTrace_8074699 : CollatzResearch.WordTrace tailWord_8074699 prefixEnd_8074699 4146201727379008436727641 := by
  unfold tailWord_8074699
  simp only [CollatzResearch.WordTrace]
  refine ⟨294508467373752046642627151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196338978249168031095084767 294508467373752046642627151)
  ·
    refine ⟨441762701060628069963940727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294508467373752046642627151 441762701060628069963940727)
    ·
      refine ⟨662644051590942104945911091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441762701060628069963940727 662644051590942104945911091)
      ·
        refine ⟨993966077386413157418866637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662644051590942104945911091 993966077386413157418866637)
        ·
          refine ⟨372737279019904934032074989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 993966077386413157418866637 372737279019904934032074989)
          ·
            refine ⟨139776479632464350262028121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372737279019904934032074989 139776479632464350262028121)
            ·
              refine ⟨104832359724348262696521091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139776479632464350262028121 104832359724348262696521091)
              ·
                refine ⟨157248539586522394044781637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104832359724348262696521091 157248539586522394044781637)
                ·
                  refine ⟨29484101172472948883396557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157248539586522394044781637 29484101172472948883396557)
                  ·
                    refine ⟨11056537939677355831273709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29484101172472948883396557 11056537939677355831273709)
                    ·
                      refine ⟨4146201727379008436727641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11056537939677355831273709 4146201727379008436727641)
                      ·
                        rfl

theorem cell23_8074699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 3, 3].length) (baseStart_8074699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074699 prefixEnd_8074699 := by exact prefixLift 8074699
  have htrace : WordTrace (prefixWord ++ tailWord_8074699) baseStart_8074699 baseEnd_8074699 := by
    simpa [prefixWord, tailWord_8074699, baseEnd_8074699] using wordTrace_append hprefix tailTrace_8074699
  have hstable : (prefixWord ++ tailWord_8074699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074699).length < 2 ^ (prefixWord ++ tailWord_8074699).sum := by decide
  have hdescent : baseEnd_8074699 < baseStart_8074699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074717 : List Nat := [1, 4, 3, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_8074717 : Nat := 118140960795 + 8074717 * 2 ^ 59
def prefixEnd_8074717 : Nat := 4983230072969 + 3 ^ 40 * 8074717 * 2
def baseEnd_8074717 : Nat := 4146210970030789366302559

theorem tailTrace_8074717 : CollatzResearch.WordTrace tailWord_8074717 prefixEnd_8074717 4146210970030789366302559 := by
  unfold tailWord_8074717
  simp only [CollatzResearch.WordTrace]
  refine ⟨294509123887686835716782405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196339415925124557144521603 294509123887686835716782405)
  ·
    refine ⟨55220460728941281696896701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294509123887686835716782405 55220460728941281696896701)
    ·
      refine ⟨20707672773352980636336263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55220460728941281696896701 20707672773352980636336263)
      ·
        refine ⟨31061509160029470954504395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20707672773352980636336263 31061509160029470954504395)
        ·
          refine ⟨46592263740044206431756593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31061509160029470954504395 46592263740044206431756593)
          ·
            refine ⟨34944197805033154823817445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46592263740044206431756593 34944197805033154823817445)
            ·
              refine ⟨6552037088443716529465771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34944197805033154823817445 6552037088443716529465771)
              ·
                refine ⟨9828055632665574794198657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552037088443716529465771 9828055632665574794198657)
                ·
                  refine ⟨7371041724499181095648993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828055632665574794198657 7371041724499181095648993)
                  ·
                    refine ⟨5528281293374385821736745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371041724499181095648993 5528281293374385821736745)
                    ·
                      refine ⟨4146210970030789366302559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528281293374385821736745 4146210970030789366302559)
                      ·
                        rfl

theorem cell23_8074717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_8074717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074717 prefixEnd_8074717 := by exact prefixLift 8074717
  have htrace : WordTrace (prefixWord ++ tailWord_8074717) baseStart_8074717 baseEnd_8074717 := by
    simpa [prefixWord, tailWord_8074717, baseEnd_8074717] using wordTrace_append hprefix tailTrace_8074717
  have hstable : (prefixWord ++ tailWord_8074717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074717).length < 2 ^ (prefixWord ++ tailWord_8074717).sum := by decide
  have hdescent : baseEnd_8074717 < baseStart_8074717 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074719 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 4, 5]
def baseStart_8074719 : Nat := 118140960795 + 8074719 * 2 ^ 59
def prefixEnd_8074719 : Nat := 4983230072969 + 3 ^ 40 * 8074719 * 2
def baseEnd_8074719 : Nat := 1382070665664032786159183

theorem tailTrace_8074719 : CollatzResearch.WordTrace tailWord_8074719 prefixEnd_8074719 1382070665664032786159183 := by
  unfold tailWord_8074719
  simp only [CollatzResearch.WordTrace]
  refine ⟨294509196833679590058355211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196339464555786393372236807 294509196833679590058355211)
  ·
    refine ⟨441763795250519385087532817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294509196833679590058355211 441763795250519385087532817)
    ·
      refine ⟨331322846437889538815649613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441763795250519385087532817 331322846437889538815649613)
      ·
        refine ⟨124246067414208577055868605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331322846437889538815649613 124246067414208577055868605)
        ·
          refine ⟨46592275280328216395950727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124246067414208577055868605 46592275280328216395950727)
          ·
            refine ⟨69888412920492324593926091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46592275280328216395950727 69888412920492324593926091)
            ·
              refine ⟨104832619380738486890889137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69888412920492324593926091 104832619380738486890889137)
              ·
                refine ⟨78624464535553865168166853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104832619380738486890889137 78624464535553865168166853)
                ·
                  refine ⟨14742087100416349719031285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78624464535553865168166853 14742087100416349719031285)
                  ·
                    refine ⟨1382070665664032786159183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14742087100416349719031285 1382070665664032786159183)
                    ·
                      rfl

theorem cell23_8074719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_8074719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074719 prefixEnd_8074719 := by exact prefixLift 8074719
  have htrace : WordTrace (prefixWord ++ tailWord_8074719) baseStart_8074719 baseEnd_8074719 := by
    simpa [prefixWord, tailWord_8074719, baseEnd_8074719] using wordTrace_append hprefix tailTrace_8074719
  have hstable : (prefixWord ++ tailWord_8074719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074719).length < 2 ^ (prefixWord ++ tailWord_8074719).sum := by decide
  have hdescent : baseEnd_8074719 < baseStart_8074719 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074736 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 2, 5]
def baseStart_8074736 : Nat := 118140960795 + 8074736 * 2 ^ 59
def prefixEnd_8074736 : Nat := 4983230072969 + 3 ^ 40 * 8074736 * 2
def baseEnd_8074736 : Nat := 1382073575387741597321657

theorem tailTrace_8074736 : CollatzResearch.WordTrace tailWord_8074736 prefixEnd_8074736 1382073575387741597321657 := by
  unfold tailWord_8074736
  simp only [CollatzResearch.WordTrace]
  refine ⟨147254908437309000980862031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196339877916412001307816041 147254908437309000980862031)
  ·
    refine ⟨220882362655963501471293047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147254908437309000980862031 220882362655963501471293047)
    ·
      refine ⟨331323543983945252206939571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220882362655963501471293047 331323543983945252206939571)
      ·
        refine ⟨496985315975917878310409357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331323543983945252206939571 496985315975917878310409357)
        ·
          refine ⟨186369493490969204366403509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496985315975917878310409357 186369493490969204366403509)
          ·
            refine ⟨17472140014778362909350329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186369493490969204366403509 17472140014778362909350329)
            ·
              refine ⟨13104105011083772182012747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17472140014778362909350329 13104105011083772182012747)
              ·
                refine ⟨19656157516625658273019121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13104105011083772182012747 19656157516625658273019121)
                ·
                  refine ⟨14742118137469243704764341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19656157516625658273019121 14742118137469243704764341)
                  ·
                    refine ⟨1382073575387741597321657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14742118137469243704764341 1382073575387741597321657)
                    ·
                      rfl

theorem cell23_8074736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_8074736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074736 prefixEnd_8074736 := by exact prefixLift 8074736
  have htrace : WordTrace (prefixWord ++ tailWord_8074736) baseStart_8074736 baseEnd_8074736 := by
    simpa [prefixWord, tailWord_8074736, baseEnd_8074736] using wordTrace_append hprefix tailTrace_8074736
  have hstable : (prefixWord ++ tailWord_8074736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074736).length < 2 ^ (prefixWord ++ tailWord_8074736).sum := by decide
  have hdescent : baseEnd_8074736 < baseStart_8074736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074773 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 2, 4, 2]
def baseStart_8074773 : Nat := 118140960795 + 8074773 * 2 ^ 59
def prefixEnd_8074773 : Nat := 4983230072969 + 3 ^ 40 * 8074773 * 2
def baseEnd_8074773 : Nat := 4146239724947441147202301

theorem tailTrace_8074773 : CollatzResearch.WordTrace tailWord_8074773 prefixEnd_8074773 4146239724947441147202301 := by
  unfold tailWord_8074773
  simp only [CollatzResearch.WordTrace]
  refine ⟨294511166375483957280820973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196340777583655971520547315 294511166375483957280820973)
  ·
    refine ⟨110441687390806483980307865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294511166375483957280820973 110441687390806483980307865)
    ·
      refine ⟨82831265543104862985230899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110441687390806483980307865 82831265543104862985230899)
      ·
        refine ⟨124246898314657294477846349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82831265543104862985230899 124246898314657294477846349)
        ·
          refine ⟨46592586867996485429192381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124246898314657294477846349 46592586867996485429192381)
          ·
            refine ⟨17472220075498682035947143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46592586867996485429192381 17472220075498682035947143)
            ·
              refine ⟨26208330113248023053920715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17472220075498682035947143 26208330113248023053920715)
              ·
                refine ⟨39312495169872034580881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26208330113248023053920715 39312495169872034580881073)
                ·
                  refine ⟨29484371377404025935660805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39312495169872034580881073 29484371377404025935660805)
                  ·
                    refine ⟨5528319633263254862936401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29484371377404025935660805 5528319633263254862936401)
                    ·
                      refine ⟨4146239724947441147202301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528319633263254862936401 4146239724947441147202301)
                      ·
                        rfl

theorem cell23_8074773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 2, 4, 2].length) (baseStart_8074773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074773 prefixEnd_8074773 := by exact prefixLift 8074773
  have htrace : WordTrace (prefixWord ++ tailWord_8074773) baseStart_8074773 baseEnd_8074773 := by
    simpa [prefixWord, tailWord_8074773, baseEnd_8074773] using wordTrace_append hprefix tailTrace_8074773
  have hstable : (prefixWord ++ tailWord_8074773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074773).length < 2 ^ (prefixWord ++ tailWord_8074773).sum := by decide
  have hdescent : baseEnd_8074773 < baseStart_8074773 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074873 : List Nat := [1, 2, 1, 3, 3, 1, 2, 4, 2, 4]
def baseStart_8074873 : Nat := 118140960795 + 8074873 * 2 ^ 59
def prefixEnd_8074873 : Nat := 4983230072969 + 3 ^ 40 * 8074873 * 2
def baseEnd_8074873 : Nat := 1382097024337630251983947

theorem tailTrace_8074873 : CollatzResearch.WordTrace tailWord_8074873 prefixEnd_8074873 1382097024337630251983947 := by
  unfold tailWord_8074873
  simp only [CollatzResearch.WordTrace]
  refine ⟨294514813675121674359461273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196343209116747782906307515 294514813675121674359461273)
  ·
    refine ⟨220886110256341255769595955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294514813675121674359461273 220886110256341255769595955)
    ·
      refine ⟨331329165384511883654393933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220886110256341255769595955 331329165384511883654393933)
      ·
        refine ⟨124248437019191956370397725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331329165384511883654393933 124248437019191956370397725)
        ·
          refine ⟨46593163882196983638899147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124248437019191956370397725 46593163882196983638899147)
          ·
            refine ⟨69889745823295475458348721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46593163882196983638899147 69889745823295475458348721)
            ·
              refine ⟨52417309367471606593761541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69889745823295475458348721 52417309367471606593761541)
              ·
                refine ⟨9828245506400926236330289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52417309367471606593761541 9828245506400926236330289)
                ·
                  refine ⟨7371184129800694677247717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828245506400926236330289 7371184129800694677247717)
                  ·
                    refine ⟨1382097024337630251983947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371184129800694677247717 1382097024337630251983947)
                    ·
                      rfl

theorem cell23_8074873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 4].length) (baseStart_8074873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074873 prefixEnd_8074873 := by exact prefixLift 8074873
  have htrace : WordTrace (prefixWord ++ tailWord_8074873) baseStart_8074873 baseEnd_8074873 := by
    simpa [prefixWord, tailWord_8074873, baseEnd_8074873] using wordTrace_append hprefix tailTrace_8074873
  have hstable : (prefixWord ++ tailWord_8074873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074873).length < 2 ^ (prefixWord ++ tailWord_8074873).sum := by decide
  have hdescent : baseEnd_8074873 < baseStart_8074873 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074890 : List Nat := [3, 1, 2, 3, 2, 2, 1, 3, 2, 4]
def baseStart_8074890 : Nat := 118140960795 + 8074890 * 2 ^ 59
def prefixEnd_8074890 : Nat := 4983230072969 + 3 ^ 40 * 8074890 * 2
def baseEnd_8074890 : Nat := 1382099934061339063146421

theorem tailTrace_8074890 : CollatzResearch.WordTrace tailWord_8074890 prefixEnd_8074890 1382099934061339063146421 := by
  unfold tailWord_8074890
  simp only [CollatzResearch.WordTrace]
  refine ⟨73628858429015021565707531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196343622477373390841886749 73628858429015021565707531)
  ·
    refine ⟨110443287643522532348561297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73628858429015021565707531 110443287643522532348561297)
    ·
      refine ⟨82832465732641899261420973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110443287643522532348561297 82832465732641899261420973)
      ·
        refine ⟨31062174649740712223032865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82832465732641899261420973 31062174649740712223032865)
        ·
          refine ⟨23296630987305534167274649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31062174649740712223032865 23296630987305534167274649)
          ·
            refine ⟨17472473240479150625455987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23296630987305534167274649 17472473240479150625455987)
            ·
              refine ⟨26208709860718725938183981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17472473240479150625455987 26208709860718725938183981)
              ·
                refine ⟨9828266197769522226818993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26208709860718725938183981 9828266197769522226818993)
                ·
                  refine ⟨7371199648327141670114245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828266197769522226818993 7371199648327141670114245)
                  ·
                    refine ⟨1382099934061339063146421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371199648327141670114245 1382099934061339063146421)
                    ·
                      rfl

theorem cell23_8074890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 3, 2, 4].length) (baseStart_8074890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074890 prefixEnd_8074890 := by exact prefixLift 8074890
  have htrace : WordTrace (prefixWord ++ tailWord_8074890) baseStart_8074890 baseEnd_8074890 := by
    simpa [prefixWord, tailWord_8074890, baseEnd_8074890] using wordTrace_append hprefix tailTrace_8074890
  have hstable : (prefixWord ++ tailWord_8074890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074890).length < 2 ^ (prefixWord ++ tailWord_8074890).sum := by decide
  have hdescent : baseEnd_8074890 < baseStart_8074890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074896 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_8074896 : Nat := 118140960795 + 8074896 * 2 ^ 59
def prefixEnd_8074896 : Nat := 4983230072969 + 3 ^ 40 * 8074896 * 2
def baseEnd_8074896 : Nat := 4146302883067944165964235

theorem tailTrace_8074896 : CollatzResearch.WordTrace tailWord_8074896 prefixEnd_8074896 4146302883067944165964235 := by
  unfold tailWord_8074896
  simp only [CollatzResearch.WordTrace]
  refine ⟨147257826277019174643774271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196343768369358899525032361 147257826277019174643774271)
  ·
    refine ⟨220886739415528761965661407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147257826277019174643774271 220886739415528761965661407)
    ·
      refine ⟨331330109123293142948492111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220886739415528761965661407 331330109123293142948492111)
      ·
        refine ⟨496995163684939714422738167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331330109123293142948492111 496995163684939714422738167)
        ·
          refine ⟨745492745527409571634107251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496995163684939714422738167 745492745527409571634107251)
          ·
            refine ⟨1118239118291114357451160877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745492745527409571634107251 1118239118291114357451160877)
            ·
              refine ⟨419339669359167884044185329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1118239118291114357451160877 419339669359167884044185329)
              ·
                refine ⟨314504752019375913033138997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419339669359167884044185329 314504752019375913033138997)
                ·
                  refine ⟨29484820501816491846856781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314504752019375913033138997 29484820501816491846856781)
                  ·
                    refine ⟨11056807688181184442571293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29484820501816491846856781 11056807688181184442571293)
                    ·
                      refine ⟨4146302883067944165964235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11056807688181184442571293 4146302883067944165964235)
                      ·
                        rfl

theorem cell23_8074896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_8074896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074896 prefixEnd_8074896 := by exact prefixLift 8074896
  have htrace : WordTrace (prefixWord ++ tailWord_8074896) baseStart_8074896 baseEnd_8074896 := by
    simpa [prefixWord, tailWord_8074896, baseEnd_8074896] using wordTrace_append hprefix tailTrace_8074896
  have hstable : (prefixWord ++ tailWord_8074896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074896).length < 2 ^ (prefixWord ++ tailWord_8074896).sum := by decide
  have hdescent : baseEnd_8074896 < baseStart_8074896 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074910 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_8074910 : Nat := 118140960795 + 8074910 * 2 ^ 59
def prefixEnd_8074910 : Nat := 4983230072969 + 3 ^ 40 * 8074910 * 2
def baseEnd_8074910 : Nat := 4146310071797107111189171

theorem tailTrace_8074910 : CollatzResearch.WordTrace tailWord_8074910 prefixEnd_8074910 4146310071797107111189171 := by
  unfold tailWord_8074910
  simp only [CollatzResearch.WordTrace]
  refine ⟨36814520396998453709819773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196344108783991753119038789 36814520396998453709819773)
  ·
    refine ⟨13805445148874420141182415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36814520396998453709819773 13805445148874420141182415)
    ·
      refine ⟨20708167723311630211773623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13805445148874420141182415 20708167723311630211773623)
      ·
        refine ⟨31062251584967445317660435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20708167723311630211773623 31062251584967445317660435)
        ·
          refine ⟨46593377377451167976490653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31062251584967445317660435 46593377377451167976490653)
          ·
            refine ⟨17472516516544187991183995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46593377377451167976490653 17472516516544187991183995)
            ·
              refine ⟨26208774774816281986775993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17472516516544187991183995 26208774774816281986775993)
              ·
                refine ⟨19656581081112211490081995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26208774774816281986775993 19656581081112211490081995)
                ·
                  refine ⟨29484871621668317235122993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19656581081112211490081995 29484871621668317235122993)
                  ·
                    refine ⟨22113653716251237926342245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29484871621668317235122993 22113653716251237926342245)
                    ·
                      refine ⟨4146310071797107111189171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22113653716251237926342245 4146310071797107111189171)
                      ·
                        rfl

theorem cell23_8074910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_8074910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074910 prefixEnd_8074910 := by exact prefixLift 8074910
  have htrace : WordTrace (prefixWord ++ tailWord_8074910) baseStart_8074910 baseEnd_8074910 := by
    simpa [prefixWord, tailWord_8074910, baseEnd_8074910] using wordTrace_append hprefix tailTrace_8074910
  have hstable : (prefixWord ++ tailWord_8074910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074910).length < 2 ^ (prefixWord ++ tailWord_8074910).sum := by decide
  have hdescent : baseEnd_8074910 < baseStart_8074910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074913 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_8074913 : Nat := 118140960795 + 8074913 * 2 ^ 59
def prefixEnd_8074913 : Nat := 4983230072969 + 3 ^ 40 * 8074913 * 2
def baseEnd_8074913 : Nat := 4146311612239070599451657

theorem tailTrace_8074913 : CollatzResearch.WordTrace tailWord_8074913 prefixEnd_8074913 4146311612239070599451657 := by
  unfold tailWord_8074913
  simp only [CollatzResearch.WordTrace]
  refine ⟨294516272594976761190917393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196344181729984507460611595 294516272594976761190917393)
  ·
    refine ⟨220887204446232570893188045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294516272594976761190917393 220887204446232570893188045)
    ·
      refine ⟨82832701667337214084945517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220887204446232570893188045 82832701667337214084945517)
      ·
        refine ⟨31062263125251455281854569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82832701667337214084945517 31062263125251455281854569)
        ·
          refine ⟨23296697343938591461390927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31062263125251455281854569 23296697343938591461390927)
          ·
            refine ⟨34945046015907887192086391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23296697343938591461390927 34945046015907887192086391)
            ·
              refine ⟨52417569023861830788129587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34945046015907887192086391 52417569023861830788129587)
              ·
                refine ⟨78626353535792746182194381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52417569023861830788129587 78626353535792746182194381)
                ·
                  refine ⟨29484882575922279818322893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78626353535792746182194381 29484882575922279818322893)
                  ·
                    refine ⟨11056830965970854931871085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29484882575922279818322893 11056830965970854931871085)
                    ·
                      refine ⟨4146311612239070599451657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11056830965970854931871085 4146311612239070599451657)
                      ·
                        rfl

theorem cell23_8074913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_8074913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074913 prefixEnd_8074913 := by exact prefixLift 8074913
  have htrace : WordTrace (prefixWord ++ tailWord_8074913) baseStart_8074913 baseEnd_8074913 := by
    simpa [prefixWord, tailWord_8074913, baseEnd_8074913] using wordTrace_append hprefix tailTrace_8074913
  have hstable : (prefixWord ++ tailWord_8074913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074913).length < 2 ^ (prefixWord ++ tailWord_8074913).sum := by decide
  have hdescent : baseEnd_8074913 < baseStart_8074913 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074914 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 1, 1, 4]
def baseStart_8074914 : Nat := 118140960795 + 8074914 * 2 ^ 59
def prefixEnd_8074914 : Nat := 4983230072969 + 3 ^ 40 * 8074914 * 2
def baseEnd_8074914 : Nat := 4146312125719725095539153

theorem tailTrace_8074914 : CollatzResearch.WordTrace tailWord_8074914 prefixEnd_8074914 4146312125719725095539153 := by
  unfold tailWord_8074914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73629077266993284590425949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196344206045315425574469197 73629077266993284590425949)
  ·
    refine ⟨27610903975122481721409731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73629077266993284590425949 27610903975122481721409731)
    ·
      refine ⟨41416355962683722582114597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27610903975122481721409731 41416355962683722582114597)
      ·
        refine ⟨7765566743003197984146487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41416355962683722582114597 7765566743003197984146487)
        ·
          refine ⟨11648350114504796976219731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765566743003197984146487 11648350114504796976219731)
          ·
            refine ⟨17472525171757195464329597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648350114504796976219731 17472525171757195464329597)
            ·
              refine ⟨6552196939408948299123599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17472525171757195464329597 6552196939408948299123599)
              ·
                refine ⟨9828295409113422448685399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552196939408948299123599 9828295409113422448685399)
                ·
                  refine ⟨14742443113670133673028099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9828295409113422448685399 14742443113670133673028099)
                  ·
                    refine ⟨22113664670505200509542149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14742443113670133673028099 22113664670505200509542149)
                    ·
                      refine ⟨4146312125719725095539153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22113664670505200509542149 4146312125719725095539153)
                      ·
                        rfl

theorem cell23_8074914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_8074914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074914 prefixEnd_8074914 := by exact prefixLift 8074914
  have htrace : WordTrace (prefixWord ++ tailWord_8074914) baseStart_8074914 baseEnd_8074914 := by
    simpa [prefixWord, tailWord_8074914, baseEnd_8074914] using wordTrace_append hprefix tailTrace_8074914
  have hstable : (prefixWord ++ tailWord_8074914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074914).length < 2 ^ (prefixWord ++ tailWord_8074914).sum := by decide
  have hdescent : baseEnd_8074914 < baseStart_8074914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074920 : List Nat := [2, 1, 7, 1, 1, 11]
def baseStart_8074920 : Nat := 118140960795 + 8074920 * 2 ^ 59
def prefixEnd_8074920 : Nat := 4983230072969 + 3 ^ 40 * 8074920 * 2
def baseEnd_8074920 : Nat := 17063025541578815111375

theorem tailTrace_8074920 : CollatzResearch.WordTrace tailWord_8074920 prefixEnd_8074920 17063025541578815111375 := by
  unfold tailWord_8074920
  simp only [CollatzResearch.WordTrace]
  refine ⟨147258263952975700693211107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196344351937300934257614809 147258263952975700693211107)
  ·
    refine ⟨220887395929463551039816661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147258263952975700693211107 220887395929463551039816661)
    ·
      refine ⟨5177048342096801977495703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 220887395929463551039816661 5177048342096801977495703)
      ·
        refine ⟨7765572513145202966243555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177048342096801977495703 7765572513145202966243555)
        ·
          refine ⟨11648358769717804449365333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765572513145202966243555 11648358769717804449365333)
          ·
            refine ⟨17063025541578815111375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11648358769717804449365333 17063025541578815111375)
            ·
              rfl

theorem cell23_8074920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 11].length) (baseStart_8074920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074920 prefixEnd_8074920 := by exact prefixLift 8074920
  have htrace : WordTrace (prefixWord ++ tailWord_8074920) baseStart_8074920 baseEnd_8074920 := by
    simpa [prefixWord, tailWord_8074920, baseEnd_8074920] using wordTrace_append hprefix tailTrace_8074920
  have hstable : (prefixWord ++ tailWord_8074920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074920).length < 2 ^ (prefixWord ++ tailWord_8074920).sum := by decide
  have hdescent : baseEnd_8074920 < baseStart_8074920 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074930 : List Nat := [3, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3]
def baseStart_8074930 : Nat := 118140960795 + 8074930 * 2 ^ 59
def prefixEnd_8074930 : Nat := 4983230072969 + 3 ^ 40 * 8074930 * 2
def baseEnd_8074930 : Nat := 4146320341410197032939079

theorem tailTrace_8074930 : CollatzResearch.WordTrace tailWord_8074930 prefixEnd_8074930 4146320341410197032939079 := by
  unfold tailWord_8074930
  simp only [CollatzResearch.WordTrace]
  refine ⟨73629223158978793273571561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196344595090610115396190829 73629223158978793273571561)
  ·
    refine ⟨55221917369234094955178671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73629223158978793273571561 55221917369234094955178671)
    ·
      refine ⟨82832876053851142432768007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55221917369234094955178671 82832876053851142432768007)
      ·
        refine ⟨124249314080776713649152011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82832876053851142432768007 124249314080776713649152011)
        ·
          refine ⟨186373971121165070473728017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124249314080776713649152011 186373971121165070473728017)
          ·
            refine ⟨139780478340873802855296013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186373971121165070473728017 139780478340873802855296013)
            ·
              refine ⟨52417679377827676070736005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139780478340873802855296013 52417679377827676070736005)
              ·
                refine ⟨9828314883342689263263001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52417679377827676070736005 9828314883342689263263001)
                ·
                  refine ⟨7371236162507016947447251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828314883342689263263001 7371236162507016947447251)
                  ·
                    refine ⟨11056854243760525421170877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7371236162507016947447251 11056854243760525421170877)
                    ·
                      refine ⟨4146320341410197032939079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11056854243760525421170877 4146320341410197032939079)
                      ·
                        rfl

theorem cell23_8074930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3].length) (baseStart_8074930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074930 prefixEnd_8074930 := by exact prefixLift 8074930
  have htrace : WordTrace (prefixWord ++ tailWord_8074930) baseStart_8074930 baseEnd_8074930 := by
    simpa [prefixWord, tailWord_8074930, baseEnd_8074930] using wordTrace_append hprefix tailTrace_8074930
  have hstable : (prefixWord ++ tailWord_8074930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074930).length < 2 ^ (prefixWord ++ tailWord_8074930).sum := by decide
  have hdescent : baseEnd_8074930 < baseStart_8074930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074940 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 3, 3, 2]
def baseStart_8074940 : Nat := 118140960795 + 8074940 * 2 ^ 59
def prefixEnd_8074940 : Nat := 4983230072969 + 3 ^ 40 * 8074940 * 2
def baseEnd_8074940 : Nat := 4146325476216741993814033

theorem tailTrace_8074940 : CollatzResearch.WordTrace tailWord_8074940 prefixEnd_8074940 4146325476216741993814033 := by
  unfold tailWord_8074940
  simp only [CollatzResearch.WordTrace]
  refine ⟨147258628682939472401075137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196344838243919296534766849 147258628682939472401075137)
  ·
    refine ⟨110443971512204604300806353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147258628682939472401075137 110443971512204604300806353)
    ·
      refine ⟨82832978634153453225604765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110443971512204604300806353 82832978634153453225604765)
      ·
        refine ⟨31062366987807544959601787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82832978634153453225604765 31062366987807544959601787)
        ·
          refine ⟨46593550481711317439402681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31062366987807544959601787 46593550481711317439402681)
          ·
            refine ⟨34945162861283488079552011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46593550481711317439402681 34945162861283488079552011)
            ·
              refine ⟨52417744291925232119328017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34945162861283488079552011 52417744291925232119328017)
              ·
                refine ⟨39313308218943924089496013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52417744291925232119328017 39313308218943924089496013)
                ·
                  refine ⟨14742490582103971533561005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39313308218943924089496013 14742490582103971533561005)
                  ·
                    refine ⟨5528433968288989325085377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14742490582103971533561005 5528433968288989325085377)
                    ·
                      refine ⟨4146325476216741993814033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528433968288989325085377 4146325476216741993814033)
                      ·
                        rfl

theorem cell23_8074940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_8074940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074940 prefixEnd_8074940 := by exact prefixLift 8074940
  have htrace : WordTrace (prefixWord ++ tailWord_8074940) baseStart_8074940 baseEnd_8074940 := by
    simpa [prefixWord, tailWord_8074940, baseEnd_8074940] using wordTrace_append hprefix tailTrace_8074940
  have hstable : (prefixWord ++ tailWord_8074940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074940).length < 2 ^ (prefixWord ++ tailWord_8074940).sum := by decide
  have hdescent : baseEnd_8074940 < baseStart_8074940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074970 : List Nat := [3, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2]
def baseStart_8074970 : Nat := 118140960795 + 8074970 * 2 ^ 59
def prefixEnd_8074970 : Nat := 4983230072969 + 3 ^ 40 * 8074970 * 2
def baseEnd_8074970 : Nat := 4146340880636376876438895

theorem tailTrace_8074970 : CollatzResearch.WordTrace tailWord_8074970 prefixEnd_8074970 4146340880636376876438895 := by
  unfold tailWord_8074970
  simp only [CollatzResearch.WordTrace]
  refine ⟨73629587888942564981435591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196345567703846839950494909 73629587888942564981435591)
  ·
    refine ⟨110444381833413847472153387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73629587888942564981435591 110444381833413847472153387)
    ·
      refine ⟨165666572750120771208230081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110444381833413847472153387 165666572750120771208230081)
      ·
        refine ⟨124249929562590578406172561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165666572750120771208230081 124249929562590578406172561)
        ·
          refine ⟨93187447171942933804629421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124249929562590578406172561 93187447171942933804629421)
          ·
            refine ⟨34945292689478600176736033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93187447171942933804629421 34945292689478600176736033)
            ·
              refine ⟨26208969517108950132552025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34945292689478600176736033 26208969517108950132552025)
              ·
                refine ⟨19656727137831712599414019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26208969517108950132552025 19656727137831712599414019)
                ·
                  refine ⟨29485090706747568899121029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19656727137831712599414019 29485090706747568899121029)
                  ·
                    refine ⟨5528454507515169168585193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29485090706747568899121029 5528454507515169168585193)
                    ·
                      refine ⟨4146340880636376876438895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528454507515169168585193 4146340880636376876438895)
                      ·
                        rfl

theorem cell23_8074970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_8074970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074970 prefixEnd_8074970 := by exact prefixLift 8074970
  have htrace : WordTrace (prefixWord ++ tailWord_8074970) baseStart_8074970 baseEnd_8074970 := by
    simpa [prefixWord, tailWord_8074970, baseEnd_8074970] using wordTrace_append hprefix tailTrace_8074970
  have hstable : (prefixWord ++ tailWord_8074970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074970).length < 2 ^ (prefixWord ++ tailWord_8074970).sum := by decide
  have hdescent : baseEnd_8074970 < baseStart_8074970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074987 : List Nat := [1, 1, 1, 1, 2, 4, 5, 2, 2, 2, 2]
def baseStart_8074987 : Nat := 118140960795 + 8074987 * 2 ^ 59
def prefixEnd_8074987 : Nat := 4983230072969 + 3 ^ 40 * 8074987 * 2
def baseEnd_8074987 : Nat := 4146349609807503309926317

theorem tailTrace_8074987 : CollatzResearch.WordTrace tailWord_8074987 prefixEnd_8074987 4146349609807503309926317 := by
  unfold tailWord_8074987
  simp only [CollatzResearch.WordTrace]
  refine ⟨294518971596708671829111215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196345981064472447886074143 294518971596708671829111215)
  ·
    refine ⟨441778457395063007743666823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294518971596708671829111215 441778457395063007743666823)
    ·
      refine ⟨662667686092594511615500235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441778457395063007743666823 662667686092594511615500235)
      ·
        refine ⟨994001529138891767423250353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662667686092594511615500235 994001529138891767423250353)
        ·
          refine ⟨745501146854168825567437765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994001529138891767423250353 745501146854168825567437765)
          ·
            refine ⟨139781465035156654793894581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 745501146854168825567437765 139781465035156654793894581)
            ·
              refine ⟨13104512347045936386927617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139781465035156654793894581 13104512347045936386927617)
              ·
                refine ⟨9828384260284452290195713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13104512347045936386927617 9828384260284452290195713)
                ·
                  refine ⟨7371288195213339217646785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828384260284452290195713 7371288195213339217646785)
                  ·
                    refine ⟨5528466146410004413235089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371288195213339217646785 5528466146410004413235089)
                    ·
                      refine ⟨4146349609807503309926317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528466146410004413235089 4146349609807503309926317)
                      ·
                        rfl

theorem cell23_8074987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 2, 2, 2, 2].length) (baseStart_8074987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074987 prefixEnd_8074987 := by exact prefixLift 8074987
  have htrace : WordTrace (prefixWord ++ tailWord_8074987) baseStart_8074987 baseEnd_8074987 := by
    simpa [prefixWord, tailWord_8074987, baseEnd_8074987] using wordTrace_append hprefix tailTrace_8074987
  have hstable : (prefixWord ++ tailWord_8074987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074987).length < 2 ^ (prefixWord ++ tailWord_8074987).sum := by decide
  have hdescent : baseEnd_8074987 < baseStart_8074987 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8074993 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 7]
def baseStart_8074993 : Nat := 118140960795 + 8074993 * 2 ^ 59
def prefixEnd_8074993 : Nat := 4983230072969 + 3 ^ 40 * 8074993 * 2
def baseEnd_8074993 : Nat := 460705854521270031827921

theorem tailTrace_8074993 : CollatzResearch.WordTrace tailWord_8074993 prefixEnd_8074993 460705854521270031827921 := by
  unfold tailWord_8074993
  simp only [CollatzResearch.WordTrace]
  refine ⟨294519190434686934853829633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196346126956457956569219755 294519190434686934853829633)
  ·
    refine ⟨220889392826015201140372225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294519190434686934853829633 220889392826015201140372225)
    ·
      refine ⟨165667044619511400855279169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220889392826015201140372225 165667044619511400855279169)
      ·
        refine ⟨124250283464633550641459377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165667044619511400855279169 124250283464633550641459377)
        ·
          refine ⟨93187712598475162981094533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124250283464633550641459377 93187712598475162981094533)
          ·
            refine ⟨17472696112214093058955225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93187712598475162981094533 17472696112214093058955225)
            ·
              refine ⟨13104522084160569794216419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17472696112214093058955225 13104522084160569794216419)
              ·
                refine ⟨19656783126240854691324629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13104522084160569794216419 19656783126240854691324629)
                ·
                  refine ⟨460705854521270031827921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19656783126240854691324629 460705854521270031827921)
                  ·
                    rfl

theorem cell23_8074993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 7].length) (baseStart_8074993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8074993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8074993 prefixEnd_8074993 := by exact prefixLift 8074993
  have htrace : WordTrace (prefixWord ++ tailWord_8074993) baseStart_8074993 baseEnd_8074993 := by
    simpa [prefixWord, tailWord_8074993, baseEnd_8074993] using wordTrace_append hprefix tailTrace_8074993
  have hstable : (prefixWord ++ tailWord_8074993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8074993).length < 2 ^ (prefixWord ++ tailWord_8074993).sum := by decide
  have hdescent : baseEnd_8074993 < baseStart_8074993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8074993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075004 : List Nat := [2, 2, 2, 1, 3, 1, 5, 1, 2, 2, 2]
def baseStart_8075004 : Nat := 118140960795 + 8075004 * 2 ^ 59
def prefixEnd_8075004 : Nat := 4983230072969 + 3 ^ 40 * 8075004 * 2
def baseEnd_8075004 : Nat := 4146358338978629743413739

theorem tailTrace_8075004 : CollatzResearch.WordTrace tailWord_8075004 prefixEnd_8075004 4146358338978629743413739 := by
  unfold tailWord_8075004
  simp only [CollatzResearch.WordTrace]
  refine ⟨147259795818823541866240033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196346394425098055821653377 147259795818823541866240033)
  ·
    refine ⟨110444846864117656399680025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147259795818823541866240033 110444846864117656399680025)
    ·
      refine ⟨82833635148088242299760019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110444846864117656399680025 82833635148088242299760019)
      ·
        refine ⟨124250452722132363449640029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82833635148088242299760019 124250452722132363449640029)
        ·
          refine ⟨46593919770799636293615011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124250452722132363449640029 46593919770799636293615011)
          ·
            refine ⟨69890879656199454440422517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46593919770799636293615011 69890879656199454440422517)
            ·
              refine ⟨6552269967768698853789611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69890879656199454440422517 6552269967768698853789611)
              ·
                refine ⟨9828404951653048280684417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552269967768698853789611 9828404951653048280684417)
                ·
                  refine ⟨7371303713739786210513313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828404951653048280684417 7371303713739786210513313)
                  ·
                    refine ⟨5528477785304839657884985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371303713739786210513313 5528477785304839657884985)
                    ·
                      refine ⟨4146358338978629743413739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528477785304839657884985 4146358338978629743413739)
                      ·
                        rfl

theorem cell23_8075004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_8075004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075004 prefixEnd_8075004 := by exact prefixLift 8075004
  have htrace : WordTrace (prefixWord ++ tailWord_8075004) baseStart_8075004 baseEnd_8075004 := by
    simpa [prefixWord, tailWord_8075004, baseEnd_8075004] using wordTrace_append hprefix tailTrace_8075004
  have hstable : (prefixWord ++ tailWord_8075004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075004).length < 2 ^ (prefixWord ++ tailWord_8075004).sum := by decide
  have hdescent : baseEnd_8075004 < baseStart_8075004 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075043 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 4]
def baseStart_8075043 : Nat := 118140960795 + 8075043 * 2 ^ 59
def prefixEnd_8075043 : Nat := 4983230072969 + 3 ^ 40 * 8075043 * 2
def baseEnd_8075043 : Nat := 4146378364724155090826059

theorem tailTrace_8075043 : CollatzResearch.WordTrace tailWord_8075043 prefixEnd_8075043 4146378364724155090826059 := by
  unfold tailWord_8075043
  simp only [CollatzResearch.WordTrace]
  refine ⟨294521014084505793393149783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196347342723003862262099855 294521014084505793393149783)
  ·
    refine ⟨441781521126758690089724675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294521014084505793393149783 441781521126758690089724675)
    ·
      refine ⟨662672281690138035134587013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441781521126758690089724675 662672281690138035134587013)
      ·
        refine ⟨124251052816900881587735065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 662672281690138035134587013 124251052816900881587735065)
        ·
          refine ⟨93188289612675661190801299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124251052816900881587735065 93188289612675661190801299)
          ·
            refine ⟨139782434419013491786201949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93188289612675661190801299 139782434419013491786201949)
            ·
              refine ⟨52418412907130059419825731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139782434419013491786201949 52418412907130059419825731)
              ·
                refine ⟨78627619360695089129738597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52418412907130059419825731 78627619360695089129738597)
                ·
                  refine ⟨14742678630130329211825987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78627619360695089129738597 14742678630130329211825987)
                  ·
                    refine ⟨22114017945195493817738981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14742678630130329211825987 22114017945195493817738981)
                    ·
                      refine ⟨4146378364724155090826059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22114017945195493817738981 4146378364724155090826059)
                      ·
                        rfl

theorem cell23_8075043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_8075043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075043 prefixEnd_8075043 := by exact prefixLift 8075043
  have htrace : WordTrace (prefixWord ++ tailWord_8075043) baseStart_8075043 baseEnd_8075043 := by
    simpa [prefixWord, tailWord_8075043, baseEnd_8075043] using wordTrace_append hprefix tailTrace_8075043
  have hstable : (prefixWord ++ tailWord_8075043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075043).length < 2 ^ (prefixWord ++ tailWord_8075043).sum := by decide
  have hdescent : baseEnd_8075043 < baseStart_8075043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075063 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 3]
def baseStart_8075063 : Nat := 118140960795 + 8075063 * 2 ^ 59
def prefixEnd_8075063 : Nat := 4983230072969 + 3 ^ 40 * 8075063 * 2
def baseEnd_8075063 : Nat := 4146388634337245012575967

theorem tailTrace_8075063 : CollatzResearch.WordTrace tailWord_8075063 prefixEnd_8075063 4146388634337245012575967 := by
  unfold tailWord_8075063
  simp only [CollatzResearch.WordTrace]
  refine ⟨294521743544433336808877843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196347829029622224539251895 294521743544433336808877843)
  ·
    refine ⟨441782615316650005213316765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294521743544433336808877843 441782615316650005213316765)
    ·
      refine ⟨165668480743743751954993787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441782615316650005213316765 165668480743743751954993787)
      ·
        refine ⟨248502721115615627932490681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165668480743743751954993787 248502721115615627932490681)
        ·
          refine ⟨186377040836711720949368011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248502721115615627932490681 186377040836711720949368011)
          ·
            refine ⟨279565561255067581424052017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186377040836711720949368011 279565561255067581424052017)
            ·
              refine ⟨209674170941300686068039013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279565561255067581424052017 209674170941300686068039013)
              ·
                refine ⟨39313907051493878637757315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209674170941300686068039013 39313907051493878637757315)
                ·
                  refine ⟨58970860577240817956635973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39313907051493878637757315 58970860577240817956635973)
                  ·
                    refine ⟨11057036358232653366869245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58970860577240817956635973 11057036358232653366869245)
                    ·
                      refine ⟨4146388634337245012575967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057036358232653366869245 4146388634337245012575967)
                      ·
                        rfl

theorem cell23_8075063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_8075063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075063 prefixEnd_8075063 := by exact prefixLift 8075063
  have htrace : WordTrace (prefixWord ++ tailWord_8075063) baseStart_8075063 baseEnd_8075063 := by
    simpa [prefixWord, tailWord_8075063, baseEnd_8075063] using wordTrace_append hprefix tailTrace_8075063
  have hstable : (prefixWord ++ tailWord_8075063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075063).length < 2 ^ (prefixWord ++ tailWord_8075063).sum := by decide
  have hdescent : baseEnd_8075063 < baseStart_8075063 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075080 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_8075080 : Nat := 118140960795 + 8075080 * 2 ^ 59
def prefixEnd_8075080 : Nat := 4983230072969 + 3 ^ 40 * 8075080 * 2
def baseEnd_8075080 : Nat := 4146397363508371446063389

theorem tailTrace_8075080 : CollatzResearch.WordTrace tailWord_8075080 prefixEnd_8075080 4146397363508371446063389 := by
  unfold tailWord_8075080
  simp only [CollatzResearch.WordTrace]
  refine ⟨147261181792685874356123347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196348242390247832474831129 147261181792685874356123347)
  ·
    refine ⟨220891772689028811534185021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147261181792685874356123347 220891772689028811534185021)
    ·
      refine ⟨82834414758385804325319383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220891772689028811534185021 82834414758385804325319383)
      ·
        refine ⟨124251622137578706487979075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82834414758385804325319383 124251622137578706487979075)
        ·
          refine ⟨186377433206368059731968613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124251622137578706487979075 186377433206368059731968613)
          ·
            refine ⟨34945768726194011199744115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186377433206368059731968613 34945768726194011199744115)
            ·
              refine ⟨52418653089291016799616173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34945768726194011199744115 52418653089291016799616173)
              ·
                refine ⟨19656994908484131299856065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52418653089291016799616173 19656994908484131299856065)
                ·
                  refine ⟨14742746181363098474892049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19656994908484131299856065 14742746181363098474892049)
                  ·
                    refine ⟨11057059636022323856169037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14742746181363098474892049 11057059636022323856169037)
                    ·
                      refine ⟨4146397363508371446063389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057059636022323856169037 4146397363508371446063389)
                      ·
                        rfl

theorem cell23_8075080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_8075080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075080 prefixEnd_8075080 := by exact prefixLift 8075080
  have htrace : WordTrace (prefixWord ++ tailWord_8075080) baseStart_8075080 baseEnd_8075080 := by
    simpa [prefixWord, tailWord_8075080, baseEnd_8075080] using wordTrace_append hprefix tailTrace_8075080
  have hstable : (prefixWord ++ tailWord_8075080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075080).length < 2 ^ (prefixWord ++ tailWord_8075080).sum := by decide
  have hdescent : baseEnd_8075080 < baseStart_8075080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075104 : List Nat := [2, 1, 1, 3, 3, 2, 4, 2, 1, 4]
def baseStart_8075104 : Nat := 118140960795 + 8075104 * 2 ^ 59
def prefixEnd_8075104 : Nat := 4983230072969 + 3 ^ 40 * 8075104 * 2
def baseEnd_8075104 : Nat := 1382136562348026450721093

theorem tailTrace_8075104 : CollatzResearch.WordTrace tailWord_8075104 prefixEnd_8075104 1382136562348026450721093 := by
  unfold tailWord_8075104
  simp only [CollatzResearch.WordTrace]
  refine ⟨147261619468642400405560183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196348825958189867207413577 147261619468642400405560183)
  ·
    refine ⟨220892429202963600608340275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147261619468642400405560183 220892429202963600608340275)
    ·
      refine ⟨331338643804445400912510413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220892429202963600608340275 331338643804445400912510413)
      ·
        refine ⟨124251991426667025342191405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331338643804445400912510413 124251991426667025342191405)
        ·
          refine ⟨46594496785000134503321777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124251991426667025342191405 46594496785000134503321777)
          ·
            refine ⟨34945872588750100877491333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46594496785000134503321777 34945872588750100877491333)
            ·
              refine ⟨6552351110390643914529625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34945872588750100877491333 6552351110390643914529625)
              ·
                refine ⟨4914263332792982935897219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6552351110390643914529625 4914263332792982935897219)
                ·
                  refine ⟨7371394999189474403845829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4914263332792982935897219 7371394999189474403845829)
                  ·
                    refine ⟨1382136562348026450721093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371394999189474403845829 1382136562348026450721093)
                    ·
                      rfl

theorem cell23_8075104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2, 1, 4].length) (baseStart_8075104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075104 prefixEnd_8075104 := by exact prefixLift 8075104
  have htrace : WordTrace (prefixWord ++ tailWord_8075104) baseStart_8075104 baseEnd_8075104 := by
    simpa [prefixWord, tailWord_8075104, baseEnd_8075104] using wordTrace_append hprefix tailTrace_8075104
  have hstable : (prefixWord ++ tailWord_8075104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075104).length < 2 ^ (prefixWord ++ tailWord_8075104).sum := by decide
  have hdescent : baseEnd_8075104 < baseStart_8075104 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075120 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 1, 5, 2]
def baseStart_8075120 : Nat := 118140960795 + 8075120 * 2 ^ 59
def prefixEnd_8075120 : Nat := 4983230072969 + 3 ^ 40 * 8075120 * 2
def baseEnd_8075120 : Nat := 4146417902734551289563205

theorem tailTrace_8075120 : CollatzResearch.WordTrace tailWord_8075120 prefixEnd_8075120 4146417902734551289563205 := by
  unfold tailWord_8075120
  simp only [CollatzResearch.WordTrace]
  refine ⟨147261911252613417771851407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196349215003484557029135209 147261911252613417771851407)
  ·
    refine ⟨220892866878920126657777111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147261911252613417771851407 220892866878920126657777111)
    ·
      refine ⟨331339300318380189986665667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220892866878920126657777111 331339300318380189986665667)
      ·
        refine ⟨497008950477570284979998501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331339300318380189986665667 497008950477570284979998501)
        ·
          refine ⟨93189178214544428433749719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497008950477570284979998501 93189178214544428433749719)
          ·
            refine ⟨139783767321816642650624579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93189178214544428433749719 139783767321816642650624579)
            ·
              refine ⟨209675650982724963975936869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139783767321816642650624579 209675650982724963975936869)
              ·
                refine ⟨39314184559260930745488163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209675650982724963975936869 39314184559260930745488163)
                ·
                  refine ⟨58971276838891396118232245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39314184559260930745488163 58971276838891396118232245)
                  ·
                    refine ⟨5528557203646068386084273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58971276838891396118232245 5528557203646068386084273)
                    ·
                      refine ⟨4146417902734551289563205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528557203646068386084273 4146417902734551289563205)
                      ·
                        rfl

theorem cell23_8075120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 5, 2].length) (baseStart_8075120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075120 prefixEnd_8075120 := by exact prefixLift 8075120
  have htrace : WordTrace (prefixWord ++ tailWord_8075120) baseStart_8075120 baseEnd_8075120 := by
    simpa [prefixWord, tailWord_8075120, baseEnd_8075120] using wordTrace_append hprefix tailTrace_8075120
  have hstable : (prefixWord ++ tailWord_8075120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075120).length < 2 ^ (prefixWord ++ tailWord_8075120).sum := by decide
  have hdescent : baseEnd_8075120 < baseStart_8075120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075187 : List Nat := [1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 3]
def baseStart_8075187 : Nat := 118140960795 + 8075187 * 2 ^ 59
def prefixEnd_8075187 : Nat := 4983230072969 + 3 ^ 40 * 8075187 * 2
def baseEnd_8075187 : Nat := 4146452305938402527425397

theorem tailTrace_8075187 : CollatzResearch.WordTrace tailWord_8075187 prefixEnd_8075187 4146452305938402527425397 := by
  unfold tailWord_8075187
  simp only [CollatzResearch.WordTrace]
  refine ⟨294526266195984105986391815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196350844130656070657594543 294526266195984105986391815)
  ·
    refine ⟨441789399293976158979587723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294526266195984105986391815 441789399293976158979587723)
    ·
      refine ⟨662684098940964238469381585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441789399293976158979587723 662684098940964238469381585)
      ·
        refine ⟨497013074205723178852036189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662684098940964238469381585 497013074205723178852036189)
        ·
          refine ⟨186379902827146192069513571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497013074205723178852036189 186379902827146192069513571)
          ·
            refine ⟨279569854240719288104270357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186379902827146192069513571 279569854240719288104270357)
            ·
              refine ⟨13104836917533716629887673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 279569854240719288104270357 13104836917533716629887673)
              ·
                refine ⟨9828627688150287472415755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13104836917533716629887673 9828627688150287472415755)
                ·
                  refine ⟨14742941532225431208623633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9828627688150287472415755 14742941532225431208623633)
                  ·
                    refine ⟨11057206149169073406467725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14742941532225431208623633 11057206149169073406467725)
                    ·
                      refine ⟨4146452305938402527425397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057206149169073406467725 4146452305938402527425397)
                      ·
                        rfl

theorem cell23_8075187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_8075187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075187 prefixEnd_8075187 := by exact prefixLift 8075187
  have htrace : WordTrace (prefixWord ++ tailWord_8075187) baseStart_8075187 baseEnd_8075187 := by
    simpa [prefixWord, tailWord_8075187, baseEnd_8075187] using wordTrace_append hprefix tailTrace_8075187
  have hstable : (prefixWord ++ tailWord_8075187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075187).length < 2 ^ (prefixWord ++ tailWord_8075187).sum := by decide
  have hdescent : baseEnd_8075187 < baseStart_8075187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075200 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_8075200 : Nat := 118140960795 + 8075200 * 2 ^ 59
def prefixEnd_8075200 : Nat := 4983230072969 + 3 ^ 40 * 8075200 * 2
def baseEnd_8075200 : Nat := 4146458981186910976562837

theorem tailTrace_8075200 : CollatzResearch.WordTrace tailWord_8075200 prefixEnd_8075200 4146458981186910976562837 := by
  unfold tailWord_8075200
  simp only [CollatzResearch.WordTrace]
  refine ⟨147263370172468504603307527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196351160229958006137743369 147263370172468504603307527)
  ·
    refine ⟨220895055258702756904961291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147263370172468504603307527 220895055258702756904961291)
    ·
      refine ⟨331342582888054135357441937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220895055258702756904961291 331342582888054135357441937)
      ·
        refine ⟨248506937166040601518081453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331342582888054135357441937 248506937166040601518081453)
        ·
          refine ⟨93190101437265225569280545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248506937166040601518081453 93190101437265225569280545)
          ·
            refine ⟨69892576077948919176960409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93190101437265225569280545 69892576077948919176960409)
            ·
              refine ⟨52419432058461689382720307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69892576077948919176960409 52419432058461689382720307)
              ·
                refine ⟨78629148087692534074080461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52419432058461689382720307 78629148087692534074080461)
                ·
                  refine ⟨29485930532884700277780173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78629148087692534074080461 29485930532884700277780173)
                  ·
                    refine ⟨11057223949831762604167565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29485930532884700277780173 11057223949831762604167565)
                    ·
                      refine ⟨4146458981186910976562837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057223949831762604167565 4146458981186910976562837)
                      ·
                        rfl

theorem cell23_8075200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_8075200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075200 prefixEnd_8075200 := by exact prefixLift 8075200
  have htrace : WordTrace (prefixWord ++ tailWord_8075200) baseStart_8075200 baseEnd_8075200 := by
    simpa [prefixWord, tailWord_8075200, baseEnd_8075200] using wordTrace_append hprefix tailTrace_8075200
  have hstable : (prefixWord ++ tailWord_8075200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075200).length < 2 ^ (prefixWord ++ tailWord_8075200).sum := by decide
  have hdescent : baseEnd_8075200 < baseStart_8075200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075218 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 3, 2, 2]
def baseStart_8075218 : Nat := 118140960795 + 8075218 * 2 ^ 59
def prefixEnd_8075218 : Nat := 4983230072969 + 3 ^ 40 * 8075218 * 2
def baseEnd_8075218 : Nat := 4146468223838691906137755

theorem tailTrace_8075218 : CollatzResearch.WordTrace tailWord_8075218 prefixEnd_8075218 4146468223838691906137755 := by
  unfold tailWord_8075218
  simp only [CollatzResearch.WordTrace]
  refine ⟨73631849214717949570192577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196351597905914532187180205 73631849214717949570192577)
  ·
    refine ⟨55223886911038462177644433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73631849214717949570192577 55223886911038462177644433)
    ·
      refine ⟨41417915183278846633233325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55223886911038462177644433 41417915183278846633233325)
      ·
        refine ⟨15531718193729567487462497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41417915183278846633233325 15531718193729567487462497)
        ·
          refine ⟨11648788645297175615596873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15531718193729567487462497 11648788645297175615596873)
          ·
            refine ⟨8736591483972881711697655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11648788645297175615596873 8736591483972881711697655)
            ·
              refine ⟨13104887225959322567546483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8736591483972881711697655 13104887225959322567546483)
              ·
                refine ⟨19657330838938983851319725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13104887225959322567546483 19657330838938983851319725)
                ·
                  refine ⟨7371499064602118944244897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19657330838938983851319725 7371499064602118944244897)
                  ·
                    refine ⟨5528624298451589208183673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371499064602118944244897 5528624298451589208183673)
                    ·
                      refine ⟨4146468223838691906137755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528624298451589208183673 4146468223838691906137755)
                      ·
                        rfl

theorem cell23_8075218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_8075218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075218 prefixEnd_8075218 := by exact prefixLift 8075218
  have htrace : WordTrace (prefixWord ++ tailWord_8075218) baseStart_8075218 baseEnd_8075218 := by
    simpa [prefixWord, tailWord_8075218, baseEnd_8075218] using wordTrace_append hprefix tailTrace_8075218
  have hstable : (prefixWord ++ tailWord_8075218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075218).length < 2 ^ (prefixWord ++ tailWord_8075218).sum := by decide
  have hdescent : baseEnd_8075218 < baseStart_8075218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075220 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_8075220 : Nat := 118140960795 + 8075220 * 2 ^ 59
def prefixEnd_8075220 : Nat := 4983230072969 + 3 ^ 40 * 8075220 * 2
def baseEnd_8075220 : Nat := 1382156416933333632770915

theorem tailTrace_8075220 : CollatzResearch.WordTrace tailWord_8075220 prefixEnd_8075220 1382156416933333632770915 := by
  unfold tailWord_8075220
  simp only [CollatzResearch.WordTrace]
  refine ⟨147263734902432276311171557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196351646536576368414895409 147263734902432276311171557)
  ·
    refine ⟨27611950294206051808344667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147263734902432276311171557 27611950294206051808344667)
    ·
      refine ⟨41417925441309077712517001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27611950294206051808344667 41417925441309077712517001)
      ·
        refine ⟨31063444080981808284387751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41417925441309077712517001 31063444080981808284387751)
        ·
          refine ⟨46595166121472712426581627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31063444080981808284387751 46595166121472712426581627)
          ·
            refine ⟨69892749182209068639872441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46595166121472712426581627 69892749182209068639872441)
            ·
              refine ⟨52419561886656801479904331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69892749182209068639872441 52419561886656801479904331)
              ·
                refine ⟨78629342829985202219856497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52419561886656801479904331 78629342829985202219856497)
                ·
                  refine ⟨58972007122488901664892373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78629342829985202219856497 58972007122488901664892373)
                  ·
                    refine ⟨1382156416933333632770915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58972007122488901664892373 1382156416933333632770915)
                    ·
                      rfl

theorem cell23_8075220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_8075220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075220 prefixEnd_8075220 := by exact prefixLift 8075220
  have htrace : WordTrace (prefixWord ++ tailWord_8075220) baseStart_8075220 baseEnd_8075220 := by
    simpa [prefixWord, tailWord_8075220, baseEnd_8075220] using wordTrace_append hprefix tailTrace_8075220
  have hstable : (prefixWord ++ tailWord_8075220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075220).length < 2 ^ (prefixWord ++ tailWord_8075220).sum := by decide
  have hdescent : baseEnd_8075220 < baseStart_8075220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075228 : List Nat := [2, 2, 6, 1, 1, 1, 1, 3, 2, 4]
def baseStart_8075228 : Nat := 118140960795 + 8075228 * 2 ^ 59
def prefixEnd_8075228 : Nat := 4983230072969 + 3 ^ 40 * 8075228 * 2
def baseEnd_8075228 : Nat := 1382157786215078955670903

theorem tailTrace_8075228 : CollatzResearch.WordTrace tailWord_8075228 prefixEnd_8075228 1382157786215078955670903 := by
  unfold tailWord_8075228
  simp only [CollatzResearch.WordTrace]
  refine ⟨147263880794417784994317169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196351841059223713325756225 147263880794417784994317169)
  ·
    refine ⟨110447910595813338745737877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147263880794417784994317169 110447910595813338745737877)
    ·
      refine ⟨5177245809178750253706463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 110447910595813338745737877 5177245809178750253706463)
      ·
        refine ⟨7765868713768125380559695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5177245809178750253706463 7765868713768125380559695)
        ·
          refine ⟨11648803070652188070839543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765868713768125380559695 11648803070652188070839543)
          ·
            refine ⟨17473204605978282106259315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648803070652188070839543 17473204605978282106259315)
            ·
              refine ⟨26209806908967423159388973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17473204605978282106259315 26209806908967423159388973)
              ·
                refine ⟨9828677590862783684770865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26209806908967423159388973 9828677590862783684770865)
                ·
                  refine ⟨7371508193147087763578149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828677590862783684770865 7371508193147087763578149)
                  ·
                    refine ⟨1382157786215078955670903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7371508193147087763578149 1382157786215078955670903)
                    ·
                      rfl

theorem cell23_8075228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_8075228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075228 prefixEnd_8075228 := by exact prefixLift 8075228
  have htrace : WordTrace (prefixWord ++ tailWord_8075228) baseStart_8075228 baseEnd_8075228 := by
    simpa [prefixWord, tailWord_8075228, baseEnd_8075228] using wordTrace_append hprefix tailTrace_8075228
  have hstable : (prefixWord ++ tailWord_8075228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075228).length < 2 ^ (prefixWord ++ tailWord_8075228).sum := by decide
  have hdescent : baseEnd_8075228 < baseStart_8075228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075257 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 3, 4, 2]
def baseStart_8075257 : Nat := 118140960795 + 8075257 * 2 ^ 59
def prefixEnd_8075257 : Nat := 4983230072969 + 3 ^ 40 * 8075257 * 2
def baseEnd_8075257 : Nat := 4146488249584217253550075

theorem tailTrace_8075257 : CollatzResearch.WordTrace tailWord_8075257 prefixEnd_8075257 4146488249584217253550075 := by
  unfold tailWord_8075257
  simp only [CollatzResearch.WordTrace]
  refine ⟨294528819305730507941440025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196352546203820338627626683 294528819305730507941440025)
  ·
    refine ⟨220896614479297880956080019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294528819305730507941440025 220896614479297880956080019)
    ·
      refine ⟨331344921718946821434120029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220896614479297880956080019 331344921718946821434120029)
      ·
        refine ⟨124254345644605058037795011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331344921718946821434120029 124254345644605058037795011)
        ·
          refine ⟨186381518466907587056692517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124254345644605058037795011 186381518466907587056692517)
          ·
            refine ⟨34946534712545172573129847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186381518466907587056692517 34946534712545172573129847)
            ·
              refine ⟨52419802068817758859694771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34946534712545172573129847 52419802068817758859694771)
              ·
                refine ⟨78629703103226638289542157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52419802068817758859694771 78629703103226638289542157)
                ·
                  refine ⟨29486138663709989358578309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78629703103226638289542157 29486138663709989358578309)
                  ·
                    refine ⟨5528650999445623004733433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29486138663709989358578309 5528650999445623004733433)
                    ·
                      refine ⟨4146488249584217253550075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528650999445623004733433 4146488249584217253550075)
                      ·
                        rfl

theorem cell23_8075257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 4, 2].length) (baseStart_8075257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075257 prefixEnd_8075257 := by exact prefixLift 8075257
  have htrace : WordTrace (prefixWord ++ tailWord_8075257) baseStart_8075257 baseEnd_8075257 := by
    simpa [prefixWord, tailWord_8075257, baseEnd_8075257] using wordTrace_append hprefix tailTrace_8075257
  have hstable : (prefixWord ++ tailWord_8075257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075257).length < 2 ^ (prefixWord ++ tailWord_8075257).sum := by decide
  have hdescent : baseEnd_8075257 < baseStart_8075257 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075260 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 2, 1, 5]
def baseStart_8075260 : Nat := 118140960795 + 8075260 * 2 ^ 59
def prefixEnd_8075260 : Nat := 4983230072969 + 3 ^ 40 * 8075260 * 2
def baseEnd_8075260 : Nat := 4146489790026180741812561

theorem tailTrace_8075260 : CollatzResearch.WordTrace tailWord_8075260 prefixEnd_8075260 4146489790026180741812561 := by
  unfold tailWord_8075260
  simp only [CollatzResearch.WordTrace]
  refine ⟨147264464362359819726899617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196352619149813092969199489 147264464362359819726899617)
  ·
    refine ⟨110448348271769864795174713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147264464362359819726899617 110448348271769864795174713)
    ·
      refine ⟨82836261203827398596381035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110448348271769864795174713 82836261203827398596381035)
      ·
        refine ⟨124254391805741097894571553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82836261203827398596381035 124254391805741097894571553)
        ·
          refine ⟨93190793854305823420928665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124254391805741097894571553 93190793854305823420928665)
          ·
            refine ⟨69893095390729367565696499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93190793854305823420928665 69893095390729367565696499)
            ·
              refine ⟨104839643086094051348544749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69893095390729367565696499 104839643086094051348544749)
              ·
                refine ⟨39314866157285269255704281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104839643086094051348544749 39314866157285269255704281)
                ·
                  refine ⟨29486149617963951941778211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39314866157285269255704281 29486149617963951941778211)
                  ·
                    refine ⟨44229224426945927912667317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29486149617963951941778211 44229224426945927912667317)
                    ·
                      refine ⟨4146489790026180741812561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44229224426945927912667317 4146489790026180741812561)
                      ·
                        rfl

theorem cell23_8075260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_8075260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075260 prefixEnd_8075260 := by exact prefixLift 8075260
  have htrace : WordTrace (prefixWord ++ tailWord_8075260) baseStart_8075260 baseEnd_8075260 := by
    simpa [prefixWord, tailWord_8075260, baseEnd_8075260] using wordTrace_append hprefix tailTrace_8075260
  have hstable : (prefixWord ++ tailWord_8075260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075260).length < 2 ^ (prefixWord ++ tailWord_8075260).sum := by decide
  have hdescent : baseEnd_8075260 < baseStart_8075260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075268 : List Nat := [2, 3, 2, 4, 1, 1, 2, 2, 2, 1, 3]
def baseStart_8075268 : Nat := 118140960795 + 8075268 * 2 ^ 59
def prefixEnd_8075268 : Nat := 4983230072969 + 3 ^ 40 * 8075268 * 2
def baseEnd_8075268 : Nat := 4146493897871416710512525

theorem tailTrace_8075268 : CollatzResearch.WordTrace tailWord_8075268 prefixEnd_8075268 4146493897871416710512525 := by
  unfold tailWord_8075268
  simp only [CollatzResearch.WordTrace]
  refine ⟨147264610254345328410045229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196352813672460437880060305 147264610254345328410045229)
  ·
    refine ⟨55224228845379498153766961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147264610254345328410045229 55224228845379498153766961)
    ·
      refine ⟨41418171634034623615325221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55224228845379498153766961 41418171634034623615325221)
      ·
        refine ⟨7765907181381491927873479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41418171634034623615325221 7765907181381491927873479)
        ·
          refine ⟨11648860772072237891810219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7765907181381491927873479 11648860772072237891810219)
          ·
            refine ⟨17473291158108356837715329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648860772072237891810219 17473291158108356837715329)
            ·
              refine ⟨13104968368581267628286497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17473291158108356837715329 13104968368581267628286497)
              ·
                refine ⟨9828726276435950721214873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13104968368581267628286497 9828726276435950721214873)
                ·
                  refine ⟨7371544707326963040911155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9828726276435950721214873 7371544707326963040911155)
                  ·
                    refine ⟨11057317060990444561366733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7371544707326963040911155 11057317060990444561366733)
                    ·
                      refine ⟨4146493897871416710512525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057317060990444561366733 4146493897871416710512525)
                      ·
                        rfl

theorem cell23_8075268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_8075268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075268 prefixEnd_8075268 := by exact prefixLift 8075268
  have htrace : WordTrace (prefixWord ++ tailWord_8075268) baseStart_8075268 baseEnd_8075268 := by
    simpa [prefixWord, tailWord_8075268, baseEnd_8075268] using wordTrace_append hprefix tailTrace_8075268
  have hstable : (prefixWord ++ tailWord_8075268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075268).length < 2 ^ (prefixWord ++ tailWord_8075268).sum := by decide
  have hdescent : baseEnd_8075268 < baseStart_8075268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075297 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 7]
def baseStart_8075297 : Nat := 118140960795 + 8075297 * 2 ^ 59
def prefixEnd_8075297 : Nat := 4983230072969 + 3 ^ 40 * 8075297 * 2
def baseEnd_8075297 : Nat := 460723198756710788561099

theorem tailTrace_8075297 : CollatzResearch.WordTrace tailWord_8075297 prefixEnd_8075297 460723198756710788561099 := by
  unfold tailWord_8075297
  simp only [CollatzResearch.WordTrace]
  refine ⟨294530278225585594772896145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196353518817057063181930763 294530278225585594772896145)
  ·
    refine ⟨220897708669189196079672109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294530278225585594772896145 220897708669189196079672109)
    ·
      refine ⟨82836640750945948529877041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220897708669189196079672109 82836640750945948529877041)
      ·
        refine ⟨62127480563209461397407781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82836640750945948529877041 62127480563209461397407781)
        ·
          refine ⟨11648902605601774012013959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62127480563209461397407781 11648902605601774012013959)
          ·
            refine ⟨17473353908402661018020939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11648902605601774012013959 17473353908402661018020939)
            ·
              refine ⟨26210030862603991527031409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17473353908402661018020939 26210030862603991527031409)
              ·
                refine ⟨19657523146952993645273557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26210030862603991527031409 19657523146952993645273557)
                ·
                  refine ⟨460723198756710788561099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19657523146952993645273557 460723198756710788561099)
                  ·
                    rfl

theorem cell23_8075297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 7].length) (baseStart_8075297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075297 prefixEnd_8075297 := by exact prefixLift 8075297
  have htrace : WordTrace (prefixWord ++ tailWord_8075297) baseStart_8075297 baseEnd_8075297 := by
    simpa [prefixWord, tailWord_8075297, baseEnd_8075297] using wordTrace_append hprefix tailTrace_8075297
  have hstable : (prefixWord ++ tailWord_8075297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075297).length < 2 ^ (prefixWord ++ tailWord_8075297).sum := by decide
  have hdescent : baseEnd_8075297 < baseStart_8075297 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075314 : List Nat := [3, 2, 1, 1, 2, 4, 2, 3, 5]
def baseStart_8075314 : Nat := 118140960795 + 8075314 * 2 ^ 59
def prefixEnd_8075314 : Nat := 4983230072969 + 3 ^ 40 * 8075314 * 2
def baseEnd_8075314 : Nat := 460724168664613725615257

theorem tailTrace_8075314 : CollatzResearch.WordTrace tailWord_8075314 prefixEnd_8075314 460724168664613725615257 := by
  unfold tailWord_8075314
  simp only [CollatzResearch.WordTrace]
  refine ⟨73632724566631001669066249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196353932177682671117509997 73632724566631001669066249)
  ·
    refine ⟨55224543424973251251799687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73632724566631001669066249 55224543424973251251799687)
    ·
      refine ⟨82836815137459876877699531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55224543424973251251799687 82836815137459876877699531)
      ·
        refine ⟨124255222706189815316549297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82836815137459876877699531 124255222706189815316549297)
        ·
          refine ⟨93191417029642361487411973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124255222706189815316549297 93191417029642361487411973)
          ·
            refine ⟨17473390693057942778889745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93191417029642361487411973 17473390693057942778889745)
            ·
              refine ⟨13105043019793457084167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17473390693057942778889745 13105043019793457084167309)
              ·
                refine ⟨4914391132422546406562741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13105043019793457084167309 4914391132422546406562741)
                ·
                  refine ⟨460724168664613725615257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4914391132422546406562741 460724168664613725615257)
                  ·
                    rfl

theorem cell23_8075314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_8075314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075314 prefixEnd_8075314 := by exact prefixLift 8075314
  have htrace : WordTrace (prefixWord ++ tailWord_8075314) baseStart_8075314 baseEnd_8075314 := by
    simpa [prefixWord, tailWord_8075314, baseEnd_8075314] using wordTrace_append hprefix tailTrace_8075314
  have hstable : (prefixWord ++ tailWord_8075314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075314).length < 2 ^ (prefixWord ++ tailWord_8075314).sum := by decide
  have hdescent : baseEnd_8075314 < baseStart_8075314 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075347 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 6, 4, 2]
def baseStart_8075347 : Nat := 118140960795 + 8075347 * 2 ^ 59
def prefixEnd_8075347 : Nat := 4983230072969 + 3 ^ 40 * 8075347 * 2
def baseEnd_8075347 : Nat := 4146534462843121901424661

theorem tailTrace_8075347 : CollatzResearch.WordTrace tailWord_8075347 prefixEnd_8075347 4146534462843121901424661 := by
  unfold tailWord_8075347
  simp only [CollatzResearch.WordTrace]
  refine ⟨294532101875404453312216295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196354734583602968874810863 294532101875404453312216295)
  ·
    refine ⟨441798152813106679968324443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294532101875404453312216295 441798152813106679968324443)
    ·
      refine ⟨662697229219660019952486665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441798152813106679968324443 662697229219660019952486665)
      ·
        refine ⟨497022921914745014964364999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662697229219660019952486665 497022921914745014964364999)
        ·
          refine ⟨745534382872117522446547499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497022921914745014964364999 745534382872117522446547499)
          ·
            refine ⟨1118301574308176283669821249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745534382872117522446547499 1118301574308176283669821249)
            ·
              refine ⟨838726180731132212752365937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1118301574308176283669821249 838726180731132212752365937)
              ·
                refine ⟨629044635548349159564274453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838726180731132212752365937 629044635548349159564274453)
                ·
                  refine ⟨29486467291328866854575365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 629044635548349159564274453 29486467291328866854575365)
                  ·
                    refine ⟨5528712617124162535232881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29486467291328866854575365 5528712617124162535232881)
                    ·
                      refine ⟨4146534462843121901424661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528712617124162535232881 4146534462843121901424661)
                      ·
                        rfl

theorem cell23_8075347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 6, 4, 2].length) (baseStart_8075347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075347 prefixEnd_8075347 := by exact prefixLift 8075347
  have htrace : WordTrace (prefixWord ++ tailWord_8075347) baseStart_8075347 baseEnd_8075347 := by
    simpa [prefixWord, tailWord_8075347, baseEnd_8075347] using wordTrace_append hprefix tailTrace_8075347
  have hstable : (prefixWord ++ tailWord_8075347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075347).length < 2 ^ (prefixWord ++ tailWord_8075347).sum := by decide
  have hdescent : baseEnd_8075347 < baseStart_8075347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075367 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 3]
def baseStart_8075367 : Nat := 118140960795 + 8075367 * 2 ^ 59
def prefixEnd_8075367 : Nat := 4983230072969 + 3 ^ 40 * 8075367 * 2
def baseEnd_8075367 : Nat := 4146544732456211823174569

theorem tailTrace_8075367 : CollatzResearch.WordTrace tailWord_8075367 prefixEnd_8075367 4146544732456211823174569 := by
  unfold tailWord_8075367
  simp only [CollatzResearch.WordTrace]
  refine ⟨294532831335331996727944355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196355220890221331151962903 294532831335331996727944355)
  ·
    refine ⟨441799247002997995091916533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294532831335331996727944355 441799247002997995091916533)
    ·
      refine ⟨41418679406531062039867175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441799247002997995091916533 41418679406531062039867175)
      ·
        refine ⟨62128019109796593059800763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41418679406531062039867175 62128019109796593059800763)
        ·
          refine ⟨93192028664694889589701145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62128019109796593059800763 93192028664694889589701145)
          ·
            refine ⟨69894021498521167192275859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93192028664694889589701145 69894021498521167192275859)
            ·
              refine ⟨104841032247781750788413789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69894021498521167192275859 104841032247781750788413789)
              ·
                refine ⟨39315387092918156545655171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104841032247781750788413789 39315387092918156545655171)
                ·
                  refine ⟨58973080639377234818482757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39315387092918156545655171 58973080639377234818482757)
                  ·
                    refine ⟨11057452619883231528465517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58973080639377234818482757 11057452619883231528465517)
                    ·
                      refine ⟨4146544732456211823174569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057452619883231528465517 4146544732456211823174569)
                      ·
                        rfl

theorem cell23_8075367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_8075367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075367 prefixEnd_8075367 := by exact prefixLift 8075367
  have htrace : WordTrace (prefixWord ++ tailWord_8075367) baseStart_8075367 baseEnd_8075367 := by
    simpa [prefixWord, tailWord_8075367, baseEnd_8075367] using wordTrace_append hprefix tailTrace_8075367
  have hstable : (prefixWord ++ tailWord_8075367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075367).length < 2 ^ (prefixWord ++ tailWord_8075367).sum := by decide
  have hdescent : baseEnd_8075367 < baseStart_8075367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075438 : List Nat := [4, 1, 4, 2, 1, 1, 2, 2, 6]
def baseStart_8075438 : Nat := 118140960795 + 8075438 * 2 ^ 59
def prefixEnd_8075438 : Nat := 4983230072969 + 3 ^ 40 * 8075438 * 2
def baseEnd_8075438 : Nat := 460731243286964560598527

theorem tailTrace_8075438 : CollatzResearch.WordTrace tailWord_8075438 prefixEnd_8075438 460731243286964560598527 := by
  unfold tailWord_8075438
  simp only [CollatzResearch.WordTrace]
  refine ⟨36816927614759346981722371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196356947278716517235852645 36816927614759346981722371)
  ·
    refine ⟨55225391422139020472583557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36816927614759346981722371 55225391422139020472583557)
    ·
      refine ⟨10354760891651066338609417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55225391422139020472583557 10354760891651066338609417)
      ·
        refine ⟨7766070668738299753957063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10354760891651066338609417 7766070668738299753957063)
        ·
          refine ⟨11649106003107449630935595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766070668738299753957063 11649106003107449630935595)
          ·
            refine ⟨17473659004661174446403393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11649106003107449630935595 17473659004661174446403393)
            ·
              refine ⟨13105244253495880834802545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17473659004661174446403393 13105244253495880834802545)
              ·
                refine ⟨9828933190121910626101909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13105244253495880834802545 9828933190121910626101909)
                ·
                  refine ⟨460731243286964560598527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9828933190121910626101909 460731243286964560598527)
                  ·
                    rfl

theorem cell23_8075438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_8075438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075438 prefixEnd_8075438 := by exact prefixLift 8075438
  have htrace : WordTrace (prefixWord ++ tailWord_8075438) baseStart_8075438 baseEnd_8075438 := by
    simpa [prefixWord, tailWord_8075438, baseEnd_8075438] using wordTrace_append hprefix tailTrace_8075438
  have hstable : (prefixWord ++ tailWord_8075438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075438).length < 2 ^ (prefixWord ++ tailWord_8075438).sum := by decide
  have hdescent : baseEnd_8075438 < baseStart_8075438 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075471 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 3, 2, 2]
def baseStart_8075471 : Nat := 118140960795 + 8075471 * 2 ^ 59
def prefixEnd_8075471 : Nat := 4983230072969 + 3 ^ 40 * 8075471 * 2
def baseEnd_8075471 : Nat := 4146598134444279416274091

theorem tailTrace_8075471 : CollatzResearch.WordTrace tailWord_8075471 prefixEnd_8075471 4146598134444279416274091 := by
  unfold tailWord_8075471
  simp only [CollatzResearch.WordTrace]
  refine ⟨294536624526955222489730267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196357749684636814993153511 294536624526955222489730267)
  ·
    refine ⟨441804936790432833734595401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294536624526955222489730267 441804936790432833734595401)
    ·
      refine ⟨331353702592824625300946551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441804936790432833734595401 331353702592824625300946551)
      ·
        refine ⟨497030553889236937951419827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331353702592824625300946551 497030553889236937951419827)
        ·
          refine ⟨745545830833855406927129741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497030553889236937951419827 745545830833855406927129741)
          ·
            refine ⟨279579686562695777597673653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745545830833855406927129741 279579686562695777597673653)
            ·
              refine ⟨26210595615252729149781905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279579686562695777597673653 26210595615252729149781905)
              ·
                refine ⟨19657946711439546862336429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26210595615252729149781905 19657946711439546862336429)
                ·
                  refine ⟨7371730016789830073376161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19657946711439546862336429 7371730016789830073376161)
                  ·
                    refine ⟨5528797512592372555032121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7371730016789830073376161 5528797512592372555032121)
                    ·
                      refine ⟨4146598134444279416274091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528797512592372555032121 4146598134444279416274091)
                      ·
                        rfl

theorem cell23_8075471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 2, 2].length) (baseStart_8075471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075471 prefixEnd_8075471 := by exact prefixLift 8075471
  have htrace : WordTrace (prefixWord ++ tailWord_8075471) baseStart_8075471 baseEnd_8075471 := by
    simpa [prefixWord, tailWord_8075471, baseEnd_8075471] using wordTrace_append hprefix tailTrace_8075471
  have hstable : (prefixWord ++ tailWord_8075471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075471).length < 2 ^ (prefixWord ++ tailWord_8075471).sum := by decide
  have hdescent : baseEnd_8075471 < baseStart_8075471 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075517 : List Nat := [1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 5]
def baseStart_8075517 : Nat := 118140960795 + 8075517 * 2 ^ 59
def prefixEnd_8075517 : Nat := 4983230072969 + 3 ^ 40 * 8075517 * 2
def baseEnd_8075517 : Nat := 4146621754554386236298879

theorem tailTrace_8075517 : CollatzResearch.WordTrace tailWord_8075517 prefixEnd_8075517 4146621754554386236298879 := by
  unfold tailWord_8075517
  simp only [CollatzResearch.WordTrace]
  refine ⟨294538302284788572345904805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196358868189859048230603203 294538302284788572345904805)
  ·
    refine ⟨55225931678397857314857151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294538302284788572345904805 55225931678397857314857151)
    ·
      refine ⟨82838897517596785972285727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55225931678397857314857151 82838897517596785972285727)
      ·
        refine ⟨124258346276395178958428591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82838897517596785972285727 124258346276395178958428591)
        ·
          refine ⟨186387519414592768437642887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124258346276395178958428591 186387519414592768437642887)
          ·
            refine ⟨279581279121889152656464331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186387519414592768437642887 279581279121889152656464331)
            ·
              refine ⟨419371918682833728984696497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279581279121889152656464331 419371918682833728984696497)
              ·
                refine ⟨314528939012125296738522373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419371918682833728984696497 314528939012125296738522373)
                ·
                  refine ⟨58974176064773493138472945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314528939012125296738522373 58974176064773493138472945)
                  ·
                    refine ⟨44230632048580119853854709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58974176064773493138472945 44230632048580119853854709)
                    ·
                      refine ⟨4146621754554386236298879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44230632048580119853854709 4146621754554386236298879)
                      ·
                        rfl

theorem cell23_8075517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_8075517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075517 prefixEnd_8075517 := by exact prefixLift 8075517
  have htrace : WordTrace (prefixWord ++ tailWord_8075517) baseStart_8075517 baseEnd_8075517 := by
    simpa [prefixWord, tailWord_8075517, baseEnd_8075517] using wordTrace_append hprefix tailTrace_8075517
  have hstable : (prefixWord ++ tailWord_8075517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075517).length < 2 ^ (prefixWord ++ tailWord_8075517).sum := by decide
  have hdescent : baseEnd_8075517 < baseStart_8075517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075547 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_8075547 : Nat := 118140960795 + 8075547 * 2 ^ 59
def prefixEnd_8075547 : Nat := 4983230072969 + 3 ^ 40 * 8075547 * 2
def baseEnd_8075547 : Nat := 4146637158974021118923741

theorem tailTrace_8075547 : CollatzResearch.WordTrace tailWord_8075547 prefixEnd_8075547 4146637158974021118923741 := by
  unfold tailWord_8075547
  simp only [CollatzResearch.WordTrace]
  refine ⟨294539396474679887469496895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196359597649786591646331263 294539396474679887469496895)
  ·
    refine ⟨441809094712019831204245343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294539396474679887469496895 441809094712019831204245343)
    ·
      refine ⟨662713642068029746806368015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441809094712019831204245343 662713642068029746806368015)
      ·
        refine ⟨994070463102044620209552023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662713642068029746806368015 994070463102044620209552023)
        ·
          refine ⟨1491105694653066930314328035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994070463102044620209552023 1491105694653066930314328035)
          ·
            refine ⟨2236658541979600395471492053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491105694653066930314328035 2236658541979600395471492053)
            ·
              refine ⟨52421684577646884268863095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2236658541979600395471492053 52421684577646884268863095)
              ·
                refine ⟨78632526866470326403294643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52421684577646884268863095 78632526866470326403294643)
                ·
                  refine ⟨117948790299705489604941965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78632526866470326403294643 117948790299705489604941965)
                  ·
                    refine ⟨44230796362389558601853237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117948790299705489604941965 44230796362389558601853237)
                    ·
                      refine ⟨4146637158974021118923741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44230796362389558601853237 4146637158974021118923741)
                      ·
                        rfl

theorem cell23_8075547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_8075547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075547 prefixEnd_8075547 := by exact prefixLift 8075547
  have htrace : WordTrace (prefixWord ++ tailWord_8075547) baseStart_8075547 baseEnd_8075547 := by
    simpa [prefixWord, tailWord_8075547, baseEnd_8075547] using wordTrace_append hprefix tailTrace_8075547
  have hstable : (prefixWord ++ tailWord_8075547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075547).length < 2 ^ (prefixWord ++ tailWord_8075547).sum := by decide
  have hdescent : baseEnd_8075547 < baseStart_8075547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075572 : List Nat := [2, 5, 1, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_8075572 : Nat := 118140960795 + 8075572 * 2 ^ 59
def prefixEnd_8075572 : Nat := 4983230072969 + 3 ^ 40 * 8075572 * 2
def baseEnd_8075572 : Nat := 4146649995990383521111127

theorem tailTrace_8075572 : CollatzResearch.WordTrace tailWord_8075572 prefixEnd_8075572 4146649995990383521111127 := by
  unfold tailWord_8075572
  simp only [CollatzResearch.WordTrace]
  refine ⟨147270154149794658369578485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196360205533059544492771313 147270154149794658369578485)
  ·
    refine ⟨13806576951543249222147983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147270154149794658369578485 13806576951543249222147983)
    ·
      refine ⟨20709865427314873833221975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13806576951543249222147983 20709865427314873833221975)
      ·
        refine ⟨31064798140972310749832963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20709865427314873833221975 31064798140972310749832963)
        ·
          refine ⟨46597197211458466124749445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31064798140972310749832963 46597197211458466124749445)
          ·
            refine ⟨8736974477148462398390521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46597197211458466124749445 8736974477148462398390521)
            ·
              refine ⟨6552730857861346798792891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8736974477148462398390521 6552730857861346798792891)
              ·
                refine ⟨9829096286792020198189337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6552730857861346798792891 9829096286792020198189337)
                ·
                  refine ⟨7371822215094015148642003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9829096286792020198189337 7371822215094015148642003)
                  ·
                    refine ⟨11057733322641022722963005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7371822215094015148642003 11057733322641022722963005)
                    ·
                      refine ⟨4146649995990383521111127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057733322641022722963005 4146649995990383521111127)
                      ·
                        rfl

theorem cell23_8075572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_8075572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075572 prefixEnd_8075572 := by exact prefixLift 8075572
  have htrace : WordTrace (prefixWord ++ tailWord_8075572) baseStart_8075572 baseEnd_8075572 := by
    simpa [prefixWord, tailWord_8075572, baseEnd_8075572] using wordTrace_append hprefix tailTrace_8075572
  have hstable : (prefixWord ++ tailWord_8075572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075572).length < 2 ^ (prefixWord ++ tailWord_8075572).sum := by decide
  have hdescent : baseEnd_8075572 < baseStart_8075572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075594 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3]
def baseStart_8075594 : Nat := 118140960795 + 8075594 * 2 ^ 59
def prefixEnd_8075594 : Nat := 4983230072969 + 3 ^ 40 * 8075594 * 2
def baseEnd_8075594 : Nat := 4146661292564782435036025

theorem tailTrace_8075594 : CollatzResearch.WordTrace tailWord_8075594 prefixEnd_8075594 4146661292564782435036025 := by
  unfold tailWord_8075594
  simp only [CollatzResearch.WordTrace]
  refine ⟨73635277676377403624114459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196360740470339742997638557 73635277676377403624114459)
  ·
    refine ⟨110452916514566105436171689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73635277676377403624114459 110452916514566105436171689)
    ·
      refine ⟨82839687385924579077128767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110452916514566105436171689 82839687385924579077128767)
      ·
        refine ⟨124259531078886868615693151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82839687385924579077128767 124259531078886868615693151)
        ·
          refine ⟨186389296618330302923539727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124259531078886868615693151 186389296618330302923539727)
          ·
            refine ⟨279583944927495454385309591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186389296618330302923539727 279583944927495454385309591)
            ·
              refine ⟨419375917391243181577964387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279583944927495454385309591 419375917391243181577964387)
              ·
                refine ⟨629063876086864772366946581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419375917391243181577964387 629063876086864772366946581)
                ·
                  refine ⟨29487369191571786204700621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 629063876086864772366946581 29487369191571786204700621)
                  ·
                    refine ⟨11057763446839419826762733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29487369191571786204700621 11057763446839419826762733)
                    ·
                      refine ⟨4146661292564782435036025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057763446839419826762733 4146661292564782435036025)
                      ·
                        rfl

theorem cell23_8075594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 6, 3, 3].length) (baseStart_8075594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075594 prefixEnd_8075594 := by exact prefixLift 8075594
  have htrace : WordTrace (prefixWord ++ tailWord_8075594) baseStart_8075594 baseEnd_8075594 := by
    simpa [prefixWord, tailWord_8075594, baseEnd_8075594] using wordTrace_append hprefix tailTrace_8075594
  have hstable : (prefixWord ++ tailWord_8075594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075594).length < 2 ^ (prefixWord ++ tailWord_8075594).sum := by decide
  have hdescent : baseEnd_8075594 < baseStart_8075594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075618 : List Nat := [3, 3, 2, 1, 1, 3, 1, 4, 5]
def baseStart_8075618 : Nat := 118140960795 + 8075618 * 2 ^ 59
def prefixEnd_8075618 : Nat := 4983230072969 + 3 ^ 40 * 8075618 * 2
def baseEnd_8075618 : Nat := 460741512900054482348435

theorem tailTrace_8075618 : CollatzResearch.WordTrace tailWord_8075618 prefixEnd_8075618 460741512900054482348435 := by
  unfold tailWord_8075618
  simp only [CollatzResearch.WordTrace]
  refine ⟨73635496514355666648832877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196361324038281777730221005 73635496514355666648832877)
  ·
    refine ⟨27613311192883374993312329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73635496514355666648832877 27613311192883374993312329)
    ·
      refine ⟨20709983394662531244984247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27613311192883374993312329 20709983394662531244984247)
      ·
        refine ⟨31064975091993796867476371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20709983394662531244984247 31064975091993796867476371)
        ·
          refine ⟨46597462637990695301214557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31064975091993796867476371 46597462637990695301214557)
          ·
            refine ⟨17474048489246510737955459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46597462637990695301214557 17474048489246510737955459)
            ·
              refine ⟨26211072733869766106933189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17474048489246510737955459 26211072733869766106933189)
              ·
                refine ⟨4914576137600581145049973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26211072733869766106933189 4914576137600581145049973)
                ·
                  refine ⟨460741512900054482348435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4914576137600581145049973 460741512900054482348435)
                  ·
                    rfl

theorem cell23_8075618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_8075618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075618 prefixEnd_8075618 := by exact prefixLift 8075618
  have htrace : WordTrace (prefixWord ++ tailWord_8075618) baseStart_8075618 baseEnd_8075618 := by
    simpa [prefixWord, tailWord_8075618, baseEnd_8075618] using wordTrace_append hprefix tailTrace_8075618
  have hstable : (prefixWord ++ tailWord_8075618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075618).length < 2 ^ (prefixWord ++ tailWord_8075618).sum := by decide
  have hdescent : baseEnd_8075618 < baseStart_8075618 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075621 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 2, 5, 2]
def baseStart_8075621 : Nat := 118140960795 + 8075621 * 2 ^ 59
def prefixEnd_8075621 : Nat := 4983230072969 + 3 ^ 40 * 8075621 * 2
def baseEnd_8075621 : Nat := 4146675156542453829398401

theorem tailTrace_8075621 : CollatzResearch.WordTrace tailWord_8075621 prefixEnd_8075621 4146675156542453829398401 := by
  unfold tailWord_8075621
  simp only [CollatzResearch.WordTrace]
  refine ⟨294542095476411798107690717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196361396984274532071793811 294542095476411798107690717)
  ·
    refine ⟨110453285803654424290384019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294542095476411798107690717 110453285803654424290384019)
    ·
      refine ⟨165679928705481636435576029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110453285803654424290384019 165679928705481636435576029)
      ·
        refine ⟨62129973264555613663341011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165679928705481636435576029 62129973264555613663341011)
        ·
          refine ⟨93194959896833420495011517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62129973264555613663341011 93194959896833420495011517)
          ·
            refine ⟨34948109961312532685629319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93194959896833420495011517 34948109961312532685629319)
            ·
              refine ⟨52422164941968799028443979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34948109961312532685629319 52422164941968799028443979)
              ·
                refine ⟨78633247412953198542665969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52422164941968799028443979 78633247412953198542665969)
                ·
                  refine ⟨58974935559714898906999477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78633247412953198542665969 58974935559714898906999477)
                  ·
                    refine ⟨5528900208723271772531201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58974935559714898906999477 5528900208723271772531201)
                    ·
                      refine ⟨4146675156542453829398401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528900208723271772531201 4146675156542453829398401)
                      ·
                        rfl

theorem cell23_8075621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_8075621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075621 prefixEnd_8075621 := by exact prefixLift 8075621
  have htrace : WordTrace (prefixWord ++ tailWord_8075621) baseStart_8075621 baseEnd_8075621 := by
    simpa [prefixWord, tailWord_8075621, baseEnd_8075621] using wordTrace_append hprefix tailTrace_8075621
  have hstable : (prefixWord ++ tailWord_8075621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075621).length < 2 ^ (prefixWord ++ tailWord_8075621).sum := by decide
  have hdescent : baseEnd_8075621 < baseStart_8075621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075651 : List Nat := [1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 4]
def baseStart_8075651 : Nat := 118140960795 + 8075651 * 2 ^ 59
def prefixEnd_8075651 : Nat := 4983230072969 + 3 ^ 40 * 8075651 * 2
def baseEnd_8075651 : Nat := 4146690560962088712023263

theorem tailTrace_8075651 : CollatzResearch.WordTrace tailWord_8075651 prefixEnd_8075651 4146690560962088712023263 := by
  unfold tailWord_8075651
  simp only [CollatzResearch.WordTrace]
  refine ⟨294543189666303113231282807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196362126444202075487521871 294543189666303113231282807)
  ·
    refine ⟨441814784499454669846924211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294543189666303113231282807 441814784499454669846924211)
    ·
      refine ⟨662722176749182004770386317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441814784499454669846924211 662722176749182004770386317)
      ·
        refine ⟨248520816280943251788894869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662722176749182004770386317 248520816280943251788894869)
        ·
          refine ⟨11649413263169214927604447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 248520816280943251788894869 11649413263169214927604447)
          ·
            refine ⟨17474119894753822391406671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11649413263169214927604447 17474119894753822391406671)
            ·
              refine ⟨26211179842130733587110007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17474119894753822391406671 26211179842130733587110007)
              ·
                refine ⟨39316769763196100380665011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26211179842130733587110007 39316769763196100380665011)
                ·
                  refine ⟨58975154644794150570997517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39316769763196100380665011 58975154644794150570997517)
                  ·
                    refine ⟨22115682991797806464124069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58975154644794150570997517 22115682991797806464124069)
                    ·
                      refine ⟨4146690560962088712023263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22115682991797806464124069 4146690560962088712023263)
                      ·
                        rfl

theorem cell23_8075651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_8075651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075651 prefixEnd_8075651 := by exact prefixLift 8075651
  have htrace : WordTrace (prefixWord ++ tailWord_8075651) baseStart_8075651 baseEnd_8075651 := by
    simpa [prefixWord, tailWord_8075651, baseEnd_8075651] using wordTrace_append hprefix tailTrace_8075651
  have hstable : (prefixWord ++ tailWord_8075651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075651).length < 2 ^ (prefixWord ++ tailWord_8075651).sum := by decide
  have hdescent : baseEnd_8075651 < baseStart_8075651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075671 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 3]
def baseStart_8075671 : Nat := 118140960795 + 8075671 * 2 ^ 59
def prefixEnd_8075671 : Nat := 4983230072969 + 3 ^ 40 * 8075671 * 2
def baseEnd_8075671 : Nat := 4146700830575178633773171

theorem tailTrace_8075671 : CollatzResearch.WordTrace tailWord_8075671 prefixEnd_8075671 4146700830575178633773171 := by
  unfold tailWord_8075671
  simp only [CollatzResearch.WordTrace]
  refine ⟨294543919126230656647010867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196362612750820437764673911 294543919126230656647010867)
  ·
    refine ⟨441815878689345984970516301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294543919126230656647010867 441815878689345984970516301)
    ·
      refine ⟨165680954508504744363943613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441815878689345984970516301 165680954508504744363943613)
      ·
        refine ⟨62130357940689279136478855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165680954508504744363943613 62130357940689279136478855)
        ·
          refine ⟨93195536911033918704718283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62130357940689279136478855 93195536911033918704718283)
          ·
            refine ⟨139793305366550878057077425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93195536911033918704718283 139793305366550878057077425)
            ·
              refine ⟨104844979024913158542808069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139793305366550878057077425 104844979024913158542808069)
              ·
                refine ⟨19658433567171217226776513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104844979024913158542808069 19658433567171217226776513)
                ·
                  refine ⟨14743825175378412920082385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19658433567171217226776513 14743825175378412920082385)
                  ·
                    refine ⟨11057868881533809690061789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14743825175378412920082385 11057868881533809690061789)
                    ·
                      refine ⟨4146700830575178633773171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057868881533809690061789 4146700830575178633773171)
                      ·
                        rfl

theorem cell23_8075671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_8075671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075671 prefixEnd_8075671 := by exact prefixLift 8075671
  have htrace : WordTrace (prefixWord ++ tailWord_8075671) baseStart_8075671 baseEnd_8075671 := by
    simpa [prefixWord, tailWord_8075671, baseEnd_8075671] using wordTrace_append hprefix tailTrace_8075671
  have hstable : (prefixWord ++ tailWord_8075671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075671).length < 2 ^ (prefixWord ++ tailWord_8075671).sum := by decide
  have hdescent : baseEnd_8075671 < baseStart_8075671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075688 : List Nat := [2, 1, 6, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_8075688 : Nat := 118140960795 + 8075688 * 2 ^ 59
def prefixEnd_8075688 : Nat := 4983230072969 + 3 ^ 40 * 8075688 * 2
def baseEnd_8075688 : Nat := 4146709559746305067260593

theorem tailTrace_8075688 : CollatzResearch.WordTrace tailWord_8075688 prefixEnd_8075688 4146709559746305067260593 := by
  unfold tailWord_8075688
  simp only [CollatzResearch.WordTrace]
  refine ⟨147272269583584534275189859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196363026111446045700253145 147272269583584534275189859)
  ·
    refine ⟨220908404375376801412784789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147272269583584534275189859 220908404375376801412784789)
    ·
      refine ⟨10355081455095787566224287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220908404375376801412784789 10355081455095787566224287)
      ·
        refine ⟨15532622182643681349336431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10355081455095787566224287 15532622182643681349336431)
        ·
          refine ⟨23298933273965522024004647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15532622182643681349336431 23298933273965522024004647)
          ·
            refine ⟨34948399910948283036006971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23298933273965522024004647 34948399910948283036006971)
            ·
              refine ⟨52422599866422424554010457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34948399910948283036006971 52422599866422424554010457)
              ·
                refine ⟨39316949899816818415507843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52422599866422424554010457 39316949899816818415507843)
                ·
                  refine ⟨58975424849725227623261765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39316949899816818415507843 58975424849725227623261765)
                  ·
                    refine ⟨11057892159323480179361581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58975424849725227623261765 11057892159323480179361581)
                    ·
                      refine ⟨4146709559746305067260593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11057892159323480179361581 4146709559746305067260593)
                      ·
                        rfl

theorem cell23_8075688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_8075688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075688 prefixEnd_8075688 := by exact prefixLift 8075688
  have htrace : WordTrace (prefixWord ++ tailWord_8075688) baseStart_8075688 baseEnd_8075688 := by
    simpa [prefixWord, tailWord_8075688, baseEnd_8075688] using wordTrace_append hprefix tailTrace_8075688
  have hstable : (prefixWord ++ tailWord_8075688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075688).length < 2 ^ (prefixWord ++ tailWord_8075688).sum := by decide
  have hdescent : baseEnd_8075688 < baseStart_8075688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075721 : List Nat := [1, 2, 1, 1, 2, 1, 6, 3, 1, 5]
def baseStart_8075721 : Nat := 118140960795 + 8075721 * 2 ^ 59
def prefixEnd_8075721 : Nat := 4983230072969 + 3 ^ 40 * 8075721 * 2
def baseEnd_8075721 : Nat := 1382242168202634479382647

theorem tailTrace_8075721 : CollatzResearch.WordTrace tailWord_8075721 prefixEnd_8075721 1382242168202634479382647 := by
  unfold tailWord_8075721
  simp only [CollatzResearch.WordTrace]
  refine ⟨294545742776049515186331017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196363828517366343457554011 294545742776049515186331017)
  ·
    refine ⟨220909307082037136389748263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294545742776049515186331017 220909307082037136389748263)
    ·
      refine ⟨331363960623055704584622395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220909307082037136389748263 331363960623055704584622395)
      ·
        refine ⟨497045940934583556876933593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331363960623055704584622395 497045940934583556876933593)
        ·
          refine ⟨372784455700937667657700195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497045940934583556876933593 372784455700937667657700195)
          ·
            refine ⟨559176683551406501486550293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372784455700937667657700195 559176683551406501486550293)
            ·
              refine ⟨26211407041472179757182045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 559176683551406501486550293 26211407041472179757182045)
              ·
                refine ⟨9829277640552067408943267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26211407041472179757182045 9829277640552067408943267)
                ·
                  refine ⟨14743916460828101113414901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9829277640552067408943267 14743916460828101113414901)
                  ·
                    refine ⟨1382242168202634479382647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14743916460828101113414901 1382242168202634479382647)
                    ·
                      rfl

theorem cell23_8075721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 5].length) (baseStart_8075721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075721 prefixEnd_8075721 := by exact prefixLift 8075721
  have htrace : WordTrace (prefixWord ++ tailWord_8075721) baseStart_8075721 baseEnd_8075721 := by
    simpa [prefixWord, tailWord_8075721, baseEnd_8075721] using wordTrace_append hprefix tailTrace_8075721
  have hstable : (prefixWord ++ tailWord_8075721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075721).length < 2 ^ (prefixWord ++ tailWord_8075721).sum := by decide
  have hdescent : baseEnd_8075721 < baseStart_8075721 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075751 : List Nat := [1, 1, 5, 2, 1, 1, 2, 3, 1, 6]
def baseStart_8075751 : Nat := 118140960795 + 8075751 * 2 ^ 59
def prefixEnd_8075751 : Nat := 4983230072969 + 3 ^ 40 * 8075751 * 2
def baseEnd_8075751 : Nat := 1382247303009179440257601

theorem tailTrace_8075751 : CollatzResearch.WordTrace tailWord_8075751 prefixEnd_8075751 1382247303009179440257601 := by
  unfold tailWord_8075751
  simp only [CollatzResearch.WordTrace]
  refine ⟨294546836965940830309923107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196364557977293886873282071 294546836965940830309923107)
  ·
    refine ⟨441820255448911245464884661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294546836965940830309923107 441820255448911245464884661)
    ·
      refine ⟨41420648948335429262332937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441820255448911245464884661 41420648948335429262332937)
      ·
        refine ⟨31065486711251571946749703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41420648948335429262332937 31065486711251571946749703)
        ·
          refine ⟨46598230066877357920124555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31065486711251571946749703 46598230066877357920124555)
          ·
            refine ⟨69897345100316036880186833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46598230066877357920124555 69897345100316036880186833)
            ·
              refine ⟨52423008825237027660140125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69897345100316036880186833 52423008825237027660140125)
              ·
                refine ⟨19658628309463885372552547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52423008825237027660140125 19658628309463885372552547)
                ·
                  refine ⟨29487942464195828058828821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19658628309463885372552547 29487942464195828058828821)
                  ·
                    refine ⟨1382247303009179440257601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29487942464195828058828821 1382247303009179440257601)
                    ·
                      rfl

theorem cell23_8075751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_8075751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075751 prefixEnd_8075751 := by exact prefixLift 8075751
  have htrace : WordTrace (prefixWord ++ tailWord_8075751) baseStart_8075751 baseEnd_8075751 := by
    simpa [prefixWord, tailWord_8075751, baseEnd_8075751] using wordTrace_append hprefix tailTrace_8075751
  have hstable : (prefixWord ++ tailWord_8075751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075751).length < 2 ^ (prefixWord ++ tailWord_8075751).sum := by decide
  have hdescent : baseEnd_8075751 < baseStart_8075751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075758 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_8075758 : Nat := 118140960795 + 8075758 * 2 ^ 59
def prefixEnd_8075758 : Nat := 4983230072969 + 3 ^ 40 * 8075758 * 2
def baseEnd_8075758 : Nat := 4146745503392119793385271

theorem tailTrace_8075758 : CollatzResearch.WordTrace tailWord_8075758 prefixEnd_8075758 4146745503392119793385271 := by
  unfold tailWord_8075758
  simp only [CollatzResearch.WordTrace]
  refine ⟨36818386534614433813178491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196364728184610313670285285 36818386534614433813178491)
  ·
    refine ⟨55227579801921650719767737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36818386534614433813178491 55227579801921650719767737)
    ·
      refine ⟨41420684851441238039825803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55227579801921650719767737 41420684851441238039825803)
      ·
        refine ⟨62131027277161857059738705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41420684851441238039825803 62131027277161857059738705)
        ·
          refine ⟨46598270457871392794804029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62131027277161857059738705 46598270457871392794804029)
          ·
            refine ⟨17474351421701772298051511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46598270457871392794804029 17474351421701772298051511)
            ·
              refine ⟨26211527132552658447077267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17474351421701772298051511 26211527132552658447077267)
              ·
                refine ⟨39317290698828987670615901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26211527132552658447077267 39317290698828987670615901)
                ·
                  refine ⟨14743984012060870376480963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39317290698828987670615901 14743984012060870376480963)
                  ·
                    refine ⟨22115976018091305564721445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14743984012060870376480963 22115976018091305564721445)
                    ·
                      refine ⟨4146745503392119793385271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22115976018091305564721445 4146745503392119793385271)
                      ·
                        rfl

theorem cell23_8075758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_8075758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075758 prefixEnd_8075758 := by exact prefixLift 8075758
  have htrace : WordTrace (prefixWord ++ tailWord_8075758) baseStart_8075758 baseEnd_8075758 := by
    simpa [prefixWord, tailWord_8075758, baseEnd_8075758] using wordTrace_append hprefix tailTrace_8075758
  have hstable : (prefixWord ++ tailWord_8075758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075758).length < 2 ^ (prefixWord ++ tailWord_8075758).sum := by decide
  have hdescent : baseEnd_8075758 < baseStart_8075758 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075762 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 2, 3, 2]
def baseStart_8075762 : Nat := 118140960795 + 8075762 * 2 ^ 59
def prefixEnd_8075762 : Nat := 4983230072969 + 3 ^ 40 * 8075762 * 2
def baseEnd_8075762 : Nat := 4146747557314737777735253

theorem tailTrace_8075762 : CollatzResearch.WordTrace tailWord_8075762 prefixEnd_8075762 4146747557314737777735253 := by
  unfold tailWord_8075762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73636809542225244797143385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196364825445933986125715693 73636809542225244797143385)
  ·
    refine ⟨55227607156668933597857539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73636809542225244797143385 55227607156668933597857539)
    ·
      refine ⟨82841410735003400396786309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55227607156668933597857539 82841410735003400396786309)
      ·
        refine ⟨15532764512813137574397433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82841410735003400396786309 15532764512813137574397433)
        ·
          refine ⟨11649573384609853180798075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15532764512813137574397433 11649573384609853180798075)
          ·
            refine ⟨17474360076914779771197113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11649573384609853180798075 17474360076914779771197113)
            ·
              refine ⟨13105770057686084828397835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17474360076914779771197113 13105770057686084828397835)
              ·
                refine ⟨19658655086529127242596753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13105770057686084828397835 19658655086529127242596753)
                ·
                  refine ⟨14743991314896845431947565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19658655086529127242596753 14743991314896845431947565)
                  ·
                    refine ⟨5528996743086317036980337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14743991314896845431947565 5528996743086317036980337)
                    ·
                      refine ⟨4146747557314737777735253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5528996743086317036980337 4146747557314737777735253)
                      ·
                        rfl

theorem cell23_8075762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_8075762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075762 prefixEnd_8075762 := by exact prefixLift 8075762
  have htrace : WordTrace (prefixWord ++ tailWord_8075762) baseStart_8075762 baseEnd_8075762 := by
    simpa [prefixWord, tailWord_8075762, baseEnd_8075762] using wordTrace_append hprefix tailTrace_8075762
  have hstable : (prefixWord ++ tailWord_8075762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075762).length < 2 ^ (prefixWord ++ tailWord_8075762).sum := by decide
  have hdescent : baseEnd_8075762 < baseStart_8075762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075848 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 3, 4, 2]
def baseStart_8075848 : Nat := 118140960795 + 8075848 * 2 ^ 59
def prefixEnd_8075848 : Nat := 4983230072969 + 3 ^ 40 * 8075848 * 2
def baseEnd_8075848 : Nat := 4146791716651024441259857

theorem tailTrace_8075848 : CollatzResearch.WordTrace tailWord_8075848 prefixEnd_8075848 4146791716651024441259857 := by
  unfold tailWord_8075848
  simp only [CollatzResearch.WordTrace]
  refine ⟨147275187423294707938102099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196366916564392943917469465 147275187423294707938102099)
  ·
    refine ⟨220912781134942061907153149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147275187423294707938102099 220912781134942061907153149)
    ·
      refine ⟨82842292925603273215182431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220912781134942061907153149 82842292925603273215182431)
      ·
        refine ⟨124263439388404909822773647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82842292925603273215182431 124263439388404909822773647)
        ·
          refine ⟨186395159082607364734160471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124263439388404909822773647 186395159082607364734160471)
          ·
            refine ⟨279592738623911047101240707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186395159082607364734160471 279592738623911047101240707)
            ·
              refine ⟨419389107935866570651861061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279592738623911047101240707 419389107935866570651861061)
              ·
                refine ⟨78635457737974981997223949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419389107935866570651861061 78635457737974981997223949)
                ·
                  refine ⟨29488296651740618248958981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78635457737974981997223949 29488296651740618248958981)
                  ·
                    refine ⟨5529055622201365921679809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29488296651740618248958981 5529055622201365921679809)
                    ·
                      refine ⟨4146791716651024441259857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529055622201365921679809 4146791716651024441259857)
                      ·
                        rfl

theorem cell23_8075848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 3, 4, 2].length) (baseStart_8075848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075848 prefixEnd_8075848 := by exact prefixLift 8075848
  have htrace : WordTrace (prefixWord ++ tailWord_8075848) baseStart_8075848 baseEnd_8075848 := by
    simpa [prefixWord, tailWord_8075848, baseEnd_8075848] using wordTrace_append hprefix tailTrace_8075848
  have hstable : (prefixWord ++ tailWord_8075848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075848).length < 2 ^ (prefixWord ++ tailWord_8075848).sum := by decide
  have hdescent : baseEnd_8075848 < baseStart_8075848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075851 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 3]
def baseStart_8075851 : Nat := 118140960795 + 8075851 * 2 ^ 59
def prefixEnd_8075851 : Nat := 4983230072969 + 3 ^ 40 * 8075851 * 2
def baseEnd_8075851 : Nat := 4146793257092987929522343

theorem tailTrace_8075851 : CollatzResearch.WordTrace tailWord_8075851 prefixEnd_8075851 4146793257092987929522343 := by
  unfold tailWord_8075851
  simp only [CollatzResearch.WordTrace]
  refine ⟨294550484265578547388563407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196366989510385698259042271 294550484265578547388563407)
  ·
    refine ⟨441825726398367821082845111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294550484265578547388563407 441825726398367821082845111)
    ·
      refine ⟨662738589597551731624267667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441825726398367821082845111 662738589597551731624267667)
      ·
        refine ⟨994107884396327597436401501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662738589597551731624267667 994107884396327597436401501)
        ·
          refine ⟨372790456648622849038650563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 994107884396327597436401501 372790456648622849038650563)
          ·
            refine ⟨559185684972934273557975845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372790456648622849038650563 559185684972934273557975845)
            ·
              refine ⟨104847315932425176292120471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 559185684972934273557975845 104847315932425176292120471)
              ·
                refine ⟨157270973898637764438180707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104847315932425176292120471 157270973898637764438180707)
                ·
                  refine ⟨235906460847956646657271061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157270973898637764438180707 235906460847956646657271061)
                  ·
                    refine ⟨11058115352247967812059581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 235906460847956646657271061 11058115352247967812059581)
                    ·
                      refine ⟨4146793257092987929522343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11058115352247967812059581 4146793257092987929522343)
                      ·
                        rfl

theorem cell23_8075851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 6, 3].length) (baseStart_8075851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075851 prefixEnd_8075851 := by exact prefixLift 8075851
  have htrace : WordTrace (prefixWord ++ tailWord_8075851) baseStart_8075851 baseEnd_8075851 := by
    simpa [prefixWord, tailWord_8075851, baseEnd_8075851] using wordTrace_append hprefix tailTrace_8075851
  have hstable : (prefixWord ++ tailWord_8075851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075851).length < 2 ^ (prefixWord ++ tailWord_8075851).sum := by decide
  have hdescent : baseEnd_8075851 < baseStart_8075851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075918 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_8075918 : Nat := 118140960795 + 8075918 * 2 ^ 59
def prefixEnd_8075918 : Nat := 4983230072969 + 3 ^ 40 * 8075918 * 2
def baseEnd_8075918 : Nat := 1382275886765613055794845

theorem tailTrace_8075918 : CollatzResearch.WordTrace tailWord_8075918 prefixEnd_8075918 1382275886765613055794845 := by
  unfold tailWord_8075918
  simp only [CollatzResearch.WordTrace]
  refine ⟨36819115994541977228906551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196368618637557211887501605 36819115994541977228906551)
  ·
    refine ⟨55228673991812965843359827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36819115994541977228906551 55228673991812965843359827)
    ·
      refine ⟨82843010987719448765039741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55228673991812965843359827 82843010987719448765039741)
      ·
        refine ⟨31066129120394793286889903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82843010987719448765039741 31066129120394793286889903)
        ·
          refine ⟨46599193680592189930334855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31066129120394793286889903 46599193680592189930334855)
          ·
            refine ⟨69898790520888284895502283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46599193680592189930334855 69898790520888284895502283)
            ·
              refine ⟨104848185781332427343253425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69898790520888284895502283 104848185781332427343253425)
              ·
                refine ⟨78636139335999320507440069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104848185781332427343253425 78636139335999320507440069)
                ·
                  refine ⟨14744276125499872595145013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78636139335999320507440069 14744276125499872595145013)
                  ·
                    refine ⟨1382275886765613055794845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14744276125499872595145013 1382275886765613055794845)
                    ·
                      rfl

theorem cell23_8075918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_8075918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075918 prefixEnd_8075918 := by exact prefixLift 8075918
  have htrace : WordTrace (prefixWord ++ tailWord_8075918) baseStart_8075918 baseEnd_8075918 := by
    simpa [prefixWord, tailWord_8075918, baseEnd_8075918] using wordTrace_append hprefix tailTrace_8075918
  have hstable : (prefixWord ++ tailWord_8075918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075918).length < 2 ^ (prefixWord ++ tailWord_8075918).sum := by decide
  have hdescent : baseEnd_8075918 < baseStart_8075918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075972 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_8075972 : Nat := 118140960795 + 8075972 * 2 ^ 59
def prefixEnd_8075972 : Nat := 4983230072969 + 3 ^ 40 * 8075972 * 2
def baseEnd_8075972 : Nat := 4146855388252181956109287

theorem tailTrace_8075972 : CollatzResearch.WordTrace tailWord_8075972 prefixEnd_8075972 4146855388252181956109287 := by
  unfold tailWord_8075972
  simp only [CollatzResearch.WordTrace]
  refine ⟨147277448749070092526859085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196369931665426790035812113 147277448749070092526859085)
  ·
    refine ⟨55229043280901284697572157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147277448749070092526859085 55229043280901284697572157)
    ·
      refine ⟨20710891230337981761589559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55229043280901284697572157 20710891230337981761589559)
      ·
        refine ⟨31066336845506972642384339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20710891230337981761589559 31066336845506972642384339)
        ·
          refine ⟨46599505268260458963576509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31066336845506972642384339 46599505268260458963576509)
          ·
            refine ⟨17474814475597672111341191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46599505268260458963576509 17474814475597672111341191)
            ·
              refine ⟨26212221713396508167011787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17474814475597672111341191 26212221713396508167011787)
              ·
                refine ⟨39318332570094762250517681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26212221713396508167011787 39318332570094762250517681)
                ·
                  refine ⟨29488749427571071687888261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39318332570094762250517681 29488749427571071687888261)
                  ·
                    refine ⟨5529140517669575941479049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29488749427571071687888261 5529140517669575941479049)
                    ·
                      refine ⟨4146855388252181956109287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529140517669575941479049 4146855388252181956109287)
                      ·
                        rfl

theorem cell23_8075972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_8075972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075972 prefixEnd_8075972 := by exact prefixLift 8075972
  have htrace : WordTrace (prefixWord ++ tailWord_8075972) baseStart_8075972 baseEnd_8075972 := by
    simpa [prefixWord, tailWord_8075972, baseEnd_8075972] using wordTrace_append hprefix tailTrace_8075972
  have hstable : (prefixWord ++ tailWord_8075972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075972).length < 2 ^ (prefixWord ++ tailWord_8075972).sum := by decide
  have hdescent : baseEnd_8075972 < baseStart_8075972 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075989 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 4]
def baseStart_8075989 : Nat := 118140960795 + 8075989 * 2 ^ 59
def prefixEnd_8075989 : Nat := 4983230072969 + 3 ^ 40 * 8075989 * 2
def baseEnd_8075989 : Nat := 4146864117423308389596709

theorem tailTrace_8075989 : CollatzResearch.WordTrace tailWord_8075989 prefixEnd_8075989 4146864117423308389596709 := by
  unfold tailWord_8075989
  simp only [CollatzResearch.WordTrace]
  refine ⟨294555517539078596957087021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196370345026052397971391347 294555517539078596957087021)
  ·
    refine ⟨110458319077154473858907633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294555517539078596957087021 110458319077154473858907633)
    ·
      refine ⟨82843739307865855394180725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110458319077154473858907633 82843739307865855394180725)
      ·
        refine ⟨7766600560112423943204443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82843739307865855394180725 7766600560112423943204443)
        ·
          refine ⟨11649900840168635914806665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7766600560112423943204443 11649900840168635914806665)
          ·
            refine ⟨8737425630126476936104999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11649900840168635914806665 8737425630126476936104999)
            ·
              refine ⟨13106138445189715404157499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8737425630126476936104999 13106138445189715404157499)
              ·
                refine ⟨19659207667784573106236249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13106138445189715404157499 19659207667784573106236249)
                ·
                  refine ⟨14744405750838429829677187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19659207667784573106236249 14744405750838429829677187)
                  ·
                    refine ⟨22116608626257644744515781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14744405750838429829677187 22116608626257644744515781)
                    ·
                      refine ⟨4146864117423308389596709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22116608626257644744515781 4146864117423308389596709)
                      ·
                        rfl

theorem cell23_8075989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_8075989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075989 prefixEnd_8075989 := by exact prefixLift 8075989
  have htrace : WordTrace (prefixWord ++ tailWord_8075989) baseStart_8075989 baseEnd_8075989 := by
    simpa [prefixWord, tailWord_8075989, baseEnd_8075989] using wordTrace_append hprefix tailTrace_8075989
  have hstable : (prefixWord ++ tailWord_8075989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075989).length < 2 ^ (prefixWord ++ tailWord_8075989).sum := by decide
  have hdescent : baseEnd_8075989 < baseStart_8075989 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8075992 : List Nat := [2, 1, 2, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_8075992 : Nat := 118140960795 + 8075992 * 2 ^ 59
def prefixEnd_8075992 : Nat := 4983230072969 + 3 ^ 40 * 8075992 * 2
def baseEnd_8075992 : Nat := 4146865657865271877859195

theorem tailTrace_8075992 : CollatzResearch.WordTrace tailWord_8075992 prefixEnd_8075992 4146865657865271877859195 := by
  unfold tailWord_8075992
  simp only [CollatzResearch.WordTrace]
  refine ⟨147277813479033864234723115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196370417972045152312964153 147277813479033864234723115)
  ·
    refine ⟨220916720218550796352084673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147277813479033864234723115 220916720218550796352084673)
    ·
      refine ⟨165687540163913097264063505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220916720218550796352084673 165687540163913097264063505)
      ·
        refine ⟨124265655122934822948047629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165687540163913097264063505 124265655122934822948047629)
        ·
          refine ⟨46599620671100558605517861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124265655122934822948047629 46599620671100558605517861)
          ·
            refine ⟨8737428875831354738534599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46599620671100558605517861 8737428875831354738534599)
            ·
              refine ⟨13106143313747032107801899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8737428875831354738534599 13106143313747032107801899)
              ·
                refine ⟨19659214970620548161702849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13106143313747032107801899 19659214970620548161702849)
                ·
                  refine ⟨14744411227965411121277137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19659214970620548161702849 14744411227965411121277137)
                  ·
                    refine ⟨11058308420974058340957853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14744411227965411121277137 11058308420974058340957853)
                    ·
                      refine ⟨4146865657865271877859195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11058308420974058340957853 4146865657865271877859195)
                      ·
                        rfl

theorem cell23_8075992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_8075992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8075992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8075992 prefixEnd_8075992 := by exact prefixLift 8075992
  have htrace : WordTrace (prefixWord ++ tailWord_8075992) baseStart_8075992 baseEnd_8075992 := by
    simpa [prefixWord, tailWord_8075992, baseEnd_8075992] using wordTrace_append hprefix tailTrace_8075992
  have hstable : (prefixWord ++ tailWord_8075992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8075992).length < 2 ^ (prefixWord ++ tailWord_8075992).sum := by decide
  have hdescent : baseEnd_8075992 < baseStart_8075992 := by decide
  rcases family_descends (prefixWord ++ tailWord_8075992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076065 : List Nat := [1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 5]
def baseStart_8076065 : Nat := 118140960795 + 8076065 * 2 ^ 59
def prefixEnd_8076065 : Nat := 4983230072969 + 3 ^ 40 * 8076065 * 2
def baseEnd_8076065 : Nat := 4146903141953050092246359

theorem tailTrace_8076065 : CollatzResearch.WordTrace tailWord_8076065 prefixEnd_8076065 4146903141953050092246359 := by
  unfold tailWord_8076065
  simp only [CollatzResearch.WordTrace]
  refine ⟨294558289486803261936853649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196372192991202174624569099 294558289486803261936853649)
  ·
    refine ⟨220918717115102446452640237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294558289486803261936853649 220918717115102446452640237)
    ·
      refine ⟨82844518918163417419740089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220918717115102446452640237 82844518918163417419740089)
      ·
        refine ⟨62133389188622563064805067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82844518918163417419740089 62133389188622563064805067)
        ·
          refine ⟨93200083782933844597207601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62133389188622563064805067 93200083782933844597207601)
          ·
            refine ⟨69900062837200383447905701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93200083782933844597207601 69900062837200383447905701)
            ·
              refine ⟨13106261781975071896482319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69900062837200383447905701 13106261781975071896482319)
              ·
                refine ⟨19659392672962607844723479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13106261781975071896482319 19659392672962607844723479)
                ·
                  refine ⟨29489089009443911767085219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19659392672962607844723479 29489089009443911767085219)
                  ·
                    refine ⟨44233633514165867650627829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29489089009443911767085219 44233633514165867650627829)
                    ·
                      refine ⟨4146903141953050092246359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44233633514165867650627829 4146903141953050092246359)
                      ·
                        rfl

theorem cell23_8076065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_8076065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076065 prefixEnd_8076065 := by exact prefixLift 8076065
  have htrace : WordTrace (prefixWord ++ tailWord_8076065) baseStart_8076065 baseEnd_8076065 := by
    simpa [prefixWord, tailWord_8076065, baseEnd_8076065] using wordTrace_append hprefix tailTrace_8076065
  have hstable : (prefixWord ++ tailWord_8076065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076065).length < 2 ^ (prefixWord ++ tailWord_8076065).sum := by decide
  have hdescent : baseEnd_8076065 < baseStart_8076065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076072 : List Nat := [2, 1, 5, 1, 1, 1, 2, 4, 2, 4]
def baseStart_8076072 : Nat := 118140960795 + 8076072 * 2 ^ 59
def prefixEnd_8076072 : Nat := 4983230072969 + 3 ^ 40 * 8076072 * 2
def baseEnd_8076072 : Nat := 1382302245439210521619609

theorem tailTrace_8076072 : CollatzResearch.WordTrace tailWord_8076072 prefixEnd_8076072 1382302245439210521619609 := by
  unfold tailWord_8076072
  simp only [CollatzResearch.WordTrace]
  refine ⟨147279272398888951066179235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196372363198518601421572313 147279272398888951066179235)
  ·
    refine ⟨220918908598333426599268853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147279272398888951066179235 220918908598333426599268853)
    ·
      refine ⟨20711147681093758743681455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220918908598333426599268853 20711147681093758743681455)
      ·
        refine ⟨31066721521640638115522183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20711147681093758743681455 31066721521640638115522183)
        ·
          refine ⟨46600082282460957173283275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31066721521640638115522183 46600082282460957173283275)
          ·
            refine ⟨69900123423691435759924913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46600082282460957173283275 69900123423691435759924913)
            ·
              refine ⟨52425092567768576819943685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69900123423691435759924913 52425092567768576819943685)
              ·
                refine ⟨9829704856456608153739441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52425092567768576819943685 9829704856456608153739441)
                ·
                  refine ⟨7372278642342456115304581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9829704856456608153739441 7372278642342456115304581)
                  ·
                    refine ⟨1382302245439210521619609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7372278642342456115304581 1382302245439210521619609)
                    ·
                      rfl

theorem cell23_8076072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_8076072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076072 prefixEnd_8076072 := by exact prefixLift 8076072
  have htrace : WordTrace (prefixWord ++ tailWord_8076072) baseStart_8076072 baseEnd_8076072 := by
    simpa [prefixWord, tailWord_8076072, baseEnd_8076072] using wordTrace_append hprefix tailTrace_8076072
  have hstable : (prefixWord ++ tailWord_8076072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076072).length < 2 ^ (prefixWord ++ tailWord_8076072).sum := by decide
  have hdescent : baseEnd_8076072 < baseStart_8076072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076085 : List Nat := [1, 3, 3, 1, 3, 2, 2, 8]
def baseStart_8076085 : Nat := 118140960795 + 8076085 * 2 ^ 59
def prefixEnd_8076085 : Nat := 4983230072969 + 3 ^ 40 * 8076085 * 2
def baseEnd_8076085 : Nat := 153589385613560741259121

theorem tailTrace_8076085 : CollatzResearch.WordTrace tailWord_8076085 prefixEnd_8076085 153589385613560741259121 := by
  unfold tailWord_8076085
  simp only [CollatzResearch.WordTrace]
  refine ⟨294559018946730805352581709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196372679297820536901721139 294559018946730805352581709)
  ·
    refine ⟨110459632105024052007218141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294559018946730805352581709 110459632105024052007218141)
    ·
      refine ⟨41422362039384019502706803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110459632105024052007218141 41422362039384019502706803)
      ·
        refine ⟨62133543059076029254060205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41422362039384019502706803 62133543059076029254060205)
        ·
          refine ⟨23300078647153510970272577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62133543059076029254060205 23300078647153510970272577)
          ·
            refine ⟨17475058985365133227704433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23300078647153510970272577 17475058985365133227704433)
            ·
              refine ⟨13106294239023849920778325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17475058985365133227704433 13106294239023849920778325)
              ·
                refine ⟨153589385613560741259121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13106294239023849920778325 153589385613560741259121)
                ·
                  rfl

theorem cell23_8076085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 2, 8].length) (baseStart_8076085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076085 prefixEnd_8076085 := by exact prefixLift 8076085
  have htrace : WordTrace (prefixWord ++ tailWord_8076085) baseStart_8076085 baseEnd_8076085 := by
    simpa [prefixWord, tailWord_8076085, baseEnd_8076085] using wordTrace_append hprefix tailTrace_8076085
  have hstable : (prefixWord ++ tailWord_8076085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076085).length < 2 ^ (prefixWord ++ tailWord_8076085).sum := by decide
  have hdescent : baseEnd_8076085 < baseStart_8076085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076088 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_8076088 : Nat := 118140960795 + 8076088 * 2 ^ 59
def prefixEnd_8076088 : Nat := 4983230072969 + 3 ^ 40 * 8076088 * 2
def baseEnd_8076088 : Nat := 4146914952008103502258753

theorem tailTrace_8076088 : CollatzResearch.WordTrace tailWord_8076088 prefixEnd_8076088 4146914952008103502258753 := by
  unfold tailWord_8076088
  simp only [CollatzResearch.WordTrace]
  refine ⟨147279564182859968432470459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196372752243813291243293945 147279564182859968432470459)
  ·
    refine ⟨220919346274289952648705689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147279564182859968432470459 220919346274289952648705689)
    ·
      refine ⟨165689509705717464486529267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220919346274289952648705689 165689509705717464486529267)
      ·
        refine ⟨248534264558576196729793901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165689509705717464486529267 248534264558576196729793901)
        ·
          refine ⟨93200349209466073773672713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248534264558576196729793901 93200349209466073773672713)
          ·
            refine ⟨69900261907099555330254535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93200349209466073773672713 69900261907099555330254535)
            ·
              refine ⟨104850392860649332995381803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69900261907099555330254535 104850392860649332995381803)
              ·
                refine ⟨157275589290973999493072705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104850392860649332995381803 157275589290973999493072705)
                ·
                  refine ⟨117956691968230499619804529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157275589290973999493072705 117956691968230499619804529)
                  ·
                    refine ⟨88467518976172874714853397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117956691968230499619804529 88467518976172874714853397)
                    ·
                      refine ⟨4146914952008103502258753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88467518976172874714853397 4146914952008103502258753)
                      ·
                        rfl

theorem cell23_8076088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_8076088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076088 prefixEnd_8076088 := by exact prefixLift 8076088
  have htrace : WordTrace (prefixWord ++ tailWord_8076088) baseStart_8076088 baseEnd_8076088 := by
    simpa [prefixWord, tailWord_8076088, baseEnd_8076088] using wordTrace_append hprefix tailTrace_8076088
  have hstable : (prefixWord ++ tailWord_8076088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076088).length < 2 ^ (prefixWord ++ tailWord_8076088).sum := by decide
  have hdescent : baseEnd_8076088 < baseStart_8076088 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076109 : List Nat := [1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 4]
def baseStart_8076109 : Nat := 118140960795 + 8076109 * 2 ^ 59
def prefixEnd_8076109 : Nat := 4983230072969 + 3 ^ 40 * 8076109 * 2
def baseEnd_8076109 : Nat := 4146925735101847920096157

theorem tailTrace_8076109 : CollatzResearch.WordTrace tailWord_8076109 prefixEnd_8076109 4146925735101847920096157 := by
  unfold tailWord_8076109
  simp only [CollatzResearch.WordTrace]
  refine ⟨294559894298643857451455381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196373262865762571634303587 294559894298643857451455381)
  ·
    refine ⟨13807495045248930818036971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 294559894298643857451455381 13807495045248930818036971)
    ·
      refine ⟨20711242567873396227055457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13807495045248930818036971 20711242567873396227055457)
      ·
        refine ⟨15533431925905047170291593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20711242567873396227055457 15533431925905047170291593)
        ·
          refine ⟨11650073944428785377718695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15533431925905047170291593 11650073944428785377718695)
          ·
            refine ⟨17475110916643178066578043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650073944428785377718695 17475110916643178066578043)
            ·
              refine ⟨26212666374964767099867065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17475110916643178066578043 26212666374964767099867065)
              ·
                refine ⟨19659499781223575324900299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26212666374964767099867065 19659499781223575324900299)
                ·
                  refine ⟨29489249671835362987350449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19659499781223575324900299 29489249671835362987350449)
                  ·
                    refine ⟨22116937253876522240512837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29489249671835362987350449 22116937253876522240512837)
                    ·
                      refine ⟨4146925735101847920096157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22116937253876522240512837 4146925735101847920096157)
                      ·
                        rfl

theorem cell23_8076109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_8076109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076109 prefixEnd_8076109 := by exact prefixLift 8076109
  have htrace : WordTrace (prefixWord ++ tailWord_8076109) baseStart_8076109 baseEnd_8076109 := by
    simpa [prefixWord, tailWord_8076109, baseEnd_8076109] using wordTrace_append hprefix tailTrace_8076109
  have hstable : (prefixWord ++ tailWord_8076109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076109).length < 2 ^ (prefixWord ++ tailWord_8076109).sum := by decide
  have hdescent : baseEnd_8076109 < baseStart_8076109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076116 : List Nat := [2, 4, 1, 1, 4, 1, 3, 1, 1, 2, 3]
def baseStart_8076116 : Nat := 118140960795 + 8076116 * 2 ^ 59
def prefixEnd_8076116 : Nat := 4983230072969 + 3 ^ 40 * 8076116 * 2
def baseEnd_8076116 : Nat := 4146929329466429392708625

theorem tailTrace_8076116 : CollatzResearch.WordTrace tailWord_8076116 prefixEnd_8076116 4146929329466429392708625 := by
  unfold tailWord_8076116
  simp only [CollatzResearch.WordTrace]
  refine ⟨147280074804809248823480101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196373433073078998431306801 147280074804809248823480101)
  ·
    refine ⟨27615014025901734154402519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147280074804809248823480101 27615014025901734154402519)
    ·
      refine ⟨41422521038852601231603779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27615014025901734154402519 41422521038852601231603779)
      ·
        refine ⟨62133781558278901847405669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41422521038852601231603779 62133781558278901847405669)
        ·
          refine ⟨11650084042177294096388563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62133781558278901847405669 11650084042177294096388563)
          ·
            refine ⟨17475126063265941144582845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650084042177294096388563 17475126063265941144582845)
            ·
              refine ⟨6553172273724727929218567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17475126063265941144582845 6553172273724727929218567)
              ·
                refine ⟨9829758410587091893827851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553172273724727929218567 9829758410587091893827851)
                ·
                  refine ⟨14744637615880637840741777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9829758410587091893827851 14744637615880637840741777)
                  ·
                    refine ⟨11058478211910478380556333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14744637615880637840741777 11058478211910478380556333)
                    ·
                      refine ⟨4146929329466429392708625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11058478211910478380556333 4146929329466429392708625)
                      ·
                        rfl

theorem cell23_8076116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_8076116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076116 prefixEnd_8076116 := by exact prefixLift 8076116
  have htrace : WordTrace (prefixWord ++ tailWord_8076116) baseStart_8076116 baseEnd_8076116 := by
    simpa [prefixWord, tailWord_8076116, baseEnd_8076116] using wordTrace_append hprefix tailTrace_8076116
  have hstable : (prefixWord ++ tailWord_8076116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076116).length < 2 ^ (prefixWord ++ tailWord_8076116).sum := by decide
  have hdescent : baseEnd_8076116 < baseStart_8076116 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076135 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 4]
def baseStart_8076135 : Nat := 118140960795 + 8076135 * 2 ^ 59
def prefixEnd_8076135 : Nat := 4983230072969 + 3 ^ 40 * 8076135 * 2
def baseEnd_8076135 : Nat := 4146939085598864818371037

theorem tailTrace_8076135 : CollatzResearch.WordTrace tailWord_8076135 prefixEnd_8076135 4146939085598864818371037 := by
  unfold tailWord_8076135
  simp only [CollatzResearch.WordTrace]
  refine ⟨294560842596549663891901859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196373895064366442594601239 294560842596549663891901859)
  ·
    refine ⟨441841263894824495837852789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294560842596549663891901859 441841263894824495837852789)
    ·
      refine ⟨41422618490139796484798699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441841263894824495837852789 41422618490139796484798699)
      ·
        refine ⟨62133927735209694727198049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41422618490139796484798699 62133927735209694727198049)
        ·
          refine ⟨46600445801407271045398537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62133927735209694727198049 46600445801407271045398537)
          ·
            refine ⟨34950334351055453284048903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46600445801407271045398537 34950334351055453284048903)
            ·
              refine ⟨52425501526583179926073355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34950334351055453284048903 52425501526583179926073355)
              ·
                refine ⟨78638252289874769889110033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52425501526583179926073355 78638252289874769889110033)
                ·
                  refine ⟨58978689217406077416832525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78638252289874769889110033 58978689217406077416832525)
                  ·
                    refine ⟨22117008456527279031312197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58978689217406077416832525 22117008456527279031312197)
                    ·
                      refine ⟨4146939085598864818371037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22117008456527279031312197 4146939085598864818371037)
                      ·
                        rfl

theorem cell23_8076135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_8076135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076135 prefixEnd_8076135 := by exact prefixLift 8076135
  have htrace : WordTrace (prefixWord ++ tailWord_8076135) baseStart_8076135 baseEnd_8076135 := by
    simpa [prefixWord, tailWord_8076135, baseEnd_8076135] using wordTrace_append hprefix tailTrace_8076135
  have hstable : (prefixWord ++ tailWord_8076135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076135).length < 2 ^ (prefixWord ++ tailWord_8076135).sum := by decide
  have hdescent : baseEnd_8076135 < baseStart_8076135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076145 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 2, 6]
def baseStart_8076145 : Nat := 118140960795 + 8076145 * 2 ^ 59
def prefixEnd_8076145 : Nat := 4983230072969 + 3 ^ 40 * 8076145 * 2
def baseEnd_8076145 : Nat := 1382314740135136593081997

theorem tailTrace_8076145 : CollatzResearch.WordTrace tailWord_8076145 prefixEnd_8076145 1382314740135136593081997 := by
  unfold tailWord_8076145
  simp only [CollatzResearch.WordTrace]
  refine ⟨294561207326513435599765889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196374138217675623733177259 294561207326513435599765889)
  ·
    refine ⟨220920905494885076699824417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294561207326513435599765889 220920905494885076699824417)
    ·
      refine ⟨165690679121163807524868313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220920905494885076699824417 165690679121163807524868313)
      ·
        refine ⟨124268009340872855643651235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165690679121163807524868313 124268009340872855643651235)
        ·
          refine ⟨186402014011309283465476853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124268009340872855643651235 186402014011309283465476853)
          ·
            refine ⟨17475188813560245324888455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186402014011309283465476853 17475188813560245324888455)
            ·
              refine ⟨26212783220340367987332683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17475188813560245324888455 26212783220340367987332683)
              ·
                refine ⟨39319174830510551980999025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26212783220340367987332683 39319174830510551980999025)
                ·
                  refine ⟨29489381122882913985749269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39319174830510551980999025 29489381122882913985749269)
                  ·
                    refine ⟨1382314740135136593081997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29489381122882913985749269 1382314740135136593081997)
                    ·
                      rfl

theorem cell23_8076145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 6].length) (baseStart_8076145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076145 prefixEnd_8076145 := by exact prefixLift 8076145
  have htrace : WordTrace (prefixWord ++ tailWord_8076145) baseStart_8076145 baseEnd_8076145 := by
    simpa [prefixWord, tailWord_8076145, baseEnd_8076145] using wordTrace_append hprefix tailTrace_8076145
  have hstable : (prefixWord ++ tailWord_8076145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076145).length < 2 ^ (prefixWord ++ tailWord_8076145).sum := by decide
  have hdescent : baseEnd_8076145 < baseStart_8076145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076186 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2]
def baseStart_8076186 : Nat := 118140960795 + 8076186 * 2 ^ 59
def prefixEnd_8076186 : Nat := 4983230072969 + 3 ^ 40 * 8076186 * 2
def baseEnd_8076186 : Nat := 4146965273112244118833303

theorem tailTrace_8076186 : CollatzResearch.WordTrace tailWord_8076186 prefixEnd_8076186 4146965273112244118833303 := by
  unfold tailWord_8076186
  simp only [CollatzResearch.WordTrace]
  refine ⟨73640675679841224900502103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196375135146243266401338941 73640675679841224900502103)
  ·
    refine ⟨110461013519761837350753155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73640675679841224900502103 110461013519761837350753155)
    ·
      refine ⟨165691520279642756026129733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110461013519761837350753155 165691520279642756026129733)
      ·
        refine ⟨31067160052433016754899325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165691520279642756026129733 31067160052433016754899325)
        ·
          refine ⟨11650185019662381283087247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31067160052433016754899325 11650185019662381283087247)
          ·
            refine ⟨17475277529493571924630871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650185019662381283087247 17475277529493571924630871)
            ·
              refine ⟨26212916294240357886946307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17475277529493571924630871 26212916294240357886946307)
              ·
                refine ⟨39319374441360536830419461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26212916294240357886946307 39319374441360536830419461)
                ·
                  refine ⟨7372382707755100655703649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39319374441360536830419461 7372382707755100655703649)
                  ·
                    refine ⟨5529287030816325491777737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7372382707755100655703649 5529287030816325491777737)
                    ·
                      refine ⟨4146965273112244118833303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529287030816325491777737 4146965273112244118833303)
                      ·
                        rfl

theorem cell23_8076186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_8076186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076186 prefixEnd_8076186 := by exact prefixLift 8076186
  have htrace : WordTrace (prefixWord ++ tailWord_8076186) baseStart_8076186 baseEnd_8076186 := by
    simpa [prefixWord, tailWord_8076186, baseEnd_8076186] using wordTrace_append hprefix tailTrace_8076186
  have hstable : (prefixWord ++ tailWord_8076186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076186).length < 2 ^ (prefixWord ++ tailWord_8076186).sum := by decide
  have hdescent : baseEnd_8076186 < baseStart_8076186 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076192 : List Nat := [2, 1, 1, 4, 1, 1, 4, 4, 5]
def baseStart_8076192 : Nat := 118140960795 + 8076192 * 2 ^ 59
def prefixEnd_8076192 : Nat := 4983230072969 + 3 ^ 40 * 8076192 * 2
def baseEnd_8076192 : Nat := 460774261555130121706475

theorem tailTrace_8076192 : CollatzResearch.WordTrace tailWord_8076192 prefixEnd_8076192 460774261555130121706475 := by
  unfold tailWord_8076192
  simp only [CollatzResearch.WordTrace]
  refine ⟨147281460778671581313363415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196375281038228775084484553 147281460778671581313363415)
  ·
    refine ⟨220922191168007371970045123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147281460778671581313363415 220922191168007371970045123)
    ·
      refine ⟨331383286752011057955067685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220922191168007371970045123 331383286752011057955067685)
      ·
        refine ⟨62134366266002073366575191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331383286752011057955067685 62134366266002073366575191)
        ·
          refine ⟨93201549399003110049862787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62134366266002073366575191 93201549399003110049862787)
          ·
            refine ⟨139802324098504665074794181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93201549399003110049862787 139802324098504665074794181)
            ·
              refine ⟨26212935768469624701523909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139802324098504665074794181 26212935768469624701523909)
              ·
                refine ⟨4914925456588054631535733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26212935768469624701523909 4914925456588054631535733)
                ·
                  refine ⟨460774261555130121706475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4914925456588054631535733 460774261555130121706475)
                  ·
                    rfl

theorem cell23_8076192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 4, 5].length) (baseStart_8076192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076192 prefixEnd_8076192 := by exact prefixLift 8076192
  have htrace : WordTrace (prefixWord ++ tailWord_8076192) baseStart_8076192 baseEnd_8076192 := by
    simpa [prefixWord, tailWord_8076192, baseEnd_8076192] using wordTrace_append hprefix tailTrace_8076192
  have hstable : (prefixWord ++ tailWord_8076192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076192).length < 2 ^ (prefixWord ++ tailWord_8076192).sum := by decide
  have hdescent : baseEnd_8076192 < baseStart_8076192 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076222 : List Nat := [4, 2, 1, 1, 1, 2, 2, 3, 2, 5]
def baseStart_8076222 : Nat := 118140960795 + 8076222 * 2 ^ 59
def prefixEnd_8076222 : Nat := 4983230072969 + 3 ^ 40 * 8076222 * 2
def baseEnd_8076222 : Nat := 1382327919471935325994379

theorem tailTrace_8076222 : CollatzResearch.WordTrace tailWord_8076222 prefixEnd_8076222 1382327919471935325994379 := by
  unfold tailWord_8076222
  simp only [CollatzResearch.WordTrace]
  refine ⟨36820501968404309718789865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196376010498156318500212613 36820501968404309718789865)
  ·
    refine ⟨27615376476303232289092399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36820501968404309718789865 27615376476303232289092399)
    ·
      refine ⟨41423064714454848433638599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27615376476303232289092399 41423064714454848433638599)
      ·
        refine ⟨62134597071682272650457899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41423064714454848433638599 62134597071682272650457899)
        ·
          refine ⟨93201895607523408975686849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62134597071682272650457899 93201895607523408975686849)
          ·
            refine ⟨69901421705642556731765137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93201895607523408975686849 69901421705642556731765137)
            ·
              refine ⟨52426066279231917548823853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69901421705642556731765137 52426066279231917548823853)
              ·
                refine ⟨19659774854711969080808945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52426066279231917548823853 19659774854711969080808945)
                ·
                  refine ⟨14744831141033976810606709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19659774854711969080808945 14744831141033976810606709)
                  ·
                    refine ⟨1382327919471935325994379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14744831141033976810606709 1382327919471935325994379)
                    ·
                      rfl

theorem cell23_8076222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_8076222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076222 prefixEnd_8076222 := by exact prefixLift 8076222
  have htrace : WordTrace (prefixWord ++ tailWord_8076222) baseStart_8076222 baseEnd_8076222 := by
    simpa [prefixWord, tailWord_8076222, baseEnd_8076222] using wordTrace_append hprefix tailTrace_8076222
  have hstable : (prefixWord ++ tailWord_8076222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076222).length < 2 ^ (prefixWord ++ tailWord_8076222).sum := by decide
  have hdescent : baseEnd_8076222 < baseStart_8076222 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076285 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 8]
def baseStart_8076285 : Nat := 118140960795 + 8076285 * 2 ^ 59
def prefixEnd_8076285 : Nat := 4983230072969 + 3 ^ 40 * 8076285 * 2
def baseEnd_8076285 : Nat := 4147016107697039231495347

theorem tailTrace_8076285 : CollatzResearch.WordTrace tailWord_8076285 prefixEnd_8076285 4147016107697039231495347 := by
  unfold tailWord_8076285
  simp only [CollatzResearch.WordTrace]
  refine ⟨294566313546006239509862309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196377542364004159673241539 294566313546006239509862309)
  ·
    refine ⟨55231183789876169908099183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294566313546006239509862309 55231183789876169908099183)
    ·
      refine ⟨82846775684814254862148775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55231183789876169908099183 82846775684814254862148775)
      ·
        refine ⟨124270163527221382293223163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82846775684814254862148775 124270163527221382293223163)
        ·
          refine ⟨186405245290832073439834745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124270163527221382293223163 186405245290832073439834745)
          ·
            refine ⟨139803933968124055079876059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186405245290832073439834745 139803933968124055079876059)
            ·
              refine ⟨209705900952186082619814089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139803933968124055079876059 209705900952186082619814089)
              ·
                refine ⟨157279425714139561964860567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209705900952186082619814089 157279425714139561964860567)
                ·
                  refine ⟨235919138571209342947290851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157279425714139561964860567 235919138571209342947290851)
                  ·
                    refine ⟨353878707856814014420936277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235919138571209342947290851 353878707856814014420936277)
                    ·
                      refine ⟨4147016107697039231495347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 353878707856814014420936277 4147016107697039231495347)
                      ·
                        rfl

theorem cell23_8076285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_8076285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076285 prefixEnd_8076285 := by exact prefixLift 8076285
  have htrace : WordTrace (prefixWord ++ tailWord_8076285) baseStart_8076285 baseEnd_8076285 := by
    simpa [prefixWord, tailWord_8076285, baseEnd_8076285] using wordTrace_append hprefix tailTrace_8076285
  have hstable : (prefixWord ++ tailWord_8076285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076285).length < 2 ^ (prefixWord ++ tailWord_8076285).sum := by decide
  have hdescent : baseEnd_8076285 < baseStart_8076285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076305 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 5]
def baseStart_8076305 : Nat := 118140960795 + 8076305 * 2 ^ 59
def prefixEnd_8076305 : Nat := 4983230072969 + 3 ^ 40 * 8076305 * 2
def baseEnd_8076305 : Nat := 4147026377310129153245255

theorem tailTrace_8076305 : CollatzResearch.WordTrace tailWord_8076305 prefixEnd_8076305 4147026377310129153245255 := by
  unfold tailWord_8076305
  simp only [CollatzResearch.WordTrace]
  refine ⟨294567043005933782925590369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196378028670622521950393579 294567043005933782925590369)
  ·
    refine ⟨220925282254450337194192777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294567043005933782925590369 220925282254450337194192777)
    ·
      refine ⟨165693961690837752895644583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220925282254450337194192777 165693961690837752895644583)
      ·
        refine ⟨248540942536256629343466875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165693961690837752895644583 248540942536256629343466875)
        ·
          refine ⟨372811413804384944015200313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248540942536256629343466875 372811413804384944015200313)
          ·
            refine ⟨279608560353288708011400235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372811413804384944015200313 279608560353288708011400235)
            ·
              refine ⟨419412840529933062017100353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279608560353288708011400235 419412840529933062017100353)
              ·
                refine ⟨314559630397449796512825265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419412840529933062017100353 314559630397449796512825265)
                ·
                  refine ⟨235919722798087347384618949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314559630397449796512825265 235919722798087347384618949)
                  ·
                    refine ⟨44234948024641377634616053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235919722798087347384618949 44234948024641377634616053)
                    ·
                      refine ⟨4147026377310129153245255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44234948024641377634616053 4147026377310129153245255)
                      ·
                        rfl

theorem cell23_8076305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_8076305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076305 prefixEnd_8076305 := by exact prefixLift 8076305
  have htrace : WordTrace (prefixWord ++ tailWord_8076305) baseStart_8076305 baseEnd_8076305 := by
    simpa [prefixWord, tailWord_8076305, baseEnd_8076305] using wordTrace_append hprefix tailTrace_8076305
  have hstable : (prefixWord ++ tailWord_8076305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076305).length < 2 ^ (prefixWord ++ tailWord_8076305).sum := by decide
  have hdescent : baseEnd_8076305 < baseStart_8076305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076312 : List Nat := [2, 1, 2, 3, 2, 2, 1, 2, 3, 5]
def baseStart_8076312 : Nat := 118140960795 + 8076312 * 2 ^ 59
def prefixEnd_8076312 : Nat := 4983230072969 + 3 ^ 40 * 8076312 * 2
def baseEnd_8076312 : Nat := 1382343323891570208619241

theorem tailTrace_8076312 : CollatzResearch.WordTrace tailWord_8076312 prefixEnd_8076312 1382343323891570208619241 := by
  unfold tailWord_8076312
  simp only [CollatzResearch.WordTrace]
  refine ⟨147283649158454211560547595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196378198877938948747396793 147283649158454211560547595)
  ·
    refine ⟨220925473737681317340821393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147283649158454211560547595 220925473737681317340821393)
    ·
      refine ⟨165694105303260988005616045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220925473737681317340821393 165694105303260988005616045)
      ·
        refine ⟨62135289488722870502106017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165694105303260988005616045 62135289488722870502106017)
        ·
          refine ⟨46601467116542152876579513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62135289488722870502106017 46601467116542152876579513)
          ·
            refine ⟨34951100337406614657434635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46601467116542152876579513 34951100337406614657434635)
            ·
              refine ⟨52426650506109921986151953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34951100337406614657434635 52426650506109921986151953)
              ·
                refine ⟨39319987879582441489613965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52426650506109921986151953 39319987879582441489613965)
                ·
                  refine ⟨14744995454843415558605237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39319987879582441489613965 14744995454843415558605237)
                  ·
                    refine ⟨1382343323891570208619241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14744995454843415558605237 1382343323891570208619241)
                    ·
                      rfl

theorem cell23_8076312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_8076312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076312 prefixEnd_8076312 := by exact prefixLift 8076312
  have htrace : WordTrace (prefixWord ++ tailWord_8076312) baseStart_8076312 baseEnd_8076312 := by
    simpa [prefixWord, tailWord_8076312, baseEnd_8076312] using wordTrace_append hprefix tailTrace_8076312
  have hstable : (prefixWord ++ tailWord_8076312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076312).length < 2 ^ (prefixWord ++ tailWord_8076312).sum := by decide
  have hdescent : baseEnd_8076312 < baseStart_8076312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076332 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 4]
def baseStart_8076332 : Nat := 118140960795 + 8076332 * 2 ^ 59
def prefixEnd_8076332 : Nat := 4983230072969 + 3 ^ 40 * 8076332 * 2
def baseEnd_8076332 : Nat := 4147040241287800547607631

theorem tailTrace_8076332 : CollatzResearch.WordTrace tailWord_8076332 prefixEnd_8076332 4147040241287800547607631 := by
  unfold tailWord_8076332
  simp only [CollatzResearch.WordTrace]
  refine ⟨147284013888417983268411625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196378685184557311024548833 147284013888417983268411625)
  ·
    refine ⟨110463010416313487451308719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147284013888417983268411625 110463010416313487451308719)
    ·
      refine ⟨165694515624470231176963079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110463010416313487451308719 165694515624470231176963079)
      ·
        refine ⟨248541773436705346765444619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165694515624470231176963079 248541773436705346765444619)
        ·
          refine ⟨372812660155058020148166929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248541773436705346765444619 372812660155058020148166929)
          ·
            refine ⟨279609495116293515111125197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372812660155058020148166929 279609495116293515111125197)
            ·
              refine ⟨104853560668610068166671949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279609495116293515111125197 104853560668610068166671949)
              ·
                refine ⟨39320085250728775562501981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104853560668610068166671949 39320085250728775562501981)
                ·
                  refine ⟨14745031969023290835938243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39320085250728775562501981 14745031969023290835938243)
                  ·
                    refine ⟨22117547953534936253907365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14745031969023290835938243 22117547953534936253907365)
                    ·
                      refine ⟨4147040241287800547607631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22117547953534936253907365 4147040241287800547607631)
                      ·
                        rfl

theorem cell23_8076332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_8076332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076332 prefixEnd_8076332 := by exact prefixLift 8076332
  have htrace : WordTrace (prefixWord ++ tailWord_8076332) baseStart_8076332 baseEnd_8076332 := by
    simpa [prefixWord, tailWord_8076332, baseEnd_8076332] using wordTrace_append hprefix tailTrace_8076332
  have hstable : (prefixWord ++ tailWord_8076332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076332).length < 2 ^ (prefixWord ++ tailWord_8076332).sum := by decide
  have hdescent : baseEnd_8076332 < baseStart_8076332 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076352 : List Nat := [2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_8076352 : Nat := 118140960795 + 8076352 * 2 ^ 59
def prefixEnd_8076352 : Nat := 4983230072969 + 3 ^ 40 * 8076352 * 2
def baseEnd_8076352 : Nat := 4147050510900890469357539

theorem tailTrace_8076352 : CollatzResearch.WordTrace tailWord_8076352 prefixEnd_8076352 4147050510900890469357539 := by
  unfold tailWord_8076352
  simp only [CollatzResearch.WordTrace]
  refine ⟨147284378618381754976275655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196379171491175673301700873 147284378618381754976275655)
  ·
    refine ⟨220926567927572632464413483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147284378618381754976275655 220926567927572632464413483)
    ·
      refine ⟨331389851891358948696620225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220926567927572632464413483 331389851891358948696620225)
      ·
        refine ⟨248542388918519211522465169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331389851891358948696620225 248542388918519211522465169)
        ·
          refine ⟨186406791688889408641848877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248542388918519211522465169 186406791688889408641848877)
          ·
            refine ⟨69902546883333528240693329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186406791688889408641848877 69902546883333528240693329)
            ·
              refine ⟨52426910162500146180519997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69902546883333528240693329 52426910162500146180519997)
              ·
                refine ⟨19660091310937554817694999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52426910162500146180519997 19660091310937554817694999)
                ·
                  refine ⟨29490136966406332226542499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19660091310937554817694999 29490136966406332226542499)
                  ·
                    refine ⟨44235205449609498339813749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29490136966406332226542499 44235205449609498339813749)
                    ·
                      refine ⟨4147050510900890469357539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44235205449609498339813749 4147050510900890469357539)
                      ·
                        rfl

theorem cell23_8076352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_8076352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076352 prefixEnd_8076352 := by exact prefixLift 8076352
  have htrace : WordTrace (prefixWord ++ tailWord_8076352) baseStart_8076352 baseEnd_8076352 := by
    simpa [prefixWord, tailWord_8076352, baseEnd_8076352] using wordTrace_append hprefix tailTrace_8076352
  have hstable : (prefixWord ++ tailWord_8076352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076352).length < 2 ^ (prefixWord ++ tailWord_8076352).sum := by decide
  have hdescent : baseEnd_8076352 < baseStart_8076352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076355 : List Nat := [1, 1, 1, 3, 1, 2, 14]
def baseStart_8076355 : Nat := 118140960795 + 8076355 * 2 ^ 59
def prefixEnd_8076355 : Nat := 4983230072969 + 3 ^ 40 * 8076355 * 2
def baseEnd_8076355 : Nat := 51198173473368567378025

theorem tailTrace_8076355 : CollatzResearch.WordTrace tailWord_8076355 prefixEnd_8076355 51198173473368567378025 := by
  unfold tailWord_8076355
  simp only [CollatzResearch.WordTrace]
  refine ⟨294568866655752641464910519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196379244437168427643273679 294568866655752641464910519)
  ·
    refine ⟨441853299983628962197365779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294568866655752641464910519 441853299983628962197365779)
    ·
      refine ⟨662779949975443443296048669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441853299983628962197365779 662779949975443443296048669)
      ·
        refine ⟨248542481240791291236018251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662779949975443443296048669 248542481240791291236018251)
        ·
          refine ⟨372813721861186936854027377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248542481240791291236018251 372813721861186936854027377)
          ·
            refine ⟨279610291395890202640520533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372813721861186936854027377 279610291395890202640520533)
            ·
              refine ⟨51198173473368567378025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 279610291395890202640520533 51198173473368567378025)
              ·
                rfl

theorem cell23_8076355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 14].length) (baseStart_8076355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076355 prefixEnd_8076355 := by exact prefixLift 8076355
  have htrace : WordTrace (prefixWord ++ tailWord_8076355) baseStart_8076355 baseEnd_8076355 := by
    simpa [prefixWord, tailWord_8076355, baseEnd_8076355] using wordTrace_append hprefix tailTrace_8076355
  have hstable : (prefixWord ++ tailWord_8076355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076355).length < 2 ^ (prefixWord ++ tailWord_8076355).sum := by decide
  have hdescent : baseEnd_8076355 < baseStart_8076355 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076359 : List Nat := [1, 1, 4, 1, 3, 3, 1, 1, 4, 4]
def baseStart_8076359 : Nat := 118140960795 + 8076359 * 2 ^ 59
def prefixEnd_8076359 : Nat := 4983230072969 + 3 ^ 40 * 8076359 * 2
def baseEnd_8076359 : Nat := 1382351368421823980656669

theorem tailTrace_8076359 : CollatzResearch.WordTrace tailWord_8076359 prefixEnd_8076359 1382351368421823980656669 := by
  unfold tailWord_8076359
  simp only [CollatzResearch.WordTrace]
  refine ⟨294569012547738150148056131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196379341698492100098704087 294569012547738150148056131)
  ·
    refine ⟨441853518821607225222084197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294569012547738150148056131 441853518821607225222084197)
    ·
      refine ⟨82847534779051354729140787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441853518821607225222084197 82847534779051354729140787)
      ·
        refine ⟨124271302168577032093711181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82847534779051354729140787 124271302168577032093711181)
        ·
          refine ⟨46601738313216387035141693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124271302168577032093711181 46601738313216387035141693)
          ·
            refine ⟨17475651867456145138178135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46601738313216387035141693 17475651867456145138178135)
            ·
              refine ⟨26213477801184217707267203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17475651867456145138178135 26213477801184217707267203)
              ·
                refine ⟨39320216701776326560900805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26213477801184217707267203 39320216701776326560900805)
                ·
                  refine ⟨7372540631583061230168901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39320216701776326560900805 7372540631583061230168901)
                  ·
                    refine ⟨1382351368421823980656669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7372540631583061230168901 1382351368421823980656669)
                    ·
                      rfl

theorem cell23_8076359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_8076359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076359 prefixEnd_8076359 := by exact prefixLift 8076359
  have htrace : WordTrace (prefixWord ++ tailWord_8076359) baseStart_8076359 baseEnd_8076359 := by
    simpa [prefixWord, tailWord_8076359, baseEnd_8076359] using wordTrace_append hprefix tailTrace_8076359
  have hstable : (prefixWord ++ tailWord_8076359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076359).length < 2 ^ (prefixWord ++ tailWord_8076359).sum := by decide
  have hdescent : baseEnd_8076359 < baseStart_8076359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076362 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4]
def baseStart_8076362 : Nat := 118140960795 + 8076362 * 2 ^ 59
def prefixEnd_8076362 : Nat := 4983230072969 + 3 ^ 40 * 8076362 * 2
def baseEnd_8076362 : Nat := 4147055645707435430232493

theorem tailTrace_8076362 : CollatzResearch.WordTrace tailWord_8076362 prefixEnd_8076362 4147055645707435430232493 := by
  unfold tailWord_8076362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73642280491681820415103835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196379414644484854440276893 73642280491681820415103835)
  ·
    refine ⟨110463420737522730622655753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73642280491681820415103835 110463420737522730622655753)
    ·
      refine ⟨82847565553142047966991815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110463420737522730622655753 82847565553142047966991815)
      ·
        refine ⟨124271348329713071950487723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82847565553142047966991815 124271348329713071950487723)
        ·
          refine ⟨186407022494569607925731585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124271348329713071950487723 186407022494569607925731585)
          ·
            refine ⟨139805266870927205944298689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186407022494569607925731585 139805266870927205944298689)
            ·
              refine ⟨104853950153195404458224017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139805266870927205944298689 104853950153195404458224017)
              ·
                refine ⟨78640462614896553343668013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104853950153195404458224017 78640462614896553343668013)
                ·
                  refine ⟨29490173480586207503875505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78640462614896553343668013 29490173480586207503875505)
                  ·
                    refine ⟨22117630110439655627906629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29490173480586207503875505 22117630110439655627906629)
                    ·
                      refine ⟨4147055645707435430232493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22117630110439655627906629 4147055645707435430232493)
                      ·
                        rfl

theorem cell23_8076362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4].length) (baseStart_8076362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076362 prefixEnd_8076362 := by exact prefixLift 8076362
  have htrace : WordTrace (prefixWord ++ tailWord_8076362) baseStart_8076362 baseEnd_8076362 := by
    simpa [prefixWord, tailWord_8076362, baseEnd_8076362] using wordTrace_append hprefix tailTrace_8076362
  have hstable : (prefixWord ++ tailWord_8076362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076362).length < 2 ^ (prefixWord ++ tailWord_8076362).sum := by decide
  have hdescent : baseEnd_8076362 < baseStart_8076362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076376 : List Nat := [2, 1, 2, 2, 1, 3, 5, 1, 2, 4]
def baseStart_8076376 : Nat := 118140960795 + 8076376 * 2 ^ 59
def prefixEnd_8076376 : Nat := 4983230072969 + 3 ^ 40 * 8076376 * 2
def baseEnd_8076376 : Nat := 1382354278145532791819143

theorem tailTrace_8076376 : CollatzResearch.WordTrace tailWord_8076376 prefixEnd_8076376 1382354278145532791819143 := by
  unfold tailWord_8076376
  simp only [CollatzResearch.WordTrace]
  refine ⟨147284816294338281025712491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196379755059117708034283321 147284816294338281025712491)
  ·
    refine ⟨220927224441507421538568737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147284816294338281025712491 220927224441507421538568737)
    ·
      refine ⟨165695418331130566153926553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220927224441507421538568737 165695418331130566153926553)
      ·
        refine ⟨124271563748347924615444915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165695418331130566153926553 124271563748347924615444915)
        ·
          refine ⟨186407345622521886923167373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124271563748347924615444915 186407345622521886923167373)
          ·
            refine ⟨69902754608445707596187765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186407345622521886923167373 69902754608445707596187765)
            ·
              refine ⟨6553383244541785087142603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69902754608445707596187765 6553383244541785087142603)
              ·
                refine ⟨9830074866812677630713905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6553383244541785087142603 9830074866812677630713905)
                ·
                  refine ⟨7372556150109508223035429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9830074866812677630713905 7372556150109508223035429)
                  ·
                    refine ⟨1382354278145532791819143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7372556150109508223035429 1382354278145532791819143)
                    ·
                      rfl

theorem cell23_8076376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 1, 2, 4].length) (baseStart_8076376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076376 prefixEnd_8076376 := by exact prefixLift 8076376
  have htrace : WordTrace (prefixWord ++ tailWord_8076376) baseStart_8076376 baseEnd_8076376 := by
    simpa [prefixWord, tailWord_8076376, baseEnd_8076376] using wordTrace_append hprefix tailTrace_8076376
  have hstable : (prefixWord ++ tailWord_8076376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076376).length < 2 ^ (prefixWord ++ tailWord_8076376).sum := by decide
  have hdescent : baseEnd_8076376 < baseStart_8076376 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076399 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 3]
def baseStart_8076399 : Nat := 118140960795 + 8076399 * 2 ^ 59
def prefixEnd_8076399 : Nat := 4983230072969 + 3 ^ 40 * 8076399 * 2
def baseEnd_8076399 : Nat := 4147074644491651785469823

theorem tailTrace_8076399 : CollatzResearch.WordTrace tailWord_8076399 prefixEnd_8076399 4147074644491651785469823 := by
  unfold tailWord_8076399
  simp only [CollatzResearch.WordTrace]
  refine ⟨294570471467593236979512251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196380314311728824653008167 294570471467593236979512251)
  ·
    refine ⟨441855707201389855469268377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294570471467593236979512251 441855707201389855469268377)
    ·
      refine ⟨331391780401042391601951283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441855707201389855469268377 331391780401042391601951283)
      ·
        refine ⟨497087670601563587402926925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331391780401042391601951283 497087670601563587402926925)
        ·
          refine ⟨186407876475586345276097597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 497087670601563587402926925 186407876475586345276097597)
          ·
            refine ⟨69902953678344879478536599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186407876475586345276097597 69902953678344879478536599)
            ·
              refine ⟨104854430517517319217804899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69902953678344879478536599 104854430517517319217804899)
              ·
                refine ⟨157281645776275978826707349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104854430517517319217804899 157281645776275978826707349)
                ·
                  refine ⟨7372577145762936507501907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 157281645776275978826707349 7372577145762936507501907)
                  ·
                    refine ⟨11058865718644404761252861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7372577145762936507501907 11058865718644404761252861)
                    ·
                      refine ⟨4147074644491651785469823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11058865718644404761252861 4147074644491651785469823)
                      ·
                        rfl

theorem cell23_8076399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 1, 3].length) (baseStart_8076399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076399 prefixEnd_8076399 := by exact prefixLift 8076399
  have htrace : WordTrace (prefixWord ++ tailWord_8076399) baseStart_8076399 baseEnd_8076399 := by
    simpa [prefixWord, tailWord_8076399, baseEnd_8076399] using wordTrace_append hprefix tailTrace_8076399
  have hstable : (prefixWord ++ tailWord_8076399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076399).length < 2 ^ (prefixWord ++ tailWord_8076399).sum := by decide
  have hdescent : baseEnd_8076399 < baseStart_8076399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076412 : List Nat := [2, 2, 2, 1, 1, 3, 1, 2, 2, 2, 5]
def baseStart_8076412 : Nat := 118140960795 + 8076412 * 2 ^ 59
def prefixEnd_8076412 : Nat := 4983230072969 + 3 ^ 40 * 8076412 * 2
def baseEnd_8076412 : Nat := 4147081319740160234607263

theorem tailTrace_8076412 : CollatzResearch.WordTrace tailWord_8076412 prefixEnd_8076412 4147081319740160234607263 := by
  unfold tailWord_8076412
  simp only [CollatzResearch.WordTrace]
  refine ⟨147285472808273070099867745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196380630411030760133156993 147285472808273070099867745)
  ·
    refine ⟨110464104606204802574900809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147285472808273070099867745 110464104606204802574900809)
    ·
      refine ⟨82848078454653601931175607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110464104606204802574900809 82848078454653601931175607)
      ·
        refine ⟨124272117681980402896763411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82848078454653601931175607 124272117681980402896763411)
        ·
          refine ⟨186408176522970604345145117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124272117681980402896763411 186408176522970604345145117)
          ·
            refine ⟨69903066196113976629429419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186408176522970604345145117 69903066196113976629429419)
            ·
              refine ⟨104854599294170964944144129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69903066196113976629429419 104854599294170964944144129)
              ·
                refine ⟨78640949470628223708108097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104854599294170964944144129 78640949470628223708108097)
                ·
                  refine ⟨58980712102971167781081073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78640949470628223708108097 58980712102971167781081073)
                  ·
                    refine ⟨44235534077228375835810805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58980712102971167781081073 44235534077228375835810805)
                    ·
                      refine ⟨4147081319740160234607263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44235534077228375835810805 4147081319740160234607263)
                      ·
                        rfl

theorem cell23_8076412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_8076412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076412 prefixEnd_8076412 := by exact prefixLift 8076412
  have htrace : WordTrace (prefixWord ++ tailWord_8076412) baseStart_8076412 baseEnd_8076412 := by
    simpa [prefixWord, tailWord_8076412, baseEnd_8076412] using wordTrace_append hprefix tailTrace_8076412
  have hstable : (prefixWord ++ tailWord_8076412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076412).length < 2 ^ (prefixWord ++ tailWord_8076412).sum := by decide
  have hdescent : baseEnd_8076412 < baseStart_8076412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076417 : List Nat := [1, 2, 4, 2, 2, 2, 3, 2, 1, 2, 2]
def baseStart_8076417 : Nat := 118140960795 + 8076417 * 2 ^ 59
def prefixEnd_8076417 : Nat := 4983230072969 + 3 ^ 40 * 8076417 * 2
def baseEnd_8076417 : Nat := 4147083887143432715044741

theorem tailTrace_8076417 : CollatzResearch.WordTrace tailWord_8076417 prefixEnd_8076417 4147083887143432715044741 := by
  unfold tailWord_8076417
  simp only [CollatzResearch.WordTrace]
  refine ⟨294571127981528026053667505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196380751987685350702445003 294571127981528026053667505)
  ·
    refine ⟨220928345986146019540250629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294571127981528026053667505 220928345986146019540250629)
    ·
      refine ⟨41424064872402378663796993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220928345986146019540250629 41424064872402378663796993)
      ·
        refine ⟨31068048654301783997847745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41424064872402378663796993 31068048654301783997847745)
        ·
          refine ⟨23301036490726337998385809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31068048654301783997847745 23301036490726337998385809)
          ·
            refine ⟨17475777368044753498789357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23301036490726337998385809 17475777368044753498789357)
            ·
              refine ⟨6553416513016782562046009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17475777368044753498789357 6553416513016782562046009)
              ·
                refine ⟨4915062384762586921534507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6553416513016782562046009 4915062384762586921534507)
                ·
                  refine ⟨7372593577143880382301761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915062384762586921534507 7372593577143880382301761)
                  ·
                    refine ⟨5529445182857910286726321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7372593577143880382301761 5529445182857910286726321)
                    ·
                      refine ⟨4147083887143432715044741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529445182857910286726321 4147083887143432715044741)
                      ·
                        rfl

theorem cell23_8076417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_8076417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076417 prefixEnd_8076417 := by exact prefixLift 8076417
  have htrace : WordTrace (prefixWord ++ tailWord_8076417) baseStart_8076417 baseEnd_8076417 := by
    simpa [prefixWord, tailWord_8076417, baseEnd_8076417] using wordTrace_append hprefix tailTrace_8076417
  have hstable : (prefixWord ++ tailWord_8076417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076417).length < 2 ^ (prefixWord ++ tailWord_8076417).sum := by decide
  have hdescent : baseEnd_8076417 < baseStart_8076417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076426 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2]
def baseStart_8076426 : Nat := 118140960795 + 8076426 * 2 ^ 59
def prefixEnd_8076426 : Nat := 4983230072969 + 3 ^ 40 * 8076426 * 2
def baseEnd_8076426 : Nat := 4147088508469323179832199

theorem tailTrace_8076426 : CollatzResearch.WordTrace tailWord_8076426 prefixEnd_8076426 4147088508469323179832199 := by
  unfold tailWord_8076426
  simp only [CollatzResearch.WordTrace]
  refine ⟨73642864059623855147686283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196380970825663613727163421 73642864059623855147686283)
  ·
    refine ⟨110464296089435782721529425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73642864059623855147686283 110464296089435782721529425)
    ·
      refine ⟨82848222067076837041147069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110464296089435782721529425 82848222067076837041147069)
      ·
        refine ⟨31068083275153813890430151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82848222067076837041147069 31068083275153813890430151)
        ·
          refine ⟨46602124912730720835645227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31068083275153813890430151 46602124912730720835645227)
          ·
            refine ⟨69903187369096081253467841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46602124912730720835645227 69903187369096081253467841)
            ·
              refine ⟨52427390526822060940100881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69903187369096081253467841 52427390526822060940100881)
              ·
                refine ⟨39320542895116545705075661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52427390526822060940100881 39320542895116545705075661)
                ·
                  refine ⟨14745203585668704639403373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39320542895116545705075661 14745203585668704639403373)
                  ·
                    refine ⟨5529451344625764239776265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14745203585668704639403373 5529451344625764239776265)
                    ·
                      refine ⟨4147088508469323179832199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529451344625764239776265 4147088508469323179832199)
                      ·
                        rfl

theorem cell23_8076426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_8076426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076426 prefixEnd_8076426 := by exact prefixLift 8076426
  have htrace : WordTrace (prefixWord ++ tailWord_8076426) baseStart_8076426 baseEnd_8076426 := by
    simpa [prefixWord, tailWord_8076426, baseEnd_8076426] using wordTrace_append hprefix tailTrace_8076426
  have hstable : (prefixWord ++ tailWord_8076426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076426).length < 2 ^ (prefixWord ++ tailWord_8076426).sum := by decide
  have hdescent : baseEnd_8076426 < baseStart_8076426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076473 : List Nat := [1, 2, 1, 4, 1, 3, 1, 4, 2, 2, 2]
def baseStart_8076473 : Nat := 118140960795 + 8076473 * 2 ^ 59
def prefixEnd_8076473 : Nat := 4983230072969 + 3 ^ 40 * 8076473 * 2
def baseEnd_8076473 : Nat := 4147112642060084495944483

theorem tailTrace_8076473 : CollatzResearch.WordTrace tailWord_8076473 prefixEnd_8076473 4147112642060084495944483 := by
  unfold tailWord_8076473
  simp only [CollatzResearch.WordTrace]
  refine ⟨294573170469325147617706073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196382113646216765078470715 294573170469325147617706073)
  ·
    refine ⟨220929877851993860713279555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294573170469325147617706073 220929877851993860713279555)
    ·
      refine ⟨331394816777990791069919333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220929877851993860713279555 331394816777990791069919333)
      ·
        refine ⟨62136528145873273325609875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331394816777990791069919333 62136528145873273325609875)
        ·
          refine ⟨93204792218809909988414813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62136528145873273325609875 93204792218809909988414813)
          ·
            refine ⟨34951797082053716245655555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93204792218809909988414813 34951797082053716245655555)
            ·
              refine ⟨52427695623080574368483333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34951797082053716245655555 52427695623080574368483333)
              ·
                refine ⟨9830192929327607694090625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52427695623080574368483333 9830192929327607694090625)
                ·
                  refine ⟨7372644696995705770567969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9830192929327607694090625 7372644696995705770567969)
                  ·
                    refine ⟨5529483522746779327925977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7372644696995705770567969 5529483522746779327925977)
                    ·
                      refine ⟨4147112642060084495944483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529483522746779327925977 4147112642060084495944483)
                      ·
                        rfl

theorem cell23_8076473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_8076473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076473 prefixEnd_8076473 := by exact prefixLift 8076473
  have htrace : WordTrace (prefixWord ++ tailWord_8076473) baseStart_8076473 baseEnd_8076473 := by
    simpa [prefixWord, tailWord_8076473, baseEnd_8076473] using wordTrace_append hprefix tailTrace_8076473
  have hstable : (prefixWord ++ tailWord_8076473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076473).length < 2 ^ (prefixWord ++ tailWord_8076473).sum := by decide
  have hdescent : baseEnd_8076473 < baseStart_8076473 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076529 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 4]
def baseStart_8076529 : Nat := 118140960795 + 8076529 * 2 ^ 59
def prefixEnd_8076529 : Nat := 4983230072969 + 3 ^ 40 * 8076529 * 2
def baseEnd_8076529 : Nat := 4147141396976736276844225

theorem tailTrace_8076529 : CollatzResearch.WordTrace tailWord_8076529 prefixEnd_8076529 4147141396976736276844225 := by
  unfold tailWord_8076529
  simp only [CollatzResearch.WordTrace]
  refine ⟨294575212957122269181744641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196383475304748179454496427 294575212957122269181744641)
  ·
    refine ⟨220931409717841701886308481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294575212957122269181744641 220931409717841701886308481)
    ·
      refine ⟨165698557288381276414731361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220931409717841701886308481 165698557288381276414731361)
      ·
        refine ⟨124273917966285957311048521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165698557288381276414731361 124273917966285957311048521)
        ·
          refine ⟨93205438474714467983286391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124273917966285957311048521 93205438474714467983286391)
          ·
            refine ⟨139808157712071701974929587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93205438474714467983286391 139808157712071701974929587)
            ·
              refine ⟨209712236568107552962394381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139808157712071701974929587 209712236568107552962394381)
              ·
                refine ⟨78642088713040332360897893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209712236568107552962394381 78642088713040332360897893)
                ·
                  refine ⟨14745391633695062317668355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78642088713040332360897893 14745391633695062317668355)
                  ·
                    refine ⟨22118087450542593476502533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14745391633695062317668355 22118087450542593476502533)
                    ·
                      refine ⟨4147141396976736276844225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22118087450542593476502533 4147141396976736276844225)
                      ·
                        rfl

theorem cell23_8076529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_8076529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076529 prefixEnd_8076529 := by exact prefixLift 8076529
  have htrace : WordTrace (prefixWord ++ tailWord_8076529) baseStart_8076529 baseEnd_8076529 := by
    simpa [prefixWord, tailWord_8076529, baseEnd_8076529] using wordTrace_append hprefix tailTrace_8076529
  have hstable : (prefixWord ++ tailWord_8076529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076529).length < 2 ^ (prefixWord ++ tailWord_8076529).sum := by decide
  have hdescent : baseEnd_8076529 < baseStart_8076529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076549 : List Nat := [1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 3]
def baseStart_8076549 : Nat := 118140960795 + 8076549 * 2 ^ 59
def prefixEnd_8076549 : Nat := 4983230072969 + 3 ^ 40 * 8076549 * 2
def baseEnd_8076549 : Nat := 4147151666589826198594133

theorem tailTrace_8076549 : CollatzResearch.WordTrace tailWord_8076549 prefixEnd_8076549 4147151666589826198594133 := by
  unfold tailWord_8076549
  simp only [CollatzResearch.WordTrace]
  refine ⟨294575942417049812597472701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196383961611366541731648467 294575942417049812597472701)
  ·
    refine ⟨110465978406393679724052263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294575942417049812597472701 110465978406393679724052263)
    ·
      refine ⟨165698967609590519586078395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110465978406393679724052263 165698967609590519586078395)
      ·
        refine ⟨248548451414385779379117593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165698967609590519586078395 248548451414385779379117593)
        ·
          refine ⟨186411338560789334534338195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248548451414385779379117593 186411338560789334534338195)
          ·
            refine ⟨279617007841184001801507293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186411338560789334534338195 279617007841184001801507293)
            ·
              refine ⟨104856377940444000675565235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279617007841184001801507293 104856377940444000675565235)
              ·
                refine ⟨157284566910666001013347853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104856377940444000675565235 157284566910666001013347853)
                ·
                  refine ⟨58981712591499750380005445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157284566910666001013347853 58981712591499750380005445)
                  ·
                    refine ⟨11059071110906203196251021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58981712591499750380005445 11059071110906203196251021)
                    ·
                      refine ⟨4147151666589826198594133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11059071110906203196251021 4147151666589826198594133)
                      ·
                        rfl

theorem cell23_8076549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_8076549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076549 prefixEnd_8076549 := by exact prefixLift 8076549
  have htrace : WordTrace (prefixWord ++ tailWord_8076549) baseStart_8076549 baseEnd_8076549 := by
    simpa [prefixWord, tailWord_8076549, baseEnd_8076549] using wordTrace_append hprefix tailTrace_8076549
  have hstable : (prefixWord ++ tailWord_8076549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076549).length < 2 ^ (prefixWord ++ tailWord_8076549).sum := by decide
  have hdescent : baseEnd_8076549 < baseStart_8076549 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076556 : List Nat := [2, 2, 1, 2, 2, 3, 2, 2, 3, 4]
def baseStart_8076556 : Nat := 118140960795 + 8076556 * 2 ^ 59
def prefixEnd_8076556 : Nat := 4983230072969 + 3 ^ 40 * 8076556 * 2
def baseEnd_8076556 : Nat := 1382385086984802557068867

theorem tailTrace_8076556 : CollatzResearch.WordTrace tailWord_8076556 prefixEnd_8076556 1382385086984802557068867 := by
  unfold tailWord_8076556
  simp only [CollatzResearch.WordTrace]
  refine ⟨147288098864012226396488761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196384131818682968528651681 147288098864012226396488761)
  ·
    refine ⟨110466074148009169797366571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147288098864012226396488761 110466074148009169797366571)
    ·
      refine ⟨165699111222013754696049857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110466074148009169797366571 165699111222013754696049857)
      ·
        refine ⟨124274333416510316022037393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165699111222013754696049857 124274333416510316022037393)
        ·
          refine ⟨93205750062382737016528045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124274333416510316022037393 93205750062382737016528045)
          ·
            refine ⟨34952156273393526381198017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93205750062382737016528045 34952156273393526381198017)
            ·
              refine ⟨26214117205045144785898513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34952156273393526381198017 26214117205045144785898513)
              ·
                refine ⟨19660587903783858589423885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26214117205045144785898513 19660587903783858589423885)
                ·
                  refine ⟨7372720463918946971033957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19660587903783858589423885 7372720463918946971033957)
                  ·
                    refine ⟨1382385086984802557068867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7372720463918946971033957 1382385086984802557068867)
                    ·
                      rfl

theorem cell23_8076556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 2, 3, 4].length) (baseStart_8076556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076556 prefixEnd_8076556 := by exact prefixLift 8076556
  have htrace : WordTrace (prefixWord ++ tailWord_8076556) baseStart_8076556 baseEnd_8076556 := by
    simpa [prefixWord, tailWord_8076556, baseEnd_8076556] using wordTrace_append hprefix tailTrace_8076556
  have hstable : (prefixWord ++ tailWord_8076556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076556).length < 2 ^ (prefixWord ++ tailWord_8076556).sum := by decide
  have hdescent : baseEnd_8076556 < baseStart_8076556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076586 : List Nat := [3, 1, 4, 2, 1, 1, 2, 1, 8]
def baseStart_8076586 : Nat := 118140960795 + 8076586 * 2 ^ 59
def prefixEnd_8076586 : Nat := 4983230072969 + 3 ^ 40 * 8076586 * 2
def baseEnd_8076586 : Nat := 460796740597115839314607

theorem tailTrace_8076586 : CollatzResearch.WordTrace tailWord_8076586 prefixEnd_8076586 460796740597115839314607 := by
  unfold tailWord_8076586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73644322979478941979142403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196384861278610511944379741 73644322979478941979142403)
  ·
    refine ⟨110466484469218412968713605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73644322979478941979142403 110466484469218412968713605)
    ·
      refine ⟨20712465837978452431633801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110466484469218412968713605 20712465837978452431633801)
      ·
        refine ⟨15534349378483839323725351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20712465837978452431633801 15534349378483839323725351)
        ·
          refine ⟨23301524067725758985588027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15534349378483839323725351 23301524067725758985588027)
          ·
            refine ⟨34952286101588638478382041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23301524067725758985588027 34952286101588638478382041)
            ·
              refine ⟨26214214576191478858786531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34952286101588638478382041 26214214576191478858786531)
              ·
                refine ⟨39321321864287218288179797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26214214576191478858786531 39321321864287218288179797)
                ·
                  refine ⟨460796740597115839314607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39321321864287218288179797 460796740597115839314607)
                  ·
                    rfl

theorem cell23_8076586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 1, 8].length) (baseStart_8076586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076586 prefixEnd_8076586 := by exact prefixLift 8076586
  have htrace : WordTrace (prefixWord ++ tailWord_8076586) baseStart_8076586 baseEnd_8076586 := by
    simpa [prefixWord, tailWord_8076586, baseEnd_8076586] using wordTrace_append hprefix tailTrace_8076586
  have hstable : (prefixWord ++ tailWord_8076586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076586).length < 2 ^ (prefixWord ++ tailWord_8076586).sum := by decide
  have hdescent : baseEnd_8076586 < baseStart_8076586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076637 : List Nat := [1, 4, 5, 1, 1, 1, 2, 2, 6]
def baseStart_8076637 : Nat := 118140960795 + 8076637 * 2 ^ 59
def prefixEnd_8076637 : Nat := 4983230072969 + 3 ^ 40 * 8076637 * 2
def baseEnd_8076637 : Nat := 460799650320824650477081

theorem tailTrace_8076637 : CollatzResearch.WordTrace tailWord_8076637 prefixEnd_8076637 460799650320824650477081 := by
  unfold tailWord_8076637
  simp only [CollatzResearch.WordTrace]
  refine ⟨294579152040731003626676165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196386101360487335751117443 294579152040731003626676165)
  ·
    refine ⟨55233591007637063180001781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294579152040731003626676165 55233591007637063180001781)
    ·
      refine ⟨5178149156965974673125167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55233591007637063180001781 5178149156965974673125167)
      ·
        refine ⟨7767223735448962009687751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178149156965974673125167 7767223735448962009687751)
        ·
          refine ⟨11650835603173443014531627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767223735448962009687751 11650835603173443014531627)
          ·
            refine ⟨17476253404760164521797441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650835603173443014531627 17476253404760164521797441)
            ·
              refine ⟨13107190053570123391348081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17476253404760164521797441 13107190053570123391348081)
              ·
                refine ⟨9830392540177592543511061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13107190053570123391348081 9830392540177592543511061)
                ·
                  refine ⟨460799650320824650477081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9830392540177592543511061 460799650320824650477081)
                  ·
                    rfl

theorem cell23_8076637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_8076637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076637 prefixEnd_8076637 := by exact prefixLift 8076637
  have htrace : WordTrace (prefixWord ++ tailWord_8076637) baseStart_8076637 baseEnd_8076637 := by
    simpa [prefixWord, tailWord_8076637, baseEnd_8076637] using wordTrace_append hprefix tailTrace_8076637
  have hstable : (prefixWord ++ tailWord_8076637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076637).length < 2 ^ (prefixWord ++ tailWord_8076637).sum := by decide
  have hdescent : baseEnd_8076637 < baseStart_8076637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076647 : List Nat := [1, 1, 5, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_8076647 : Nat := 118140960795 + 8076647 * 2 ^ 59
def prefixEnd_8076647 : Nat := 4983230072969 + 3 ^ 40 * 8076647 * 2
def baseEnd_8076647 : Nat := 4147201987693966815168683

theorem tailTrace_8076647 : CollatzResearch.WordTrace tailWord_8076647 prefixEnd_8076647 4147201987693966815168683 := by
  unfold tailWord_8076647
  simp only [CollatzResearch.WordTrace]
  refine ⟨294579516770694775334540195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196386344513796516889693463 294579516770694775334540195)
  ·
    refine ⟨441869275156042163001810293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294579516770694775334540195 441869275156042163001810293)
    ·
      refine ⟨41425244545878952781419715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441869275156042163001810293 41425244545878952781419715)
      ·
        refine ⟨62137866818818429172129573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41425244545878952781419715 62137866818818429172129573)
        ·
          refine ⟨11650850028528455469774295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62137866818818429172129573 11650850028528455469774295)
          ·
            refine ⟨17476275042792683204661443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11650850028528455469774295 17476275042792683204661443)
            ·
              refine ⟨26214412564189024806992165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17476275042792683204661443 26214412564189024806992165)
              ·
                refine ⟨4915202355785442151311031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26214412564189024806992165 4915202355785442151311031)
                ·
                  refine ⟨7372803533678163226966547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915202355785442151311031 7372803533678163226966547)
                  ·
                    refine ⟨11059205300517244840449821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7372803533678163226966547 11059205300517244840449821)
                    ·
                      refine ⟨4147201987693966815168683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11059205300517244840449821 4147201987693966815168683)
                      ·
                        rfl

theorem cell23_8076647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_8076647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076647 prefixEnd_8076647 := by exact prefixLift 8076647
  have htrace : WordTrace (prefixWord ++ tailWord_8076647) baseStart_8076647 baseEnd_8076647 := by
    simpa [prefixWord, tailWord_8076647, baseEnd_8076647] using wordTrace_append hprefix tailTrace_8076647
  have hstable : (prefixWord ++ tailWord_8076647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076647).length < 2 ^ (prefixWord ++ tailWord_8076647).sum := by decide
  have hdescent : baseEnd_8076647 < baseStart_8076647 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076649 : List Nat := [1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 6]
def baseStart_8076649 : Nat := 118140960795 + 8076649 * 2 ^ 59
def prefixEnd_8076649 : Nat := 4983230072969 + 3 ^ 40 * 8076649 * 2
def baseEnd_8076649 : Nat := 4147203014655275807343673

theorem tailTrace_8076649 : CollatzResearch.WordTrace tailWord_8076649 prefixEnd_8076649 4147203014655275807343673 := by
  unfold tailWord_8076649
  simp only [CollatzResearch.WordTrace]
  refine ⟨294579589716687529676113001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196386393144458353117408667 294579589716687529676113001)
  ·
    refine ⟨220934692287515647257084751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294579589716687529676113001 220934692287515647257084751)
    ·
      refine ⟨331402038431273470885627127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220934692287515647257084751 331402038431273470885627127)
      ·
        refine ⟨497103057646910206328440691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331402038431273470885627127 497103057646910206328440691)
        ·
          refine ⟨745654586470365309492661037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497103057646910206328440691 745654586470365309492661037)
          ·
            refine ⟨279620469926386991059747889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745654586470365309492661037 279620469926386991059747889)
            ·
              refine ⟨209715352444790243294810917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279620469926386991059747889 209715352444790243294810917)
              ·
                refine ⟨39321628583398170617777047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209715352444790243294810917 39321628583398170617777047)
                ·
                  refine ⟨58982442875097255926665571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39321628583398170617777047 58982442875097255926665571)
                  ·
                    refine ⟨88473664312645883889998357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58982442875097255926665571 88473664312645883889998357)
                    ·
                      refine ⟨4147203014655275807343673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88473664312645883889998357 4147203014655275807343673)
                      ·
                        rfl

theorem cell23_8076649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 1, 6].length) (baseStart_8076649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076649 prefixEnd_8076649 := by exact prefixLift 8076649
  have htrace : WordTrace (prefixWord ++ tailWord_8076649) baseStart_8076649 baseEnd_8076649 := by
    simpa [prefixWord, tailWord_8076649, baseEnd_8076649] using wordTrace_append hprefix tailTrace_8076649
  have hstable : (prefixWord ++ tailWord_8076649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076649).length < 2 ^ (prefixWord ++ tailWord_8076649).sum := by decide
  have hdescent : baseEnd_8076649 < baseStart_8076649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076656 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_8076656 : Nat := 118140960795 + 8076656 * 2 ^ 59
def prefixEnd_8076656 : Nat := 4983230072969 + 3 ^ 40 * 8076656 * 2
def baseEnd_8076656 : Nat := 4147206609019857279956141

theorem tailTrace_8076656 : CollatzResearch.WordTrace tailWord_8076656 prefixEnd_8076656 4147206609019857279956141 := by
  unfold tailWord_8076656
  simp only [CollatzResearch.WordTrace]
  refine ⟨147289922513831084935808911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196386563351774779914411881 147289922513831084935808911)
  ·
    refine ⟨220934883770746627403713367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147289922513831084935808911 220934883770746627403713367)
    ·
      refine ⟨331402325656119941105570051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220934883770746627403713367 331402325656119941105570051)
      ·
        refine ⟨497103488484179911658355077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331402325656119941105570051 497103488484179911658355077)
        ·
          refine ⟨93206904090783733435941577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 497103488484179911658355077 93206904090783733435941577)
          ·
            refine ⟨69905178068087800076956183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93206904090783733435941577 69905178068087800076956183)
            ·
              refine ⟨104857767102131700115434275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69905178068087800076956183 104857767102131700115434275)
              ·
                refine ⟨157286650653197550173151413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104857767102131700115434275 157286650653197550173151413)
                ·
                  refine ⟨14745623498737270328732945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157286650653197550173151413 14745623498737270328732945)
                  ·
                    refine ⟨11059217624052952746549709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14745623498737270328732945 11059217624052952746549709)
                    ·
                      refine ⟨4147206609019857279956141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11059217624052952746549709 4147206609019857279956141)
                      ·
                        rfl

theorem cell23_8076656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_8076656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076656 prefixEnd_8076656 := by exact prefixLift 8076656
  have htrace : WordTrace (prefixWord ++ tailWord_8076656) baseStart_8076656 baseEnd_8076656 := by
    simpa [prefixWord, tailWord_8076656, baseEnd_8076656] using wordTrace_append hprefix tailTrace_8076656
  have hstable : (prefixWord ++ tailWord_8076656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076656).length < 2 ^ (prefixWord ++ tailWord_8076656).sum := by decide
  have hdescent : baseEnd_8076656 < baseStart_8076656 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076674 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_8076674 : Nat := 118140960795 + 8076674 * 2 ^ 59
def prefixEnd_8076674 : Nat := 4983230072969 + 3 ^ 40 * 8076674 * 2
def baseEnd_8076674 : Nat := 4147215851671638209531059

theorem tailTrace_8076674 : CollatzResearch.WordTrace tailWord_8076674 prefixEnd_8076674 4147215851671638209531059 := by
  unfold tailWord_8076674
  simp only [CollatzResearch.WordTrace]
  refine ⟨73645125385399239736443269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196387001027731305963848717 73645125385399239736443269)
  ·
    refine ⟨13808461009762357450583113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73645125385399239736443269 13808461009762357450583113)
    ·
      refine ⟨10356345757321768087937335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13808461009762357450583113 10356345757321768087937335)
      ·
        refine ⟨15534518635982652131906003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10356345757321768087937335 15534518635982652131906003)
        ·
          refine ⟨23301777953973978197859005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15534518635982652131906003 23301777953973978197859005)
          ·
            refine ⟨8738166732740241824197127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23301777953973978197859005 8738166732740241824197127)
            ·
              refine ⟨13107250099110362736295691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738166732740241824197127 13107250099110362736295691)
              ·
                refine ⟨19660875148665544104443537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13107250099110362736295691 19660875148665544104443537)
                ·
                  refine ⟨14745656361499158078332653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19660875148665544104443537 14745656361499158078332653)
                  ·
                    refine ⟨5529621135562184279374745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14745656361499158078332653 5529621135562184279374745)
                    ·
                      refine ⟨4147215851671638209531059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529621135562184279374745 4147215851671638209531059)
                      ·
                        rfl

theorem cell23_8076674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_8076674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076674 prefixEnd_8076674 := by exact prefixLift 8076674
  have htrace : WordTrace (prefixWord ++ tailWord_8076674) baseStart_8076674 baseEnd_8076674 := by
    simpa [prefixWord, tailWord_8076674, baseEnd_8076674] using wordTrace_append hprefix tailTrace_8076674
  have hstable : (prefixWord ++ tailWord_8076674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076674).length < 2 ^ (prefixWord ++ tailWord_8076674).sum := by decide
  have hdescent : baseEnd_8076674 < baseStart_8076674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076689 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 4, 7]
def baseStart_8076689 : Nat := 118140960795 + 8076689 * 2 ^ 59
def prefixEnd_8076689 : Nat := 4983230072969 + 3 ^ 40 * 8076689 * 2
def baseEnd_8076689 : Nat := 1382407851293818550281163

theorem tailTrace_8076689 : CollatzResearch.WordTrace tailWord_8076689 prefixEnd_8076689 1382407851293818550281163 := by
  unfold tailWord_8076689
  simp only [CollatzResearch.WordTrace]
  refine ⟨294581048636542616507569121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196387365757695077671712747 294581048636542616507569121)
  ·
    refine ⟨220935786477406962380676841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294581048636542616507569121 220935786477406962380676841)
    ·
      refine ⟨165701839858055221785507631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220935786477406962380676841 165701839858055221785507631)
      ·
        refine ⟨248552759787082832678261447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165701839858055221785507631 248552759787082832678261447)
        ·
          refine ⟨372829139680624249017392171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248552759787082832678261447 372829139680624249017392171)
          ·
            refine ⟨559243709520936373526088257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372829139680624249017392171 559243709520936373526088257)
            ·
              refine ⟨419432782140702280144566193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 559243709520936373526088257 419432782140702280144566193)
              ·
                refine ⟨314574586605526710108424645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419432782140702280144566193 314574586605526710108424645)
                ·
                  refine ⟨58982734988536258145329621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314574586605526710108424645 58982734988536258145329621)
                  ·
                    refine ⟨1382407851293818550281163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58982734988536258145329621 1382407851293818550281163)
                    ·
                      rfl

theorem cell23_8076689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_8076689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076689 prefixEnd_8076689 := by exact prefixLift 8076689
  have htrace : WordTrace (prefixWord ++ tailWord_8076689) baseStart_8076689 baseEnd_8076689 := by
    simpa [prefixWord, tailWord_8076689, baseEnd_8076689] using wordTrace_append hprefix tailTrace_8076689
  have hstable : (prefixWord ++ tailWord_8076689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076689).length < 2 ^ (prefixWord ++ tailWord_8076689).sum := by decide
  have hdescent : baseEnd_8076689 < baseStart_8076689 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076699 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5]
def baseStart_8076699 : Nat := 118140960795 + 8076699 * 2 ^ 59
def prefixEnd_8076699 : Nat := 4983230072969 + 3 ^ 40 * 8076699 * 2
def baseEnd_8076699 : Nat := 4147228688688000611718443

theorem tailTrace_8076699 : CollatzResearch.WordTrace tailWord_8076699 prefixEnd_8076699 4147228688688000611718443 := by
  unfold tailWord_8076699
  simp only [CollatzResearch.WordTrace]
  refine ⟨294581413366506388215433151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196387608911004258810288767 294581413366506388215433151)
  ·
    refine ⟨441872120049759582323149727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294581413366506388215433151 441872120049759582323149727)
    ·
      refine ⟨662808180074639373484724591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441872120049759582323149727 662808180074639373484724591)
      ·
        refine ⟨994212270111959060227086887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662808180074639373484724591 994212270111959060227086887)
        ·
          refine ⟨1491318405167938590340630331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 994212270111959060227086887 1491318405167938590340630331)
          ·
            refine ⟨2236977607751907885510945497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1491318405167938590340630331 2236977607751907885510945497)
            ·
              refine ⟨1677733205813930914133209123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2236977607751907885510945497 1677733205813930914133209123)
              ·
                refine ⟨2516599808720896371199813685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1677733205813930914133209123 2516599808720896371199813685)
                ·
                  refine ⟨235931232067584034799982533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2516599808720896371199813685 235931232067584034799982533)
                  ·
                    refine ⟨44237106012672006524996725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235931232067584034799982533 44237106012672006524996725)
                    ·
                      refine ⟨4147228688688000611718443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44237106012672006524996725 4147228688688000611718443)
                      ·
                        rfl

theorem cell23_8076699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 5].length) (baseStart_8076699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076699 prefixEnd_8076699 := by exact prefixLift 8076699
  have htrace : WordTrace (prefixWord ++ tailWord_8076699) baseStart_8076699 baseEnd_8076699 := by
    simpa [prefixWord, tailWord_8076699, baseEnd_8076699] using wordTrace_append hprefix tailTrace_8076699
  have hstable : (prefixWord ++ tailWord_8076699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076699).length < 2 ^ (prefixWord ++ tailWord_8076699).sum := by decide
  have hdescent : baseEnd_8076699 < baseStart_8076699 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076743 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 3, 4, 2]
def baseStart_8076743 : Nat := 118140960795 + 8076743 * 2 ^ 59
def prefixEnd_8076743 : Nat := 4983230072969 + 3 ^ 40 * 8076743 * 2
def baseEnd_8076743 : Nat := 4147251281836798439568241

theorem tailTrace_8076743 : CollatzResearch.WordTrace tailWord_8076743 prefixEnd_8076743 4147251281836798439568241 := by
  unfold tailWord_8076743
  simp only [CollatzResearch.WordTrace]
  refine ⟨294583018178346983730034883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196388678785564655820023255 294583018178346983730034883)
  ·
    refine ⟨441874527267520475595052325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294583018178346983730034883 441874527267520475595052325)
    ·
      refine ⟨82851473862660089174072311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441874527267520475595052325 82851473862660089174072311)
      ·
        refine ⟨124277210793990133761108467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82851473862660089174072311 124277210793990133761108467)
        ·
          refine ⟨186415816190985200641662701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124277210793990133761108467 186415816190985200641662701)
          ·
            refine ⟨69905931071619450240623513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186415816190985200641662701 69905931071619450240623513)
            ·
              refine ⟨52429448303714587680467635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69905931071619450240623513 52429448303714587680467635)
              ·
                refine ⟨78644172455571881520701453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52429448303714587680467635 78644172455571881520701453)
                ·
                  refine ⟨29491564670839455570263045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78644172455571881520701453 29491564670839455570263045)
                  ·
                    refine ⟨5529668375782397919424321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29491564670839455570263045 5529668375782397919424321)
                    ·
                      refine ⟨4147251281836798439568241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529668375782397919424321 4147251281836798439568241)
                      ·
                        rfl

theorem cell23_8076743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 3, 4, 2].length) (baseStart_8076743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076743 prefixEnd_8076743 := by exact prefixLift 8076743
  have htrace : WordTrace (prefixWord ++ tailWord_8076743) baseStart_8076743 baseEnd_8076743 := by
    simpa [prefixWord, tailWord_8076743, baseEnd_8076743] using wordTrace_append hprefix tailTrace_8076743
  have hstable : (prefixWord ++ tailWord_8076743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076743).length < 2 ^ (prefixWord ++ tailWord_8076743).sum := by decide
  have hdescent : baseEnd_8076743 < baseStart_8076743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076746 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5]
def baseStart_8076746 : Nat := 118140960795 + 8076746 * 2 ^ 59
def prefixEnd_8076746 : Nat := 4983230072969 + 3 ^ 40 * 8076746 * 2
def baseEnd_8076746 : Nat := 4147252822278761927830727

theorem tailTrace_8076746 : CollatzResearch.WordTrace tailWord_8076746 prefixEnd_8076746 4147252822278761927830727 := by
  unfold tailWord_8076746
  simp only [CollatzResearch.WordTrace]
  refine ⟨73645781899334028810598523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196388751731557410161596061 73645781899334028810598523)
  ·
    refine ⟨110468672849001043215897785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73645781899334028810598523 110468672849001043215897785)
    ·
      refine ⟨82851504636750782411923339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110468672849001043215897785 82851504636750782411923339)
      ·
        refine ⟨124277256955126173617885009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82851504636750782411923339 124277256955126173617885009)
        ·
          refine ⟨93207942716344630213413757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124277256955126173617885009 93207942716344630213413757)
          ·
            refine ⟨34952978518629236330030159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93207942716344630213413757 34952978518629236330030159)
            ·
              refine ⟨52429467777943854495045239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34952978518629236330030159 52429467777943854495045239)
              ·
                refine ⟨78644201666915781742567859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52429467777943854495045239 78644201666915781742567859)
                ·
                  refine ⟨117966302500373672613851789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78644201666915781742567859 117966302500373672613851789)
                  ·
                    refine ⟨44237363437640127230194421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117966302500373672613851789 44237363437640127230194421)
                    ·
                      refine ⟨4147252822278761927830727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44237363437640127230194421 4147252822278761927830727)
                      ·
                        rfl

theorem cell23_8076746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 3, 5].length) (baseStart_8076746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076746 prefixEnd_8076746 := by exact prefixLift 8076746
  have htrace : WordTrace (prefixWord ++ tailWord_8076746) baseStart_8076746 baseEnd_8076746 := by
    simpa [prefixWord, tailWord_8076746, baseEnd_8076746] using wordTrace_append hprefix tailTrace_8076746
  have hstable : (prefixWord ++ tailWord_8076746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076746).length < 2 ^ (prefixWord ++ tailWord_8076746).sum := by decide
  have hdescent : baseEnd_8076746 < baseStart_8076746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076760 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 4, 2, 2]
def baseStart_8076760 : Nat := 118140960795 + 8076760 * 2 ^ 59
def prefixEnd_8076760 : Nat := 4983230072969 + 3 ^ 40 * 8076760 * 2
def baseEnd_8076760 : Nat := 4147260011007924873055663

theorem tailTrace_8076760 : CollatzResearch.WordTrace tailWord_8076760 prefixEnd_8076760 4147260011007924873055663 := by
  unfold tailWord_8076760
  simp only [CollatzResearch.WordTrace]
  refine ⟨147291819109642697816701867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196389092146190263755602489 147291819109642697816701867)
  ·
    refine ⟨220937728664464046725052801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147291819109642697816701867 220937728664464046725052801)
    ·
      refine ⟨165703296498348035043789601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220937728664464046725052801 165703296498348035043789601)
      ·
        refine ⟨124277472373761026282842201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165703296498348035043789601 124277472373761026282842201)
        ·
          refine ⟨93208104280320769712131651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124277472373761026282842201 93208104280320769712131651)
          ·
            refine ⟨139812156420481154568197477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93208104280320769712131651 139812156420481154568197477)
            ·
              refine ⟨26214779328840216481537027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139812156420481154568197477 26214779328840216481537027)
              ·
                refine ⟨39322168993260324722305541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26214779328840216481537027 39322168993260324722305541)
                ·
                  refine ⟨7372906686236310885432289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39322168993260324722305541 7372906686236310885432289)
                  ·
                    refine ⟨5529680014677233164074217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7372906686236310885432289 5529680014677233164074217)
                    ·
                      refine ⟨4147260011007924873055663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529680014677233164074217 4147260011007924873055663)
                      ·
                        rfl

theorem cell23_8076760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_8076760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076760 prefixEnd_8076760 := by exact prefixLift 8076760
  have htrace : WordTrace (prefixWord ++ tailWord_8076760) baseStart_8076760 baseEnd_8076760 := by
    simpa [prefixWord, tailWord_8076760, baseEnd_8076760] using wordTrace_append hprefix tailTrace_8076760
  have hstable : (prefixWord ++ tailWord_8076760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076760).length < 2 ^ (prefixWord ++ tailWord_8076760).sum := by decide
  have hdescent : baseEnd_8076760 < baseStart_8076760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076781 : List Nat := [1, 5, 1, 3, 3, 1, 1, 2, 1, 3, 2]
def baseStart_8076781 : Nat := 118140960795 + 8076781 * 2 ^ 59
def prefixEnd_8076781 : Nat := 4983230072969 + 3 ^ 40 * 8076781 * 2
def baseEnd_8076781 : Nat := 4147270794101669290893067

theorem tailTrace_8076781 : CollatzResearch.WordTrace tailWord_8076781 prefixEnd_8076781 4147270794101669290893067 := by
  unfold tailWord_8076781
  simp only [CollatzResearch.WordTrace]
  refine ⟨294584404152209316219918197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196389602768139544146612131 294584404152209316219918197)
  ·
    refine ⟨27617287889269623395617331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294584404152209316219918197 27617287889269623395617331)
    ·
      refine ⟨41425931833904435093425997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27617287889269623395617331 41425931833904435093425997)
      ·
        refine ⟨15534724437714163160034749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41425931833904435093425997 15534724437714163160034749)
        ·
          refine ⟨5825521664142811185013031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15534724437714163160034749 5825521664142811185013031)
          ·
            refine ⟨8738282496214216777519547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5825521664142811185013031 8738282496214216777519547)
            ·
              refine ⟨13107423744321325166279321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738282496214216777519547 13107423744321325166279321)
              ·
                refine ⟨9830567808240993874709491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13107423744321325166279321 9830567808240993874709491)
                ·
                  refine ⟨14745851712361490812064237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9830567808240993874709491 14745851712361490812064237)
                  ·
                    refine ⟨5529694392135559054524089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14745851712361490812064237 5529694392135559054524089)
                    ·
                      refine ⟨4147270794101669290893067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529694392135559054524089 4147270794101669290893067)
                      ·
                        rfl

theorem cell23_8076781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_8076781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076781 prefixEnd_8076781 := by exact prefixLift 8076781
  have htrace : WordTrace (prefixWord ++ tailWord_8076781) baseStart_8076781 baseEnd_8076781 := by
    simpa [prefixWord, tailWord_8076781, baseEnd_8076781] using wordTrace_append hprefix tailTrace_8076781
  have hstable : (prefixWord ++ tailWord_8076781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076781).length < 2 ^ (prefixWord ++ tailWord_8076781).sum := by decide
  have hdescent : baseEnd_8076781 < baseStart_8076781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076796 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 1, 7]
def baseStart_8076796 : Nat := 118140960795 + 8076796 * 2 ^ 59
def prefixEnd_8076796 : Nat := 4983230072969 + 3 ^ 40 * 8076796 * 2
def baseEnd_8076796 : Nat := 1382426165437162244068499

theorem tailTrace_8076796 : CollatzResearch.WordTrace tailWord_8076796 prefixEnd_8076796 1382426165437162244068499 := by
  unfold tailWord_8076796
  simp only [CollatzResearch.WordTrace]
  refine ⟨147292475623577486890857121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196389967498103315854476161 147292475623577486890857121)
  ·
    refine ⟨110469356717683115168142841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147292475623577486890857121 110469356717683115168142841)
    ·
      refine ⟨82852017538262336376107131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110469356717683115168142841 82852017538262336376107131)
      ·
        refine ⟨124278026307393504564160697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82852017538262336376107131 124278026307393504564160697)
        ·
          refine ⟨93208519730545128423120523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124278026307393504564160697 93208519730545128423120523)
          ·
            refine ⟨139812779595817692634680785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93208519730545128423120523 139812779595817692634680785)
            ·
              refine ⟨104859584696863269476010589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139812779595817692634680785 104859584696863269476010589)
              ·
                refine ⟨39322344261323726053503971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104859584696863269476010589 39322344261323726053503971)
                ·
                  refine ⟨58983516391985589080255957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39322344261323726053503971 58983516391985589080255957)
                  ·
                    refine ⟨1382426165437162244068499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58983516391985589080255957 1382426165437162244068499)
                    ·
                      rfl

theorem cell23_8076796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 1, 7].length) (baseStart_8076796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076796 prefixEnd_8076796 := by exact prefixLift 8076796
  have htrace : WordTrace (prefixWord ++ tailWord_8076796) baseStart_8076796 baseEnd_8076796 := by
    simpa [prefixWord, tailWord_8076796, baseEnd_8076796] using wordTrace_append hprefix tailTrace_8076796
  have hstable : (prefixWord ++ tailWord_8076796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076796).length < 2 ^ (prefixWord ++ tailWord_8076796).sum := by decide
  have hdescent : baseEnd_8076796 < baseStart_8076796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076826 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 2, 8]
def baseStart_8076826 : Nat := 118140960795 + 8076826 * 2 ^ 59
def prefixEnd_8076826 : Nat := 4983230072969 + 3 ^ 40 * 8076826 * 2
def baseEnd_8076826 : Nat := 1382431300243707204943453

theorem tailTrace_8076826 : CollatzResearch.WordTrace tailWord_8076826 prefixEnd_8076826 1382431300243707204943453 := by
  unfold tailWord_8076826
  simp only [CollatzResearch.WordTrace]
  refine ⟨73646511359261572226326583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196390696958030859270204221 73646511359261572226326583)
  ·
    refine ⟨110469767038892358339489875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73646511359261572226326583 110469767038892358339489875)
    ·
      refine ⟨165704650558338537509234813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110469767038892358339489875 165704650558338537509234813)
      ·
        refine ⟨62139243959376951565963055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165704650558338537509234813 62139243959376951565963055)
        ·
          refine ⟨93208865939065427348944583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62139243959376951565963055 93208865939065427348944583)
          ·
            refine ⟨139813298908598141023416875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93208865939065427348944583 139813298908598141023416875)
            ·
              refine ⟨209719948362897211535125313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139813298908598141023416875 209719948362897211535125313)
              ·
                refine ⟨157289961272172908651343985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209719948362897211535125313 157289961272172908651343985)
                ·
                  refine ⟨117967470954129681488507989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157289961272172908651343985 117967470954129681488507989)
                  ·
                    refine ⟨1382431300243707204943453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117967470954129681488507989 1382431300243707204943453)
                    ·
                      rfl

theorem cell23_8076826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_8076826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076826 prefixEnd_8076826 := by exact prefixLift 8076826
  have htrace : WordTrace (prefixWord ++ tailWord_8076826) baseStart_8076826 baseEnd_8076826 := by
    simpa [prefixWord, tailWord_8076826, baseEnd_8076826] using wordTrace_append hprefix tailTrace_8076826
  have hstable : (prefixWord ++ tailWord_8076826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076826).length < 2 ^ (prefixWord ++ tailWord_8076826).sum := by decide
  have hdescent : baseEnd_8076826 < baseStart_8076826 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076903 : List Nat := [1, 1, 5, 1, 1, 1, 2, 3, 3, 5]
def baseStart_8076903 : Nat := 118140960795 + 8076903 * 2 ^ 59
def prefixEnd_8076903 : Nat := 4983230072969 + 3 ^ 40 * 8076903 * 2
def baseEnd_8076903 : Nat := 1382444479580505937855835

theorem tailTrace_8076903 : CollatzResearch.WordTrace tailWord_8076903 prefixEnd_8076903 1382444479580505937855835 := by
  unfold tailWord_8076903
  simp only [CollatzResearch.WordTrace]
  refine ⟨294588853857767331055859363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196392569238511554037239575 294588853857767331055859363)
  ·
    refine ⟨441883280786650996583789045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294588853857767331055859363 441883280786650996583789045)
    ·
      refine ⟨41426557573748530929730223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441883280786650996583789045 41426557573748530929730223)
      ·
        refine ⟨62139836360622796394595335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41426557573748530929730223 62139836360622796394595335)
        ·
          refine ⟨93209754540934194591893003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62139836360622796394595335 93209754540934194591893003)
          ·
            refine ⟨139814631811401291887839505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93209754540934194591893003 139814631811401291887839505)
            ·
              refine ⟨104860973858550968915879629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139814631811401291887839505 104860973858550968915879629)
              ·
                refine ⟨39322865196956613343454861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104860973858550968915879629 39322865196956613343454861)
                ·
                  refine ⟨14746074448858730003795573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39322865196956613343454861 14746074448858730003795573)
                  ·
                    refine ⟨1382444479580505937855835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14746074448858730003795573 1382444479580505937855835)
                    ·
                      rfl

theorem cell23_8076903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_8076903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076903 prefixEnd_8076903 := by exact prefixLift 8076903
  have htrace : WordTrace (prefixWord ++ tailWord_8076903) baseStart_8076903 baseEnd_8076903 := by
    simpa [prefixWord, tailWord_8076903, baseEnd_8076903] using wordTrace_append hprefix tailTrace_8076903
  have hstable : (prefixWord ++ tailWord_8076903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076903).length < 2 ^ (prefixWord ++ tailWord_8076903).sum := by decide
  have hdescent : baseEnd_8076903 < baseStart_8076903 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8076957 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_8076957 : Nat := 118140960795 + 8076957 * 2 ^ 59
def prefixEnd_8076957 : Nat := 4983230072969 + 3 ^ 40 * 8076957 * 2
def baseEnd_8076957 : Nat := 4147361166696860602292257

theorem tailTrace_8076957 : CollatzResearch.WordTrace tailWord_8076957 prefixEnd_8076957 4147361166696860602292257 := by
  unfold tailWord_8076957
  simp only [CollatzResearch.WordTrace]
  refine ⟨294590823399571698278325125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196393882266381132185550083 294590823399571698278325125)
  ·
    refine ⟨55235779387419693427185961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294590823399571698278325125 55235779387419693427185961)
    ·
      refine ⟨41426834540564770070389471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55235779387419693427185961 41426834540564770070389471)
      ·
        refine ⟨62140251810847155105584207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41426834540564770070389471 62140251810847155105584207)
        ·
          refine ⟨93210377716270732658376311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62140251810847155105584207 93210377716270732658376311)
          ·
            refine ⟨139815566574406098987564467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93210377716270732658376311 139815566574406098987564467)
            ·
              refine ⟨209723349861609148481346701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139815566574406098987564467 209723349861609148481346701)
              ·
                refine ⟨78646256198103430680505013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209723349861609148481346701 78646256198103430680505013)
                ·
                  refine ⟨7373086518572196626297345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78646256198103430680505013 7373086518572196626297345)
                  ·
                    refine ⟨5529814888929147469723009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7373086518572196626297345 5529814888929147469723009)
                    ·
                      refine ⟨4147361166696860602292257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529814888929147469723009 4147361166696860602292257)
                      ·
                        rfl

theorem cell23_8076957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_8076957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8076957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8076957 prefixEnd_8076957 := by exact prefixLift 8076957
  have htrace : WordTrace (prefixWord ++ tailWord_8076957) baseStart_8076957 baseEnd_8076957 := by
    simpa [prefixWord, tailWord_8076957, baseEnd_8076957] using wordTrace_append hprefix tailTrace_8076957
  have hstable : (prefixWord ++ tailWord_8076957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8076957).length < 2 ^ (prefixWord ++ tailWord_8076957).sum := by decide
  have hdescent : baseEnd_8076957 < baseStart_8076957 := by decide
  rcases family_descends (prefixWord ++ tailWord_8076957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077017 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 3, 3, 2]
def baseStart_8077017 : Nat := 118140960795 + 8077017 * 2 ^ 59
def prefixEnd_8077017 : Nat := 4983230072969 + 3 ^ 40 * 8077017 * 2
def baseEnd_8077017 : Nat := 4147391975536130367541981

theorem tailTrace_8077017 : CollatzResearch.WordTrace tailWord_8077017 prefixEnd_8077017 4147391975536130367541981 := by
  unfold tailWord_8077017
  simp only [CollatzResearch.WordTrace]
  refine ⟨294593011779354328525509305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196395341186236219017006203 294593011779354328525509305)
  ·
    refine ⟨220944758834515746394131979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294593011779354328525509305 220944758834515746394131979)
    ·
      refine ⟨331417138251773619591197969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220944758834515746394131979 331417138251773619591197969)
      ·
        refine ⟨248562853688830214693398477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 331417138251773619591197969 248562853688830214693398477)
        ·
          refine ⟨93211070133311330510024429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248562853688830214693398477 93211070133311330510024429)
          ·
            refine ⟨34954151299991748941259161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93211070133311330510024429 34954151299991748941259161)
            ·
              refine ⟨26215613474993811705944371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34954151299991748941259161 26215613474993811705944371)
              ·
                refine ⟨39323420212490717558916557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26215613474993811705944371 39323420212490717558916557)
                ·
                  refine ⟨14746282579684019084593709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39323420212490717558916557 14746282579684019084593709)
                  ·
                    refine ⟨5529855967381507156722641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14746282579684019084593709 5529855967381507156722641)
                    ·
                      refine ⟨4147391975536130367541981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529855967381507156722641 4147391975536130367541981)
                      ·
                        rfl

theorem cell23_8077017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 3, 3, 2].length) (baseStart_8077017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077017 prefixEnd_8077017 := by exact prefixLift 8077017
  have htrace : WordTrace (prefixWord ++ tailWord_8077017) baseStart_8077017 baseEnd_8077017 := by
    simpa [prefixWord, tailWord_8077017, baseEnd_8077017] using wordTrace_append hprefix tailTrace_8077017
  have hstable : (prefixWord ++ tailWord_8077017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077017).length < 2 ^ (prefixWord ++ tailWord_8077017).sum := by decide
  have hdescent : baseEnd_8077017 < baseStart_8077017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077023 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 1, 8]
def baseStart_8077023 : Nat := 118140960795 + 8077023 * 2 ^ 59
def prefixEnd_8077023 : Nat := 4983230072969 + 3 ^ 40 * 8077023 * 2
def baseEnd_8077023 : Nat := 1382465018806685781355651

theorem tailTrace_8077023 : CollatzResearch.WordTrace tailWord_8077023 prefixEnd_8077023 1382465018806685781355651 := by
  unfold tailWord_8077023
  simp only [CollatzResearch.WordTrace]
  refine ⟨294593230617332591550227723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196395487078221727700151815 294593230617332591550227723)
  ·
    refine ⟨441889845925998887325341585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294593230617332591550227723 441889845925998887325341585)
    ·
      refine ⟨331417384444499165494006189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441889845925998887325341585 331417384444499165494006189)
      ·
        refine ⟨124281519166687187060252321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331417384444499165494006189 124281519166687187060252321)
        ·
          refine ⟨93211139375015390295189241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124281519166687187060252321 93211139375015390295189241)
          ·
            refine ⟨69908354531261542721391931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93211139375015390295189241 69908354531261542721391931)
            ·
              refine ⟨104862531796892314082087897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69908354531261542721391931 104862531796892314082087897)
              ·
                refine ⟨78646898847669235561565923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104862531796892314082087897 78646898847669235561565923)
                ·
                  refine ⟨117970348271503853342348885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78646898847669235561565923 117970348271503853342348885)
                  ·
                    refine ⟨1382465018806685781355651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117970348271503853342348885 1382465018806685781355651)
                    ·
                      rfl

theorem cell23_8077023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_8077023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077023 prefixEnd_8077023 := by exact prefixLift 8077023
  have htrace : WordTrace (prefixWord ++ tailWord_8077023) baseStart_8077023 baseEnd_8077023 := by
    simpa [prefixWord, tailWord_8077023, baseEnd_8077023] using wordTrace_append hprefix tailTrace_8077023
  have hstable : (prefixWord ++ tailWord_8077023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077023).length < 2 ^ (prefixWord ++ tailWord_8077023).sum := by decide
  have hdescent : baseEnd_8077023 < baseStart_8077023 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077033 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 5]
def baseStart_8077033 : Nat := 118140960795 + 8077033 * 2 ^ 59
def prefixEnd_8077033 : Nat := 4983230072969 + 3 ^ 40 * 8077033 * 2
def baseEnd_8077033 : Nat := 4147400191226602304941907

theorem tailTrace_8077033 : CollatzResearch.WordTrace tailWord_8077033 prefixEnd_8077033 4147400191226602304941907 := by
  unfold tailWord_8077033
  simp only [CollatzResearch.WordTrace]
  refine ⟨294593595347296363258091753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196395730231530908838727835 294593595347296363258091753)
  ·
    refine ⟨220945196510472272443568815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294593595347296363258091753 220945196510472272443568815)
    ·
      refine ⟨331417794765708408665353223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220945196510472272443568815 331417794765708408665353223)
      ·
        refine ⟨497126692148562612998029835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331417794765708408665353223 497126692148562612998029835)
        ·
          refine ⟨745690038222843919497044753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497126692148562612998029835 745690038222843919497044753)
          ·
            refine ⟨559267528667132939622783565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745690038222843919497044753 559267528667132939622783565)
            ·
              refine ⟨209725323250174852358543837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559267528667132939622783565 209725323250174852358543837)
              ·
                refine ⟨78646996218815569634453939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209725323250174852358543837 78646996218815569634453939)
                ·
                  refine ⟨117970494328223354451680909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78646996218815569634453939 117970494328223354451680909)
                  ·
                    refine ⟨44238935373083757919380341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117970494328223354451680909 44238935373083757919380341)
                    ·
                      refine ⟨4147400191226602304941907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44238935373083757919380341 4147400191226602304941907)
                      ·
                        rfl

theorem cell23_8077033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 5].length) (baseStart_8077033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077033 prefixEnd_8077033 := by exact prefixLift 8077033
  have htrace : WordTrace (prefixWord ++ tailWord_8077033) baseStart_8077033 baseEnd_8077033 := by
    simpa [prefixWord, tailWord_8077033, baseEnd_8077033] using wordTrace_append hprefix tailTrace_8077033
  have hstable : (prefixWord ++ tailWord_8077033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077033).length < 2 ^ (prefixWord ++ tailWord_8077033).sum := by decide
  have hdescent : baseEnd_8077033 < baseStart_8077033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077062 : List Nat := [6, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8077062 : Nat := 118140960795 + 8077062 * 2 ^ 59
def prefixEnd_8077062 : Nat := 4983230072969 + 3 ^ 40 * 8077062 * 2
def baseEnd_8077062 : Nat := 4147415082165582691479275

theorem tailTrace_8077062 : CollatzResearch.WordTrace tailWord_8077062 prefixEnd_8077062 4147415082165582691479275 := by
  unfold tailWord_8077062
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206082908255978162840545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196396435376127534140598293 9206082908255978162840545)
  ·
    refine ⟨6904562181191983622130409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9206082908255978162840545 6904562181191983622130409)
    ·
      refine ⟨5178421635893987716597807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6904562181191983622130409 5178421635893987716597807)
      ·
        refine ⟨7767632453840981574896711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178421635893987716597807 7767632453840981574896711)
        ·
          refine ⟨11651448680761472362345067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767632453840981574896711 11651448680761472362345067)
          ·
            refine ⟨17477173021142208543517601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11651448680761472362345067 17477173021142208543517601)
            ·
              refine ⟨13107879765856656407638201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17477173021142208543517601 13107879765856656407638201)
              ·
                refine ⟨9830909824392492305728651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13107879765856656407638201 9830909824392492305728651)
                ·
                  refine ⟨14746364736588738458592977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9830909824392492305728651 14746364736588738458592977)
                  ·
                    refine ⟨11059773552441553843944733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14746364736588738458592977 11059773552441553843944733)
                    ·
                      refine ⟨4147415082165582691479275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11059773552441553843944733 4147415082165582691479275)
                      ·
                        rfl

theorem cell23_8077062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8077062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077062 prefixEnd_8077062 := by exact prefixLift 8077062
  have htrace : WordTrace (prefixWord ++ tailWord_8077062) baseStart_8077062 baseEnd_8077062 := by
    simpa [prefixWord, tailWord_8077062, baseEnd_8077062] using wordTrace_append hprefix tailTrace_8077062
  have hstable : (prefixWord ++ tailWord_8077062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077062).length < 2 ^ (prefixWord ++ tailWord_8077062).sum := by decide
  have hdescent : baseEnd_8077062 < baseStart_8077062 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077070 : List Nat := [4, 1, 1, 2, 1, 1, 4, 2, 7]
def baseStart_8077070 : Nat := 118140960795 + 8077070 * 2 ^ 59
def prefixEnd_8077070 : Nat := 4983230072969 + 3 ^ 40 * 8077070 * 2
def baseEnd_8077070 : Nat := 460824354445646517797693

theorem tailTrace_8077070 : CollatzResearch.WordTrace tailWord_8077070 prefixEnd_8077070 460824354445646517797693 := by
  unfold tailWord_8077070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36824368106020289822148583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196396629898774879051459109 36824368106020289822148583)
  ·
    refine ⟨55236552159030434733222875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36824368106020289822148583 55236552159030434733222875)
    ·
      refine ⟨82854828238545652099834313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55236552159030434733222875 82854828238545652099834313)
      ·
        refine ⟨62141121178909239074875735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82854828238545652099834313 62141121178909239074875735)
        ·
          refine ⟨93211681768363858612313603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62141121178909239074875735 93211681768363858612313603)
          ·
            refine ⟨139817522652545787918470405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93211681768363858612313603 139817522652545787918470405)
            ·
              refine ⟨26215785497352335234713201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139817522652545787918470405 26215785497352335234713201)
              ·
                refine ⟨19661839123014251426034901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26215785497352335234713201 19661839123014251426034901)
                ·
                  refine ⟨460824354445646517797693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19661839123014251426034901 460824354445646517797693)
                  ·
                    rfl

theorem cell23_8077070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_8077070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077070 prefixEnd_8077070 := by exact prefixLift 8077070
  have htrace : WordTrace (prefixWord ++ tailWord_8077070) baseStart_8077070 baseEnd_8077070 := by
    simpa [prefixWord, tailWord_8077070, baseEnd_8077070] using wordTrace_append hprefix tailTrace_8077070
  have hstable : (prefixWord ++ tailWord_8077070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077070).length < 2 ^ (prefixWord ++ tailWord_8077070).sum := by decide
  have hdescent : baseEnd_8077070 < baseStart_8077070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077080 : List Nat := [2, 1, 2, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_8077080 : Nat := 118140960795 + 8077080 * 2 ^ 59
def prefixEnd_8077080 : Nat := 4983230072969 + 3 ^ 40 * 8077080 * 2
def baseEnd_8077080 : Nat := 4147424324817363621054191

theorem tailTrace_8077080 : CollatzResearch.WordTrace tailWord_8077080 prefixEnd_8077080 4147424324817363621054191 := by
  unfold tailWord_8077080
  simp only [CollatzResearch.WordTrace]
  refine ⟨147297654789063045142526347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196396873052084060190035129 147297654789063045142526347)
  ·
    refine ⟨220946482183594567713789521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147297654789063045142526347 220946482183594567713789521)
    ·
      refine ⟨165709861637695925785342141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220946482183594567713789521 165709861637695925785342141)
      ·
        refine ⟨62141198114135972169503303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165709861637695925785342141 62141198114135972169503303)
        ·
          refine ⟨93211797171203958254254955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62141198114135972169503303 93211797171203958254254955)
          ·
            refine ⟨139817695756805937381382433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93211797171203958254254955 139817695756805937381382433)
            ·
              refine ⟨104863271817604453036036825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139817695756805937381382433 104863271817604453036036825)
              ·
                refine ⟨78647453863203339777027619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104863271817604453036036825 78647453863203339777027619)
                ·
                  refine ⟨117971180794805009665541429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78647453863203339777027619 117971180794805009665541429)
                  ·
                    refine ⟨11059798199512969656144509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117971180794805009665541429 11059798199512969656144509)
                    ·
                      refine ⟨4147424324817363621054191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11059798199512969656144509 4147424324817363621054191)
                      ·
                        rfl

theorem cell23_8077080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_8077080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077080 prefixEnd_8077080 := by exact prefixLift 8077080
  have htrace : WordTrace (prefixWord ++ tailWord_8077080) baseStart_8077080 baseEnd_8077080 := by
    simpa [prefixWord, tailWord_8077080, baseEnd_8077080] using wordTrace_append hprefix tailTrace_8077080
  have hstable : (prefixWord ++ tailWord_8077080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077080).length < 2 ^ (prefixWord ++ tailWord_8077080).sum := by decide
  have hdescent : baseEnd_8077080 < baseStart_8077080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077100 : List Nat := [2, 2, 1, 1, 1, 5, 1, 1, 4, 5]
def baseStart_8077100 : Nat := 118140960795 + 8077100 * 2 ^ 59
def prefixEnd_8077100 : Nat := 4983230072969 + 3 ^ 40 * 8077100 * 2
def baseEnd_8077100 : Nat := 1382478198143484514268033

theorem tailTrace_8077100 : CollatzResearch.WordTrace tailWord_8077100 prefixEnd_8077100 1382478198143484514268033 := by
  unfold tailWord_8077100
  simp only [CollatzResearch.WordTrace]
  refine ⟨147298019519026816850390377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196397359358702422467187169 147298019519026816850390377)
  ·
    refine ⟨110473514639270112637792783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147298019519026816850390377 110473514639270112637792783)
    ·
      refine ⟨165710271958905168956689175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110473514639270112637792783 165710271958905168956689175)
      ·
        refine ⟨248565407938357753435033763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165710271958905168956689175 248565407938357753435033763)
        ·
          refine ⟨372848111907536630152550645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248565407938357753435033763 372848111907536630152550645)
          ·
            refine ⟨34954510491331559076801623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 372848111907536630152550645 34954510491331559076801623)
            ·
              refine ⟨52431765736997338615202435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34954510491331559076801623 52431765736997338615202435)
              ·
                refine ⟨78647648605496007922803653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52431765736997338615202435 78647648605496007922803653)
                ·
                  refine ⟨14746434113530501485525685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78647648605496007922803653 14746434113530501485525685)
                  ·
                    refine ⟨1382478198143484514268033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14746434113530501485525685 1382478198143484514268033)
                    ·
                      rfl

theorem cell23_8077100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 5].length) (baseStart_8077100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077100 prefixEnd_8077100 := by exact prefixLift 8077100
  have htrace : WordTrace (prefixWord ++ tailWord_8077100) baseStart_8077100 baseEnd_8077100 := by
    simpa [prefixWord, tailWord_8077100, baseEnd_8077100] using wordTrace_append hprefix tailTrace_8077100
  have hstable : (prefixWord ++ tailWord_8077100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077100).length < 2 ^ (prefixWord ++ tailWord_8077100).sum := by decide
  have hdescent : baseEnd_8077100 < baseStart_8077100 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077137 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 4]
def baseStart_8077137 : Nat := 118140960795 + 8077137 * 2 ^ 59
def prefixEnd_8077137 : Nat := 4983230072969 + 3 ^ 40 * 8077137 * 2
def baseEnd_8077137 : Nat := 4147453593214669898041429

theorem tailTrace_8077137 : CollatzResearch.WordTrace tailWord_8077137 prefixEnd_8077137 4147453593214669898041429 := by
  unfold tailWord_8077137
  simp only [CollatzResearch.WordTrace]
  refine ⟨294597388538919589019877665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196398259025946392679918443 294597388538919589019877665)
  ·
    refine ⟨220948041404189691764908249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294597388538919589019877665 220948041404189691764908249)
    ·
      refine ⟨165711031053142268823681187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220948041404189691764908249 165711031053142268823681187)
      ·
        refine ⟨248566546579713403235521781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165711031053142268823681187 248566546579713403235521781)
        ·
          refine ⟨23303113741848131553330167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248566546579713403235521781 23303113741848131553330167)
          ·
            refine ⟨34954670612772197329995251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23303113741848131553330167 34954670612772197329995251)
            ·
              refine ⟨52432005919158295994992877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34954670612772197329995251 52432005919158295994992877)
              ·
                refine ⟨19662002219684360998122329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52432005919158295994992877 19662002219684360998122329)
                ·
                  refine ⟨14746501664763270748591747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19662002219684360998122329 14746501664763270748591747)
                  ·
                    refine ⟨22119752497144906122887621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14746501664763270748591747 22119752497144906122887621)
                    ·
                      refine ⟨4147453593214669898041429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22119752497144906122887621 4147453593214669898041429)
                      ·
                        rfl

theorem cell23_8077137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 2, 1, 4].length) (baseStart_8077137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077137 prefixEnd_8077137 := by exact prefixLift 8077137
  have htrace : WordTrace (prefixWord ++ tailWord_8077137) baseStart_8077137 baseEnd_8077137 := by
    simpa [prefixWord, tailWord_8077137, baseEnd_8077137] using wordTrace_append hprefix tailTrace_8077137
  have hstable : (prefixWord ++ tailWord_8077137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077137).length < 2 ^ (prefixWord ++ tailWord_8077137).sum := by decide
  have hdescent : baseEnd_8077137 < baseStart_8077137 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077154 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 2, 1, 4]
def baseStart_8077154 : Nat := 118140960795 + 8077154 * 2 ^ 59
def prefixEnd_8077154 : Nat := 4983230072969 + 3 ^ 40 * 8077154 * 2
def baseEnd_8077154 : Nat := 4147462322385796331528851

theorem tailTrace_8077154 : CollatzResearch.WordTrace tailWord_8077154 prefixEnd_8077154 4147462322385796331528851 := by
  unfold tailWord_8077154
  simp only [CollatzResearch.WordTrace]
  refine ⟨73649502144964500230811629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196398672386572000615497677 73649502144964500230811629)
  ·
    refine ⟨27618563304361687586554361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73649502144964500230811629 27618563304361687586554361)
    ·
      refine ⟨20713922478271265689915771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27618563304361687586554361 20713922478271265689915771)
      ·
        refine ⟨31070883717406898534873657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20713922478271265689915771 31070883717406898534873657)
        ·
          refine ⟨23303162788055173901155243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31070883717406898534873657 23303162788055173901155243)
          ·
            refine ⟨34954744182082760851732865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23303162788055173901155243 34954744182082760851732865)
            ·
              refine ⟨26216058136562070638799649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34954744182082760851732865 26216058136562070638799649)
              ·
                refine ⟨19662043602421552979099737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26216058136562070638799649 19662043602421552979099737)
                ·
                  refine ⟨14746532701816164734324803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19662043602421552979099737 14746532701816164734324803)
                  ·
                    refine ⟨22119799052724247101487205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14746532701816164734324803 22119799052724247101487205)
                    ·
                      refine ⟨4147462322385796331528851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22119799052724247101487205 4147462322385796331528851)
                      ·
                        rfl

theorem cell23_8077154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_8077154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077154 prefixEnd_8077154 := by exact prefixLift 8077154
  have htrace : WordTrace (prefixWord ++ tailWord_8077154) baseStart_8077154 baseEnd_8077154 := by
    simpa [prefixWord, tailWord_8077154, baseEnd_8077154] using wordTrace_append hprefix tailTrace_8077154
  have hstable : (prefixWord ++ tailWord_8077154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077154).length < 2 ^ (prefixWord ++ tailWord_8077154).sum := by decide
  have hdescent : baseEnd_8077154 < baseStart_8077154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077191 : List Nat := [1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 3]
def baseStart_8077191 : Nat := 118140960795 + 8077191 * 2 ^ 59
def prefixEnd_8077191 : Nat := 4983230072969 + 3 ^ 40 * 8077191 * 2
def baseEnd_8077191 : Nat := 4147481321170012686766181

theorem tailTrace_8077191 : CollatzResearch.WordTrace tailWord_8077191 prefixEnd_8077191 4147481321170012686766181 := by
  unfold tailWord_8077191
  simp only [CollatzResearch.WordTrace]
  refine ⟨294599358080723956242343427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196399572053815970828228951 294599358080723956242343427)
  ·
    refine ⟨441899037121085934363515141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294599358080723956242343427 441899037121085934363515141)
    ·
      refine ⟨82856069460203612693159089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441899037121085934363515141 82856069460203612693159089)
      ·
        refine ⟨62142052095152709519869317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82856069460203612693159089 62142052095152709519869317)
        ·
          refine ⟨11651634767841133034975497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62142052095152709519869317 11651634767841133034975497)
          ·
            refine ⟨8738726075880849776231623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11651634767841133034975497 8738726075880849776231623)
            ·
              refine ⟨13108089113821274664347435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8738726075880849776231623 13108089113821274664347435)
              ·
                refine ⟨19662133670731911996521153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13108089113821274664347435 19662133670731911996521153)
                ·
                  refine ⟨14746600253048933997390865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19662133670731911996521153 14746600253048933997390865)
                  ·
                    refine ⟨11059950189786700498043149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14746600253048933997390865 11059950189786700498043149)
                    ·
                      refine ⟨4147481321170012686766181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11059950189786700498043149 4147481321170012686766181)
                      ·
                        rfl

theorem cell23_8077191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_8077191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077191 prefixEnd_8077191 := by exact prefixLift 8077191
  have htrace : WordTrace (prefixWord ++ tailWord_8077191) baseStart_8077191 baseEnd_8077191 := by
    simpa [prefixWord, tailWord_8077191, baseEnd_8077191] using wordTrace_append hprefix tailTrace_8077191
  have hstable : (prefixWord ++ tailWord_8077191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077191).length < 2 ^ (prefixWord ++ tailWord_8077191).sum := by decide
  have hdescent : baseEnd_8077191 < baseStart_8077191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077227 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 6, 2]
def baseStart_8077227 : Nat := 118140960795 + 8077227 * 2 ^ 59
def prefixEnd_8077227 : Nat := 4983230072969 + 3 ^ 40 * 8077227 * 2
def baseEnd_8077227 : Nat := 4147499806473574545916015

theorem tailTrace_8077227 : CollatzResearch.WordTrace tailWord_8077227 prefixEnd_8077227 4147499806473574545916015 := by
  unfold tailWord_8077227
  simp only [CollatzResearch.WordTrace]
  refine ⟨294600671108593534390653935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196400447405729022927102623 294600671108593534390653935)
  ·
    refine ⟨441901006662890301585980903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294600671108593534390653935 441901006662890301585980903)
    ·
      refine ⟨662851509994335452378971355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441901006662890301585980903 662851509994335452378971355)
      ·
        refine ⟨994277264991503178568457033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662851509994335452378971355 994277264991503178568457033)
        ·
          refine ⟨745707948743627383926342775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994277264991503178568457033 745707948743627383926342775)
          ·
            refine ⟨1118561923115441075889514163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745707948743627383926342775 1118561923115441075889514163)
            ·
              refine ⟨1677842884673161613834271245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118561923115441075889514163 1677842884673161613834271245)
              ·
                refine ⟨629191081752435605187851717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1677842884673161613834271245 629191081752435605187851717)
                ·
                  refine ⟨117973327828581675972722197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 629191081752435605187851717 117973327828581675972722197)
                  ·
                    refine ⟨5529999741964766061221353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117973327828581675972722197 5529999741964766061221353)
                    ·
                      refine ⟨4147499806473574545916015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5529999741964766061221353 4147499806473574545916015)
                      ·
                        rfl

theorem cell23_8077227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 6, 2].length) (baseStart_8077227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077227 prefixEnd_8077227 := by exact prefixLift 8077227
  have htrace : WordTrace (prefixWord ++ tailWord_8077227) baseStart_8077227 baseEnd_8077227 := by
    simpa [prefixWord, tailWord_8077227, baseEnd_8077227] using wordTrace_append hprefix tailTrace_8077227
  have hstable : (prefixWord ++ tailWord_8077227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077227).length < 2 ^ (prefixWord ++ tailWord_8077227).sum := by decide
  have hdescent : baseEnd_8077227 < baseStart_8077227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077264 : List Nat := [2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3]
def baseStart_8077264 : Nat := 118140960795 + 8077264 * 2 ^ 59
def prefixEnd_8077264 : Nat := 4983230072969 + 3 ^ 40 * 8077264 * 2
def baseEnd_8077264 : Nat := 4147518805257790901153345

theorem tailTrace_8077264 : CollatzResearch.WordTrace tailWord_8077264 prefixEnd_8077264 4147518805257790901153345 := by
  unfold tailWord_8077264
  simp only [CollatzResearch.WordTrace]
  refine ⟨147301010304729744854875423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196401347072972993139833897 147301010304729744854875423)
  ·
    refine ⟨220951515457094617282313135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147301010304729744854875423 220951515457094617282313135)
    ·
      refine ⟨331427273185641925923469703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220951515457094617282313135 331427273185641925923469703)
      ·
        refine ⟨497140909778462888885204555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331427273185641925923469703 497140909778462888885204555)
        ·
          refine ⟨745711364667694333327806833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497140909778462888885204555 745711364667694333327806833)
          ·
            refine ⟨559283523500770749995855125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 745711364667694333327806833 559283523500770749995855125)
            ·
              refine ⟨26216415164098628906055709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 559283523500770749995855125 26216415164098628906055709)
              ·
                refine ⟨9831155686536985839770891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26216415164098628906055709 9831155686536985839770891)
                ·
                  refine ⟨14746733529805478759656337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9831155686536985839770891 14746733529805478759656337)
                  ·
                    refine ⟨11060050147354109069742253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14746733529805478759656337 11060050147354109069742253)
                    ·
                      refine ⟨4147518805257790901153345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11060050147354109069742253 4147518805257790901153345)
                      ·
                        rfl

theorem cell23_8077264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_8077264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077264 prefixEnd_8077264 := by exact prefixLift 8077264
  have htrace : WordTrace (prefixWord ++ tailWord_8077264) baseStart_8077264 baseEnd_8077264 := by
    simpa [prefixWord, tailWord_8077264, baseEnd_8077264] using wordTrace_append hprefix tailTrace_8077264
  have hstable : (prefixWord ++ tailWord_8077264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077264).length < 2 ^ (prefixWord ++ tailWord_8077264).sum := by decide
  have hdescent : baseEnd_8077264 < baseStart_8077264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077318 : List Nat := [6, 2, 1, 2, 1, 11]
def baseStart_8077318 : Nat := 118140960795 + 8077318 * 2 ^ 59
def prefixEnd_8077318 : Nat := 4983230072969 + 3 ^ 40 * 8077318 * 2
def baseEnd_8077318 : Nat := 17068092729272155102379

theorem tailTrace_8077318 : CollatzResearch.WordTrace tailWord_8077318 prefixEnd_8077318 17068092729272155102379 := by
  unfold tailWord_8077318
  simp only [CollatzResearch.WordTrace]
  refine ⟨9206374692226995529131769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196402660100842571288144405 9206374692226995529131769)
  ·
    refine ⟨6904781019170246646848827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9206374692226995529131769 6904781019170246646848827)
    ·
      refine ⟨10357171528755369970273241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6904781019170246646848827 10357171528755369970273241)
      ·
        refine ⟨7767878646566527477704931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10357171528755369970273241 7767878646566527477704931)
        ·
          refine ⟨11651817969849791216557397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767878646566527477704931 11651817969849791216557397)
          ·
            refine ⟨17068092729272155102379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11651817969849791216557397 17068092729272155102379)
            ·
              rfl

theorem cell23_8077318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 11].length) (baseStart_8077318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077318 prefixEnd_8077318 := by exact prefixLift 8077318
  have htrace : WordTrace (prefixWord ++ tailWord_8077318) baseStart_8077318 baseEnd_8077318 := by
    simpa [prefixWord, tailWord_8077318, baseEnd_8077318] using wordTrace_append hprefix tailTrace_8077318
  have hstable : (prefixWord ++ tailWord_8077318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077318).length < 2 ^ (prefixWord ++ tailWord_8077318).sum := by decide
  have hdescent : baseEnd_8077318 < baseStart_8077318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077398 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_8077398 : Nat := 118140960795 + 8077398 * 2 ^ 59
def prefixEnd_8077398 : Nat := 4983230072969 + 3 ^ 40 * 8077398 * 2
def baseEnd_8077398 : Nat := 4147587611665493376877729

theorem tailTrace_8077398 : CollatzResearch.WordTrace tailWord_8077398 prefixEnd_8077398 4147587611665493376877729 := by
  unfold tailWord_8077398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18412931749435876912195553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196404605327316020396752565 18412931749435876912195553)
  ·
    refine ⟨13809698812076907684146665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18412931749435876912195553 13809698812076907684146665)
    ·
      refine ⟨10357274109057680763109999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13809698812076907684146665 10357274109057680763109999)
      ·
        refine ⟨15535911163586521144664999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10357274109057680763109999 15535911163586521144664999)
        ·
          refine ⟨23303866745379781716997499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15535911163586521144664999 23303866745379781716997499)
          ·
            refine ⟨34955800118069672575496249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23303866745379781716997499 34955800118069672575496249)
            ·
              refine ⟨26216850088552254431622187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34955800118069672575496249 26216850088552254431622187)
              ·
                refine ⟨39325275132828381647433281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26216850088552254431622187 39325275132828381647433281)
                ·
                  refine ⟨29493956349621286235574961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39325275132828381647433281 29493956349621286235574961)
                  ·
                    refine ⟨22120467262215964676681221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29493956349621286235574961 22120467262215964676681221)
                    ·
                      refine ⟨4147587611665493376877729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22120467262215964676681221 4147587611665493376877729)
                      ·
                        rfl

theorem cell23_8077398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_8077398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077398 prefixEnd_8077398 := by exact prefixLift 8077398
  have htrace : WordTrace (prefixWord ++ tailWord_8077398) baseStart_8077398 baseEnd_8077398 := by
    simpa [prefixWord, tailWord_8077398, baseEnd_8077398] using wordTrace_append hprefix tailTrace_8077398
  have hstable : (prefixWord ++ tailWord_8077398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077398).length < 2 ^ (prefixWord ++ tailWord_8077398).sum := by decide
  have hdescent : baseEnd_8077398 < baseStart_8077398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077404 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 1, 7]
def baseStart_8077404 : Nat := 118140960795 + 8077404 * 2 ^ 59
def prefixEnd_8077404 : Nat := 4983230072969 + 3 ^ 40 * 8077404 * 2
def baseEnd_8077404 : Nat := 1382530230849806784467567

theorem tailTrace_8077404 : CollatzResearch.WordTrace tailWord_8077404 prefixEnd_8077404 1382530230849806784467567 := by
  unfold tailWord_8077404
  simp only [CollatzResearch.WordTrace]
  refine ⟨147303563414476146809923633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196404751219301529079898177 147303563414476146809923633)
  ·
    refine ⟨110477672560857110107442725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147303563414476146809923633 110477672560857110107442725)
    ·
      refine ⟨20714563605160708145145511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110477672560857110107442725 20714563605160708145145511)
      ·
        refine ⟨31071845407741062217718267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20714563605160708145145511 31071845407741062217718267)
        ·
          refine ⟨46607768111611593326577401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31071845407741062217718267 46607768111611593326577401)
          ·
            refine ⟨34955826083708694994933051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46607768111611593326577401 34955826083708694994933051)
            ·
              refine ⟨52433739125563042492399577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34955826083708694994933051 52433739125563042492399577)
              ·
                refine ⟨39325304344172281869299683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52433739125563042492399577 39325304344172281869299683)
                ·
                  refine ⟨58987956516258422803949525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39325304344172281869299683 58987956516258422803949525)
                  ·
                    refine ⟨1382530230849806784467567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58987956516258422803949525 1382530230849806784467567)
                    ·
                      rfl

theorem cell23_8077404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_8077404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077404 prefixEnd_8077404 := by exact prefixLift 8077404
  have htrace : WordTrace (prefixWord ++ tailWord_8077404) baseStart_8077404 baseEnd_8077404 := by
    simpa [prefixWord, tailWord_8077404, baseEnd_8077404] using wordTrace_append hprefix tailTrace_8077404
  have hstable : (prefixWord ++ tailWord_8077404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077404).length < 2 ^ (prefixWord ++ tailWord_8077404).sum := by decide
  have hdescent : baseEnd_8077404 < baseStart_8077404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077417 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 2, 8]
def baseStart_8077417 : Nat := 118140960795 + 8077417 * 2 ^ 59
def prefixEnd_8077417 : Nat := 4983230072969 + 3 ^ 40 * 8077417 * 2
def baseEnd_8077417 : Nat := 1382532455932642934180047

theorem tailTrace_8077417 : CollatzResearch.WordTrace tailWord_8077417 prefixEnd_8077417 1382532455932642934180047 := by
  unfold tailWord_8077417
  simp only [CollatzResearch.WordTrace]
  refine ⟨294607600977905196840070505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196405067318603464560047003 294607600977905196840070505)
  ·
    refine ⟨220955700733428897630052879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294607600977905196840070505 220955700733428897630052879)
    ·
      refine ⟨331433551100143346445079319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220955700733428897630052879 331433551100143346445079319)
      ·
        refine ⟨497150326650215019667618979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331433551100143346445079319 497150326650215019667618979)
        ·
          refine ⟨745725489975322529501428469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497150326650215019667618979 745725489975322529501428469)
          ·
            refine ⟨69911764685186487140758919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 745725489975322529501428469 69911764685186487140758919)
            ·
              refine ⟨104867647027779730711138379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69911764685186487140758919 104867647027779730711138379)
              ·
                refine ⟨157301470541669596066707569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104867647027779730711138379 157301470541669596066707569)
                ·
                  refine ⟨117976102906252197050030677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157301470541669596066707569 117976102906252197050030677)
                  ·
                    refine ⟨1382532455932642934180047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117976102906252197050030677 1382532455932642934180047)
                    ·
                      rfl

theorem cell23_8077417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 8].length) (baseStart_8077417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077417 prefixEnd_8077417 := by exact prefixLift 8077417
  have htrace : WordTrace (prefixWord ++ tailWord_8077417) baseStart_8077417 baseEnd_8077417 := by
    simpa [prefixWord, tailWord_8077417, baseEnd_8077417] using wordTrace_append hprefix tailTrace_8077417
  have hstable : (prefixWord ++ tailWord_8077417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077417).length < 2 ^ (prefixWord ++ tailWord_8077417).sum := by decide
  have hdescent : baseEnd_8077417 < baseStart_8077417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077424 : List Nat := [2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_8077424 : Nat := 118140960795 + 8077424 * 2 ^ 59
def prefixEnd_8077424 : Nat := 4983230072969 + 3 ^ 40 * 8077424 * 2
def baseEnd_8077424 : Nat := 4147600962162510275152609

theorem tailTrace_8077424 : CollatzResearch.WordTrace tailWord_8077424 prefixEnd_8077424 4147600962162510275152609 := by
  unfold tailWord_8077424
  simp only [CollatzResearch.WordTrace]
  refine ⟨147303928144439918517787663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196405237525919891357050217 147303928144439918517787663)
  ·
    refine ⟨220955892216659877776681495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147303928144439918517787663 220955892216659877776681495)
    ·
      refine ⟨331433838324989816665022243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220955892216659877776681495 331433838324989816665022243)
      ·
        refine ⟨497150757487484724997533365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331433838324989816665022243 497150757487484724997533365)
        ·
          refine ⟨46607883514451692968518753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497150757487484724997533365 46607883514451692968518753)
          ·
            refine ⟨34955912635838769726389065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46607883514451692968518753 34955912635838769726389065)
            ·
              refine ⟨26216934476879077294791799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34955912635838769726389065 26216934476879077294791799)
              ·
                refine ⟨39325401715318615942187699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26216934476879077294791799 39325401715318615942187699)
                ·
                  refine ⟨58988102572977923913281549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39325401715318615942187699 58988102572977923913281549)
                  ·
                    refine ⟨22120538464866721467480581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58988102572977923913281549 22120538464866721467480581)
                    ·
                      refine ⟨4147600962162510275152609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22120538464866721467480581 4147600962162510275152609)
                      ·
                        rfl

theorem cell23_8077424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_8077424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077424 prefixEnd_8077424 := by exact prefixLift 8077424
  have htrace : WordTrace (prefixWord ++ tailWord_8077424) baseStart_8077424 baseEnd_8077424 := by
    simpa [prefixWord, tailWord_8077424, baseEnd_8077424] using wordTrace_append hprefix tailTrace_8077424
  have hstable : (prefixWord ++ tailWord_8077424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077424).length < 2 ^ (prefixWord ++ tailWord_8077424).sum := by decide
  have hdescent : baseEnd_8077424 < baseStart_8077424 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077501 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 3, 5, 2]
def baseStart_8077501 : Nat := 118140960795 + 8077501 * 2 ^ 59
def prefixEnd_8077501 : Nat := 4983230072969 + 3 ^ 40 * 8077501 * 2
def baseEnd_8077501 : Nat := 4147640500172906473889755

theorem tailTrace_8077501 : CollatzResearch.WordTrace tailWord_8077501 prefixEnd_8077501 4147640500172906473889755 := by
  unfold tailWord_8077501
  simp only [CollatzResearch.WordTrace]
  refine ⟨294610664709600879186128357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196407109806400586124085571 294610664709600879186128357)
  ·
    refine ⟨55239499633050164847399067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294610664709600879186128357 55239499633050164847399067)
    ·
      refine ⟨82859249449575247271098601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55239499633050164847399067 82859249449575247271098601)
      ·
        refine ⟨62144437087181435453323951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82859249449575247271098601 62144437087181435453323951)
        ·
          refine ⟨93216655630772153179985927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62144437087181435453323951 93216655630772153179985927)
          ·
            refine ⟨139824983446158229769978891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93216655630772153179985927 139824983446158229769978891)
            ·
              refine ⟨209737475169237344654968337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139824983446158229769978891 209737475169237344654968337)
              ·
                refine ⟨157303106376928008491226253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209737475169237344654968337 157303106376928008491226253)
                ·
                  refine ⟨58988664891348003184209845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157303106376928008491226253 58988664891348003184209845)
                  ·
                    refine ⟨5530187333563875298519673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58988664891348003184209845 5530187333563875298519673)
                    ·
                      refine ⟨4147640500172906473889755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530187333563875298519673 4147640500172906473889755)
                      ·
                        rfl

theorem cell23_8077501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_8077501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077501 prefixEnd_8077501 := by exact prefixLift 8077501
  have htrace : WordTrace (prefixWord ++ tailWord_8077501) baseStart_8077501 baseEnd_8077501 := by
    simpa [prefixWord, tailWord_8077501, baseEnd_8077501] using wordTrace_append hprefix tailTrace_8077501
  have hstable : (prefixWord ++ tailWord_8077501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077501).length < 2 ^ (prefixWord ++ tailWord_8077501).sum := by decide
  have hdescent : baseEnd_8077501 < baseStart_8077501 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077525 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 3]
def baseStart_8077525 : Nat := 118140960795 + 8077525 * 2 ^ 59
def prefixEnd_8077525 : Nat := 4983230072969 + 3 ^ 40 * 8077525 * 2
def baseEnd_8077525 : Nat := 4147652823708614379989645

theorem tailTrace_8077525 : CollatzResearch.WordTrace tailWord_8077525 prefixEnd_8077525 4147652823708614379989645 := by
  unfold tailWord_8077525
  simp only [CollatzResearch.WordTrace]
  refine ⟨294611540061513931285002029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196407693374342620856668019 294611540061513931285002029)
  ·
    refine ⟨110479327523067724231875761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294611540061513931285002029 110479327523067724231875761)
    ·
      refine ⟨82859495642300793173906821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110479327523067724231875761 82859495642300793173906821)
      ·
        refine ⟨15536155432931398720107529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82859495642300793173906821 15536155432931398720107529)
        ·
          refine ⟨11652116574698549040080647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15536155432931398720107529 11652116574698549040080647)
          ·
            refine ⟨17478174862047823560120971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652116574698549040080647 17478174862047823560120971)
            ·
              refine ⟨26217262293071735340181457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17478174862047823560120971 26217262293071735340181457)
              ·
                refine ⟨19662946719803801505136093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26217262293071735340181457 19662946719803801505136093)
                ·
                  refine ⟨7373605019926425564426035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19662946719803801505136093 7373605019926425564426035)
                  ·
                    refine ⟨11060407529889638346639053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7373605019926425564426035 11060407529889638346639053)
                    ·
                      refine ⟨4147652823708614379989645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11060407529889638346639053 4147652823708614379989645)
                      ·
                        rfl

theorem cell23_8077525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_8077525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077525 prefixEnd_8077525 := by exact prefixLift 8077525
  have htrace : WordTrace (prefixWord ++ tailWord_8077525) baseStart_8077525 baseEnd_8077525 := by
    simpa [prefixWord, tailWord_8077525, baseEnd_8077525] using wordTrace_append hprefix tailTrace_8077525
  have hstable : (prefixWord ++ tailWord_8077525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077525).length < 2 ^ (prefixWord ++ tailWord_8077525).sum := by decide
  have hdescent : baseEnd_8077525 < baseStart_8077525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077541 : List Nat := [1, 3, 1, 4, 2, 1, 2, 2, 1, 6]
def baseStart_8077541 : Nat := 118140960795 + 8077541 * 2 ^ 59
def prefixEnd_8077541 : Nat := 4983230072969 + 3 ^ 40 * 8077541 * 2
def baseEnd_8077541 : Nat := 1382553679799695439129857

theorem tailTrace_8077541 : CollatzResearch.WordTrace tailWord_8077541 prefixEnd_8077541 1382553679799695439129857 := by
  unfold tailWord_8077541
  simp only [CollatzResearch.WordTrace]
  refine ⟨294612123629455966017584477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196408082419637310678389651 294612123629455966017584477)
  ·
    refine ⟨110479546361045987256594179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294612123629455966017584477 110479546361045987256594179)
    ·
      refine ⟨165719319541568980884891269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110479546361045987256594179 165719319541568980884891269)
      ·
        refine ⟨31072372414044183915917113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165719319541568980884891269 31072372414044183915917113)
        ·
          refine ⟨23304279310533137936937835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31072372414044183915917113 23304279310533137936937835)
          ·
            refine ⟨34956418965799706905406753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23304279310533137936937835 34956418965799706905406753)
            ·
              refine ⟨26217314224349780179055065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34956418965799706905406753 26217314224349780179055065)
              ·
                refine ⟨19662985668262335134291299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26217314224349780179055065 19662985668262335134291299)
                ·
                  refine ⟨29494478502393502701436949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19662985668262335134291299 29494478502393502701436949)
                  ·
                    refine ⟨1382553679799695439129857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29494478502393502701436949 1382553679799695439129857)
                    ·
                      rfl

theorem cell23_8077541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_8077541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077541 prefixEnd_8077541 := by exact prefixLift 8077541
  have htrace : WordTrace (prefixWord ++ tailWord_8077541) baseStart_8077541 baseEnd_8077541 := by
    simpa [prefixWord, tailWord_8077541, baseEnd_8077541] using wordTrace_append hprefix tailTrace_8077541
  have hstable : (prefixWord ++ tailWord_8077541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077541).length < 2 ^ (prefixWord ++ tailWord_8077541).sum := by decide
  have hdescent : baseEnd_8077541 < baseStart_8077541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077548 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 5, 2, 2]
def baseStart_8077548 : Nat := 118140960795 + 8077548 * 2 ^ 59
def prefixEnd_8077548 : Nat := 4983230072969 + 3 ^ 40 * 8077548 * 2
def baseEnd_8077548 : Nat := 4147664633763667790002039

theorem tailTrace_8077548 : CollatzResearch.WordTrace tailWord_8077548 prefixEnd_8077548 4147664633763667790002039 := by
  unfold tailWord_8077548
  simp only [CollatzResearch.WordTrace]
  refine ⟨147306189470215303106544649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196408252626953737475392865 147306189470215303106544649)
  ·
    refine ⟨110479642102661477329908487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147306189470215303106544649 110479642102661477329908487)
    ·
      refine ⟨165719463153992215994862731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110479642102661477329908487 165719463153992215994862731)
      ·
        refine ⟨248579194730988323992294097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165719463153992215994862731 248579194730988323992294097)
        ·
          refine ⟨186434396048241242994220573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248579194730988323992294097 186434396048241242994220573)
          ·
            refine ⟨69912898518090466122832715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186434396048241242994220573 69912898518090466122832715)
            ·
              refine ⟨104869347777135699184249073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69912898518090466122832715 104869347777135699184249073)
              ·
                refine ⟨78652010832851774388186805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104869347777135699184249073 78652010832851774388186805)
                ·
                  refine ⟨7373626015579853848892513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78652010832851774388186805 7373626015579853848892513)
                  ·
                    refine ⟨5530219511684890386669385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7373626015579853848892513 5530219511684890386669385)
                    ·
                      refine ⟨4147664633763667790002039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530219511684890386669385 4147664633763667790002039)
                      ·
                        rfl

theorem cell23_8077548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 2, 2].length) (baseStart_8077548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077548 prefixEnd_8077548 := by exact prefixLift 8077548
  have htrace : WordTrace (prefixWord ++ tailWord_8077548) baseStart_8077548 baseEnd_8077548 := by
    simpa [prefixWord, tailWord_8077548, baseEnd_8077548] using wordTrace_append hprefix tailTrace_8077548
  have hstable : (prefixWord ++ tailWord_8077548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077548).length < 2 ^ (prefixWord ++ tailWord_8077548).sum := by decide
  have hdescent : baseEnd_8077548 < baseStart_8077548 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077575 : List Nat := [1, 1, 4, 5, 1, 2, 1, 1, 1, 6]
def baseStart_8077575 : Nat := 118140960795 + 8077575 * 2 ^ 59
def prefixEnd_8077575 : Nat := 4983230072969 + 3 ^ 40 * 8077575 * 2
def baseEnd_8077575 : Nat := 1382559499247113061454805

theorem tailTrace_8077575 : CollatzResearch.WordTrace tailWord_8077575 prefixEnd_8077575 1382559499247113061454805 := by
  unfold tailWord_8077575
  simp only [CollatzResearch.WordTrace]
  refine ⟨294613363711332789824322179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196408909140888526549548119 294613363711332789824322179)
  ·
    refine ⟨441920045566999184736483269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294613363711332789824322179 441920045566999184736483269)
    ·
      refine ⟨82860008543812347138090613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441920045566999184736483269 82860008543812347138090613)
      ·
        refine ⟨7768125800982407544195995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 82860008543812347138090613 7768125800982407544195995)
        ·
          refine ⟨11652188701473611316293993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768125800982407544195995 11652188701473611316293993)
          ·
            refine ⟨8739141526105208487220495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11652188701473611316293993 8739141526105208487220495)
            ·
              refine ⟨13108712289157812730830743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739141526105208487220495 13108712289157812730830743)
              ·
                refine ⟨19663068433736719096246115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13108712289157812730830743 19663068433736719096246115)
                ·
                  refine ⟨29494602650605078644369173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19663068433736719096246115 29494602650605078644369173)
                  ·
                    refine ⟨1382559499247113061454805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29494602650605078644369173 1382559499247113061454805)
                    ·
                      rfl

theorem cell23_8077575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_8077575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077575 prefixEnd_8077575 := by exact prefixLift 8077575
  have htrace : WordTrace (prefixWord ++ tailWord_8077575) baseStart_8077575 baseEnd_8077575 := by
    simpa [prefixWord, tailWord_8077575, baseEnd_8077575] using wordTrace_append hprefix tailTrace_8077575
  have hstable : (prefixWord ++ tailWord_8077575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077575).length < 2 ^ (prefixWord ++ tailWord_8077575).sum := by decide
  have hdescent : baseEnd_8077575 < baseStart_8077575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077599 : List Nat := [1, 1, 2, 4, 3, 3, 1, 3, 1, 2, 2]
def baseStart_8077599 : Nat := 118140960795 + 8077599 * 2 ^ 59
def prefixEnd_8077599 : Nat := 4983230072969 + 3 ^ 40 * 8077599 * 2
def baseEnd_8077599 : Nat := 4147690821277047090464305

theorem tailTrace_8077599 : CollatzResearch.WordTrace tailWord_8077599 prefixEnd_8077599 4147690821277047090464305 := by
  unfold tailWord_8077599
  simp only [CollatzResearch.WordTrace]
  refine ⟨294614239063245841923195851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196409492708830561282130567 294614239063245841923195851)
  ·
    refine ⟨441921358594868762884793777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294614239063245841923195851 441921358594868762884793777)
    ·
      refine ⟨331441018946151572163595333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441921358594868762884793777 331441018946151572163595333)
      ·
        refine ⟨62145191052403419780674125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 331441018946151572163595333 62145191052403419780674125)
        ·
          refine ⟨23304446644651282417752797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62145191052403419780674125 23304446644651282417752797)
          ·
            refine ⟨8739167491744230906657299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23304446644651282417752797 8739167491744230906657299)
            ·
              refine ⟨13108751237616346359985949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739167491744230906657299 13108751237616346359985949)
              ·
                refine ⟨4915781714106129884994731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13108751237616346359985949 4915781714106129884994731)
                ·
                  refine ⟨7373672571159194827492097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915781714106129884994731 7373672571159194827492097)
                  ·
                    refine ⟨5530254428369396120619073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7373672571159194827492097 5530254428369396120619073)
                    ·
                      refine ⟨4147690821277047090464305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530254428369396120619073 4147690821277047090464305)
                      ·
                        rfl

theorem cell23_8077599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_8077599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077599 prefixEnd_8077599 := by exact prefixLift 8077599
  have htrace : WordTrace (prefixWord ++ tailWord_8077599) baseStart_8077599 baseEnd_8077599 := by
    simpa [prefixWord, tailWord_8077599, baseEnd_8077599] using wordTrace_append hprefix tailTrace_8077599
  have hstable : (prefixWord ++ tailWord_8077599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077599).length < 2 ^ (prefixWord ++ tailWord_8077599).sum := by decide
  have hdescent : baseEnd_8077599 < baseStart_8077599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077621 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 4]
def baseStart_8077621 : Nat := 118140960795 + 8077621 * 2 ^ 59
def prefixEnd_8077621 : Nat := 4983230072969 + 3 ^ 40 * 8077621 * 2
def baseEnd_8077621 : Nat := 4147702117851446004389203

theorem tailTrace_8077621 : CollatzResearch.WordTrace tailWord_8077621 prefixEnd_8077621 4147702117851446004389203 := by
  unfold tailWord_8077621
  simp only [CollatzResearch.WordTrace]
  refine ⟨294615041469166139680496717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196410027646110759786997811 294615041469166139680496717)
  ·
    refine ⟨110480640550937302380186269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294615041469166139680496717 110480640550937302380186269)
    ·
      refine ⟨41430240206601488392569851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110480640550937302380186269 41430240206601488392569851)
      ·
        refine ⟨62145360309902232588854777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41430240206601488392569851 62145360309902232588854777)
        ·
          refine ⟨46609020232426674441641083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62145360309902232588854777 46609020232426674441641083)
          ·
            refine ⟨69913530348640011662461625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46609020232426674441641083 69913530348640011662461625)
            ·
              refine ⟨52435147761480008746846219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69913530348640011662461625 52435147761480008746846219)
              ·
                refine ⟨78652721642220013120269329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52435147761480008746846219 78652721642220013120269329)
                ·
                  refine ⟨58989541231665009840201997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78652721642220013120269329 58989541231665009840201997)
                  ·
                    refine ⟨22121077961874378690075749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58989541231665009840201997 22121077961874378690075749)
                    ·
                      refine ⟨4147702117851446004389203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22121077961874378690075749 4147702117851446004389203)
                      ·
                        rfl

theorem cell23_8077621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_8077621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077621 prefixEnd_8077621 := by exact prefixLift 8077621
  have htrace : WordTrace (prefixWord ++ tailWord_8077621) baseStart_8077621 baseEnd_8077621 := by
    simpa [prefixWord, tailWord_8077621, baseEnd_8077621] using wordTrace_append hprefix tailTrace_8077621
  have hstable : (prefixWord ++ tailWord_8077621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077621).length < 2 ^ (prefixWord ++ tailWord_8077621).sum := by decide
  have hdescent : baseEnd_8077621 < baseStart_8077621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077672 : List Nat := [2, 1, 4, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_8077672 : Nat := 118140960795 + 8077672 * 2 ^ 59
def prefixEnd_8077672 : Nat := 4983230072969 + 3 ^ 40 * 8077672 * 2
def baseEnd_8077672 : Nat := 4147728305364825304851469

theorem tailTrace_8077672 : CollatzResearch.WordTrace tailWord_8077672 prefixEnd_8077672 4147728305364825304851469 := by
  unfold tailWord_8077672
  simp only [CollatzResearch.WordTrace]
  refine ⟨147308450795990687695301635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196411267727987583593735513 147308450795990687695301635)
  ·
    refine ⟨220962676193986031542952453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147308450795990687695301635 220962676193986031542952453)
    ·
      refine ⟨41430501786372380914303585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220962676193986031542952453 41430501786372380914303585)
      ·
        refine ⟨31072876339779285685727689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41430501786372380914303585 31072876339779285685727689)
        ·
          refine ⟨23304657254834464264295767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31072876339779285685727689 23304657254834464264295767)
          ·
            refine ⟨34956985882251696396443651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23304657254834464264295767 34956985882251696396443651)
            ·
              refine ⟨52435478823377544594665477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34956985882251696396443651 52435478823377544594665477)
              ·
                refine ⟨9831652279383289611499777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52435478823377544594665477 9831652279383289611499777)
                ·
                  refine ⟨7373739209537467208624833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9831652279383289611499777 7373739209537467208624833)
                  ·
                    refine ⟨5530304407153100406468625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7373739209537467208624833 5530304407153100406468625)
                    ·
                      refine ⟨4147728305364825304851469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530304407153100406468625 4147728305364825304851469)
                      ·
                        rfl

theorem cell23_8077672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_8077672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077672 prefixEnd_8077672 := by exact prefixLift 8077672
  have htrace : WordTrace (prefixWord ++ tailWord_8077672) baseStart_8077672 baseEnd_8077672 := by
    simpa [prefixWord, tailWord_8077672, baseEnd_8077672] using wordTrace_append hprefix tailTrace_8077672
  have hstable : (prefixWord ++ tailWord_8077672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077672).length < 2 ^ (prefixWord ++ tailWord_8077672).sum := by decide
  have hdescent : baseEnd_8077672 < baseStart_8077672 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077708 : List Nat := [2, 2, 1, 2, 1, 4, 3, 1, 2, 5]
def baseStart_8077708 : Nat := 118140960795 + 8077708 * 2 ^ 59
def prefixEnd_8077708 : Nat := 4983230072969 + 3 ^ 40 * 8077708 * 2
def baseEnd_8077708 : Nat := 1382582263556129054667101

theorem tailTrace_8077708 : CollatzResearch.WordTrace tailWord_8077708 prefixEnd_8077708 1382582263556129054667101 := by
  unfold tailWord_8077708
  simp only [CollatzResearch.WordTrace]
  refine ⟨147309107309925476769456889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196412143079900635692609185 147309107309925476769456889)
  ·
    refine ⟨110481830482444107577092667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147309107309925476769456889 110481830482444107577092667)
    ·
      refine ⟨165722745723666161365639001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110481830482444107577092667 165722745723666161365639001)
      ·
        refine ⟨124292059292749621024229251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165722745723666161365639001 124292059292749621024229251)
        ·
          refine ⟨186438088939124431536343877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124292059292749621024229251 186438088939124431536343877)
          ·
            refine ⟨34957141676085830913064477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186438088939124431536343877 34957141676085830913064477)
            ·
              refine ⟨13108928128532186592399179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34957141676085830913064477 13108928128532186592399179)
              ·
                refine ⟨19663392192798279888598769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13108928128532186592399179 19663392192798279888598769)
                ·
                  refine ⟨14747544144598709916449077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19663392192798279888598769 14747544144598709916449077)
                  ·
                    refine ⟨1382582263556129054667101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14747544144598709916449077 1382582263556129054667101)
                    ·
                      rfl

theorem cell23_8077708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 1, 2, 5].length) (baseStart_8077708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077708 prefixEnd_8077708 := by exact prefixLift 8077708
  have htrace : WordTrace (prefixWord ++ tailWord_8077708) baseStart_8077708 baseEnd_8077708 := by
    simpa [prefixWord, tailWord_8077708, baseEnd_8077708] using wordTrace_append hprefix tailTrace_8077708
  have hstable : (prefixWord ++ tailWord_8077708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077708).length < 2 ^ (prefixWord ++ tailWord_8077708).sum := by decide
  have hdescent : baseEnd_8077708 < baseStart_8077708 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077745 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 2, 4, 2]
def baseStart_8077745 : Nat := 118140960795 + 8077745 * 2 ^ 59
def prefixEnd_8077745 : Nat := 4983230072969 + 3 ^ 40 * 8077745 * 2
def baseEnd_8077745 : Nat := 4147765789452603519238633

theorem tailTrace_8077745 : CollatzResearch.WordTrace tailWord_8077745 prefixEnd_8077745 4147765789452603519238633 := by
  unfold tailWord_8077745
  simp only [CollatzResearch.WordTrace]
  refine ⟨294619564120716908858010689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196413042747144605905340459 294619564120716908858010689)
  ·
    refine ⟨220964673090537681643508017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294619564120716908858010689 220964673090537681643508017)
    ·
      refine ⟨165723504817903261232631013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220964673090537681643508017 165723504817903261232631013)
      ·
        refine ⟨31073157153356861481118315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165723504817903261232631013 31073157153356861481118315)
        ·
          refine ⟨46609735730035292221677473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31073157153356861481118315 46609735730035292221677473)
          ·
            refine ⟨34957301797526469166258105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46609735730035292221677473 34957301797526469166258105)
            ·
              refine ⟨26217976348144851874693579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34957301797526469166258105 26217976348144851874693579)
              ·
                refine ⟨39326964522217277812040369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26217976348144851874693579 39326964522217277812040369)
                ·
                  refine ⟨29495223391662958359030277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39326964522217277812040369 29495223391662958359030277)
                  ·
                    refine ⟨5530354385936804692318177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29495223391662958359030277 5530354385936804692318177)
                    ·
                      refine ⟨4147765789452603519238633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530354385936804692318177 4147765789452603519238633)
                      ·
                        rfl

theorem cell23_8077745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_8077745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077745 prefixEnd_8077745 := by exact prefixLift 8077745
  have htrace : WordTrace (prefixWord ++ tailWord_8077745) baseStart_8077745 baseEnd_8077745 := by
    simpa [prefixWord, tailWord_8077745, baseEnd_8077745] using wordTrace_append hprefix tailTrace_8077745
  have hstable : (prefixWord ++ tailWord_8077745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077745).length < 2 ^ (prefixWord ++ tailWord_8077745).sum := by decide
  have hdescent : baseEnd_8077745 < baseStart_8077745 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077782 : List Nat := [5, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_8077782 : Nat := 118140960795 + 8077782 * 2 ^ 59
def prefixEnd_8077782 : Nat := 4983230072969 + 3 ^ 40 * 8077782 * 2
def baseEnd_8077782 : Nat := 4147784788236819874475963

theorem tailTrace_8077782 : CollatzResearch.WordTrace tailWord_8077782 prefixEnd_8077782 4147784788236819874475963 := by
  unfold tailWord_8077782
  simp only [CollatzResearch.WordTrace]
  refine ⟨18413807101348929011069225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196413942414388576118071733 18413807101348929011069225)
  ·
    refine ⟨13810355326011696758301919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18413807101348929011069225 13810355326011696758301919)
    ·
      refine ⟨20715532989017545137452879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13810355326011696758301919 20715532989017545137452879)
      ·
        refine ⟨31073299483526317706179319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20715532989017545137452879 31073299483526317706179319)
        ·
          refine ⟨46609949225289476559268979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31073299483526317706179319 46609949225289476559268979)
          ·
            refine ⟨69914923837934214838903469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46609949225289476559268979 69914923837934214838903469)
            ·
              refine ⟨26218096439225330564588801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69914923837934214838903469 26218096439225330564588801)
              ·
                refine ⟨19663572329418997923441601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26218096439225330564588801 19663572329418997923441601)
                ·
                  refine ⟨14747679247064248442581201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19663572329418997923441601 14747679247064248442581201)
                  ·
                    refine ⟨11060759435298186331935901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14747679247064248442581201 11060759435298186331935901)
                    ·
                      refine ⟨4147784788236819874475963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11060759435298186331935901 4147784788236819874475963)
                      ·
                        rfl

theorem cell23_8077782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_8077782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077782 prefixEnd_8077782 := by exact prefixLift 8077782
  have htrace : WordTrace (prefixWord ++ tailWord_8077782) baseStart_8077782 baseEnd_8077782 := by
    simpa [prefixWord, tailWord_8077782, baseEnd_8077782] using wordTrace_append hprefix tailTrace_8077782
  have hstable : (prefixWord ++ tailWord_8077782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077782).length < 2 ^ (prefixWord ++ tailWord_8077782).sum := by decide
  have hdescent : baseEnd_8077782 < baseStart_8077782 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077789 : List Nat := [1, 4, 3, 1, 1, 1, 5, 2, 1, 4]
def baseStart_8077789 : Nat := 118140960795 + 8077789 * 2 ^ 59
def prefixEnd_8077789 : Nat := 4983230072969 + 3 ^ 40 * 8077789 * 2
def baseEnd_8077789 : Nat := 1382596127533800449029477

theorem tailTrace_8077789 : CollatzResearch.WordTrace tailWord_8077789 prefixEnd_8077789 1382596127533800449029477 := by
  unfold tailWord_8077789
  simp only [CollatzResearch.WordTrace]
  refine ⟨294621168932557504372612421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196414112621705002915074947 294621168932557504372612421)
  ·
    refine ⟨55241469174854532069864829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294621168932557504372612421 55241469174854532069864829)
    ·
      refine ⟨20715550940570449526199311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55241469174854532069864829 20715550940570449526199311)
      ·
        refine ⟨31073326410855674289298967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20715550940570449526199311 31073326410855674289298967)
        ·
          refine ⟨46609989616283511433948451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31073326410855674289298967 46609989616283511433948451)
          ·
            refine ⟨69914984424425267150922677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46609989616283511433948451 69914984424425267150922677)
            ·
              refine ⟨6554529789789868795399001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69914984424425267150922677 6554529789789868795399001)
              ·
                refine ⟨4915897342342401596549251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554529789789868795399001 4915897342342401596549251)
                ·
                  refine ⟨7373846013513602394823877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915897342342401596549251 7373846013513602394823877)
                  ·
                    refine ⟨1382596127533800449029477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7373846013513602394823877 1382596127533800449029477)
                    ·
                      rfl

theorem cell23_8077789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_8077789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077789 prefixEnd_8077789 := by exact prefixLift 8077789
  have htrace : WordTrace (prefixWord ++ tailWord_8077789) baseStart_8077789 baseEnd_8077789 := by
    simpa [prefixWord, tailWord_8077789, baseEnd_8077789] using wordTrace_append hprefix tailTrace_8077789
  have hstable : (prefixWord ++ tailWord_8077789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077789).length < 2 ^ (prefixWord ++ tailWord_8077789).sum := by decide
  have hdescent : baseEnd_8077789 < baseStart_8077789 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077802 : List Nat := [3, 1, 3, 1, 3, 3, 2, 1, 6]
def baseStart_8077802 : Nat := 118140960795 + 8077802 * 2 ^ 59
def prefixEnd_8077802 : Nat := 4983230072969 + 3 ^ 40 * 8077802 * 2
def baseEnd_8077802 : Nat := 460866117538878866247319

theorem tailTrace_8077802 : CollatzResearch.WordTrace tailWord_8077802 prefixEnd_8077802 460866117538878866247319 := by
  unfold tailWord_8077802
  simp only [CollatzResearch.WordTrace]
  refine ⟨73655410770377601898208915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196414428721006938395223773 73655410770377601898208915)
  ·
    refine ⟨110483116155566402847313373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73655410770377601898208915 110483116155566402847313373)
    ·
      refine ⟨41431168558337401067742515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110483116155566402847313373 41431168558337401067742515)
      ·
        refine ⟨62146752837506101601613773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41431168558337401067742515 62146752837506101601613773)
        ·
          refine ⟨23305032314064788100605165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62146752837506101601613773 23305032314064788100605165)
          ·
            refine ⟨8739387117774295537726937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23305032314064788100605165 8739387117774295537726937)
            ·
              refine ⟨6554540338330721653295203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739387117774295537726937 6554540338330721653295203)
              ·
                refine ⟨9831810507496082479942805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554540338330721653295203 9831810507496082479942805)
                ·
                  refine ⟨460866117538878866247319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9831810507496082479942805 460866117538878866247319)
                  ·
                    rfl

theorem cell23_8077802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 2, 1, 6].length) (baseStart_8077802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077802 prefixEnd_8077802 := by exact prefixLift 8077802
  have htrace : WordTrace (prefixWord ++ tailWord_8077802) baseStart_8077802 baseEnd_8077802 := by
    simpa [prefixWord, tailWord_8077802, baseEnd_8077802] using wordTrace_append hprefix tailTrace_8077802
  have hstable : (prefixWord ++ tailWord_8077802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077802).length < 2 ^ (prefixWord ++ tailWord_8077802).sum := by decide
  have hdescent : baseEnd_8077802 < baseStart_8077802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077889 : List Nat := [1, 2, 5, 1, 1, 2, 4, 1, 1, 2, 3]
def baseStart_8077889 : Nat := 118140960795 + 8077889 * 2 ^ 59
def prefixEnd_8077889 : Nat := 4983230072969 + 3 ^ 40 * 8077889 * 2
def baseEnd_8077889 : Nat := 4147839730666850955837971

theorem tailTrace_8077889 : CollatzResearch.WordTrace tailWord_8077889 prefixEnd_8077889 4147839730666850955837971 := by
  unfold tailWord_8077889
  simp only [CollatzResearch.WordTrace]
  refine ⟨294624816232195221451252721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196416544154796814300835147 294624816232195221451252721)
  ·
    refine ⟨220968612174146416088439541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294624816232195221451252721 220968612174146416088439541)
    ·
      refine ⟨20715807391326226508291207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220968612174146416088439541 20715807391326226508291207)
      ·
        refine ⟨31073711086989339762436811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20715807391326226508291207 31073711086989339762436811)
        ·
          refine ⟨46610566630484009643655217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31073711086989339762436811 46610566630484009643655217)
          ·
            refine ⟨34957924972863007232741413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46610566630484009643655217 34957924972863007232741413)
            ·
              refine ⟨6554610932411813856139015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34957924972863007232741413 6554610932411813856139015)
              ·
                refine ⟨9831916398617720784208523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554610932411813856139015 9831916398617720784208523)
                ·
                  refine ⟨14747874597926581176312785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9831916398617720784208523 14747874597926581176312785)
                  ·
                    refine ⟨11060905948444935882234589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14747874597926581176312785 11060905948444935882234589)
                    ·
                      refine ⟨4147839730666850955837971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11060905948444935882234589 4147839730666850955837971)
                      ·
                        rfl

theorem cell23_8077889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_8077889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077889 prefixEnd_8077889 := by exact prefixLift 8077889
  have htrace : WordTrace (prefixWord ++ tailWord_8077889) baseStart_8077889 baseEnd_8077889 := by
    simpa [prefixWord, tailWord_8077889, baseEnd_8077889] using wordTrace_append hprefix tailTrace_8077889
  have hstable : (prefixWord ++ tailWord_8077889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077889).length < 2 ^ (prefixWord ++ tailWord_8077889).sum := by decide
  have hdescent : baseEnd_8077889 < baseStart_8077889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077945 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 5]
def baseStart_8077945 : Nat := 118140960795 + 8077945 * 2 ^ 59
def prefixEnd_8077945 : Nat := 4983230072969 + 3 ^ 40 * 8077945 * 2
def baseEnd_8077945 : Nat := 4147868485583502736737713

theorem tailTrace_8077945 : CollatzResearch.WordTrace tailWord_8077945 prefixEnd_8077945 4147868485583502736737713 := by
  unfold tailWord_8077945
  simp only [CollatzResearch.WordTrace]
  refine ⟨294626858719992343015291289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196417905813328228676860859 294626858719992343015291289)
  ·
    refine ⟨220970144039994257261468467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294626858719992343015291289 220970144039994257261468467)
    ·
      refine ⟨331455216059991385892202701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220970144039994257261468467 331455216059991385892202701)
      ·
        refine ⟨124295706022496769709576013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331455216059991385892202701 124295706022496769709576013)
        ·
          refine ⟨46610889758436288641091005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124295706022496769709576013 46610889758436288641091005)
          ·
            refine ⟨17479083659413608240409127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46610889758436288641091005 17479083659413608240409127)
            ·
              refine ⟨26218625489120412360613691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17479083659413608240409127 26218625489120412360613691)
              ·
                refine ⟨39327938233680618540920537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26218625489120412360613691 39327938233680618540920537)
                ·
                  refine ⟨29495953675260463905690403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39327938233680618540920537 29495953675260463905690403)
                  ·
                    refine ⟨44243930512890695858535605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29495953675260463905690403 44243930512890695858535605)
                    ·
                      refine ⟨4147868485583502736737713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44243930512890695858535605 4147868485583502736737713)
                      ·
                        rfl

theorem cell23_8077945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_8077945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077945 prefixEnd_8077945 := by exact prefixLift 8077945
  have htrace : WordTrace (prefixWord ++ tailWord_8077945) baseStart_8077945 baseEnd_8077945 := by
    simpa [prefixWord, tailWord_8077945, baseEnd_8077945] using wordTrace_append hprefix tailTrace_8077945
  have hstable : (prefixWord ++ tailWord_8077945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077945).length < 2 ^ (prefixWord ++ tailWord_8077945).sum := by decide
  have hdescent : baseEnd_8077945 < baseStart_8077945 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077948 : List Nat := [2, 2, 2, 1, 1, 2, 2, 2, 9]
def baseStart_8077948 : Nat := 118140960795 + 8077948 * 2 ^ 59
def prefixEnd_8077948 : Nat := 4983230072969 + 3 ^ 40 * 8077948 * 2
def baseEnd_8077948 : Nat := 460874447336162913888911

theorem tailTrace_8077948 : CollatzResearch.WordTrace tailWord_8077948 prefixEnd_8077948 460874447336162913888911 := by
  unfold tailWord_8077948
  simp only [CollatzResearch.WordTrace]
  refine ⟨147313484069490737263825249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196417978759320983018433665 147313484069490737263825249)
  ·
    refine ⟨110485113052118052947868937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147313484069490737263825249 110485113052118052947868937)
    ·
      refine ⟨82863834789088539710901703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110485113052118052947868937 82863834789088539710901703)
      ·
        refine ⟨124295752183632809566352555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82863834789088539710901703 124295752183632809566352555)
        ·
          refine ⟨186443628275449214349528833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124295752183632809566352555 186443628275449214349528833)
          ·
            refine ⟨139832721206586910762146625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186443628275449214349528833 139832721206586910762146625)
            ·
              refine ⟨104874540904940183071609969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139832721206586910762146625 104874540904940183071609969)
              ·
                refine ⟨78655905678705137303707477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104874540904940183071609969 78655905678705137303707477)
                ·
                  refine ⟨460874447336162913888911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78655905678705137303707477 460874447336162913888911)
                  ·
                    rfl

theorem cell23_8077948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 2, 9].length) (baseStart_8077948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077948 prefixEnd_8077948 := by exact prefixLift 8077948
  have htrace : WordTrace (prefixWord ++ tailWord_8077948) baseStart_8077948 baseEnd_8077948 := by
    simpa [prefixWord, tailWord_8077948, baseEnd_8077948] using wordTrace_append hprefix tailTrace_8077948
  have hstable : (prefixWord ++ tailWord_8077948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077948).length < 2 ^ (prefixWord ++ tailWord_8077948).sum := by decide
  have hdescent : baseEnd_8077948 < baseStart_8077948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077954 : List Nat := [3, 4, 3, 1, 1, 1, 3, 2, 1, 2, 2]
def baseStart_8077954 : Nat := 118140960795 + 8077954 * 2 ^ 59
def prefixEnd_8077954 : Nat := 4983230072969 + 3 ^ 40 * 8077954 * 2
def baseEnd_8077954 : Nat := 4147873106909393201525173

theorem tailTrace_8077954 : CollatzResearch.WordTrace tailWord_8077954 prefixEnd_8077954 4147873106909393201525173 := by
  unfold tailWord_8077954
  simp only [CollatzResearch.WordTrace]
  refine ⟨73656796744239934388092229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196418124651306491701579277 73656796744239934388092229)
  ·
    refine ⟨13810649389544987697767293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73656796744239934388092229 13810649389544987697767293)
    ·
      refine ⟨5178993521079370386662735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13810649389544987697767293 5178993521079370386662735)
      ·
        refine ⟨7768490281619055579994103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178993521079370386662735 7768490281619055579994103)
        ·
          refine ⟨11652735422428583369991155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768490281619055579994103 11652735422428583369991155)
          ·
            refine ⟨17479103133642875054986733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11652735422428583369991155 17479103133642875054986733)
            ·
              refine ⟨6554663675116078145620025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17479103133642875054986733 6554663675116078145620025)
              ·
                refine ⟨4915997756337058609215019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554663675116078145620025 4915997756337058609215019)
                ·
                  refine ⟨7373996634505587913822529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4915997756337058609215019 7373996634505587913822529)
                  ·
                    refine ⟨5530497475879190935366897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7373996634505587913822529 5530497475879190935366897)
                    ·
                      refine ⟨4147873106909393201525173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530497475879190935366897 4147873106909393201525173)
                      ·
                        rfl

theorem cell23_8077954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_8077954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077954 prefixEnd_8077954 := by exact prefixLift 8077954
  have htrace : WordTrace (prefixWord ++ tailWord_8077954) baseStart_8077954 baseEnd_8077954 := by
    simpa [prefixWord, tailWord_8077954, baseEnd_8077954] using wordTrace_append hprefix tailTrace_8077954
  have hstable : (prefixWord ++ tailWord_8077954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077954).length < 2 ^ (prefixWord ++ tailWord_8077954).sum := by decide
  have hdescent : baseEnd_8077954 < baseStart_8077954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077959 : List Nat := [1, 1, 4, 2, 1, 2, 2, 4, 2, 2, 2]
def baseStart_8077959 : Nat := 118140960795 + 8077959 * 2 ^ 59
def prefixEnd_8077959 : Nat := 4983230072969 + 3 ^ 40 * 8077959 * 2
def baseEnd_8077959 : Nat := 4147875674312665681962649

theorem tailTrace_8077959 : CollatzResearch.WordTrace tailWord_8077959 prefixEnd_8077959 4147875674312665681962649 := by
  unfold tailWord_8077959
  simp only [CollatzResearch.WordTrace]
  refine ⟨294627369341941623406300931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196418246227961082270867287 294627369341941623406300931)
  ·
    refine ⟨441941054012912435109451397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294627369341941623406300931 441941054012912435109451397)
    ·
      refine ⟨82863947627421081583022137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441941054012912435109451397 82863947627421081583022137)
      ·
        refine ⟨62147960720565811187266603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82863947627421081583022137 62147960720565811187266603)
        ·
          refine ⟨93221941080848716780899905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62147960720565811187266603 93221941080848716780899905)
          ·
            refine ⟨69916455810636537585674929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93221941080848716780899905 69916455810636537585674929)
            ·
              refine ⟨52437341857977403189256197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69916455810636537585674929 52437341857977403189256197)
              ·
                refine ⟨9832001598370763097985537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52437341857977403189256197 9832001598370763097985537)
                ·
                  refine ⟨7374001198778072323489153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9832001598370763097985537 7374001198778072323489153)
                  ·
                    refine ⟨5530500899083554242616865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7374001198778072323489153 5530500899083554242616865)
                    ·
                      refine ⟨4147875674312665681962649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530500899083554242616865 4147875674312665681962649)
                      ·
                        rfl

theorem cell23_8077959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_8077959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077959 prefixEnd_8077959 := by exact prefixLift 8077959
  have htrace : WordTrace (prefixWord ++ tailWord_8077959) baseStart_8077959 baseEnd_8077959 := by
    simpa [prefixWord, tailWord_8077959, baseEnd_8077959] using wordTrace_append hprefix tailTrace_8077959
  have hstable : (prefixWord ++ tailWord_8077959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077959).length < 2 ^ (prefixWord ++ tailWord_8077959).sum := by decide
  have hdescent : baseEnd_8077959 < baseStart_8077959 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8077975 : List Nat := [1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 3]
def baseStart_8077975 : Nat := 118140960795 + 8077975 * 2 ^ 59
def prefixEnd_8077975 : Nat := 4983230072969 + 3 ^ 40 * 8077975 * 2
def baseEnd_8077975 : Nat := 4147883890003137619362575

theorem tailTrace_8077975 : CollatzResearch.WordTrace tailWord_8077975 prefixEnd_8077975 4147883890003137619362575 := by
  unfold tailWord_8077975
  simp only [CollatzResearch.WordTrace]
  refine ⟨294627952909883658138883379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196418635273255772092588919 294627952909883658138883379)
  ·
    refine ⟨441941929364825487208325069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294627952909883658138883379 441941929364825487208325069)
    ·
      refine ⟨165728223511809557703121901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441941929364825487208325069 165728223511809557703121901)
      ·
        refine ⟨62148083816928584138670713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165728223511809557703121901 62148083816928584138670713)
        ·
          refine ⟨46611062862696438104003035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62148083816928584138670713 46611062862696438104003035)
          ·
            refine ⟨69916594294044657156004553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46611062862696438104003035 69916594294044657156004553)
            ·
              refine ⟨52437445720533492867003415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69916594294044657156004553 52437445720533492867003415)
              ·
                refine ⟨78656168580800239300505123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52437445720533492867003415 78656168580800239300505123)
                ·
                  refine ⟨117984252871200358950757685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78656168580800239300505123 117984252871200358950757685)
                  ·
                    refine ⟨11061023706675033651633533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117984252871200358950757685 11061023706675033651633533)
                    ·
                      refine ⟨4147883890003137619362575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11061023706675033651633533 4147883890003137619362575)
                      ·
                        rfl

theorem cell23_8077975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_8077975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8077975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8077975 prefixEnd_8077975 := by exact prefixLift 8077975
  have htrace : WordTrace (prefixWord ++ tailWord_8077975) baseStart_8077975 baseEnd_8077975 := by
    simpa [prefixWord, tailWord_8077975, baseEnd_8077975] using wordTrace_append hprefix tailTrace_8077975
  have hstable : (prefixWord ++ tailWord_8077975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8077975).length < 2 ^ (prefixWord ++ tailWord_8077975).sum := by decide
  have hdescent : baseEnd_8077975 < baseStart_8077975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8077975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078025 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 9, 4]
def baseStart_8078025 : Nat := 118140960795 + 8078025 * 2 ^ 59
def prefixEnd_8078025 : Nat := 4983230072969 + 3 ^ 40 * 8078025 * 2
def baseEnd_8078025 : Nat := 1382636521345287474579115

theorem tailTrace_8078025 : CollatzResearch.WordTrace tailWord_8078025 prefixEnd_8078025 1382636521345287474579115 := by
  unfold tailWord_8078025
  simp only [CollatzResearch.WordTrace]
  refine ⟨294629776559702516678203529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196419851039801677785469019 294629776559702516678203529)
  ·
    refine ⟨220972332419776887508652647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294629776559702516678203529 220972332419776887508652647)
    ·
      refine ⟨331458498629665331262978971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220972332419776887508652647 331458498629665331262978971)
      ·
        refine ⟨497187747944497996894468457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331458498629665331262978971 497187747944497996894468457)
        ·
          refine ⟨372890810958373497670851343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497187747944497996894468457 372890810958373497670851343)
          ·
            refine ⟨559336216437560246506277015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372890810958373497670851343 559336216437560246506277015)
            ·
              refine ⟨839004324656340369759415523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559336216437560246506277015 839004324656340369759415523)
              ·
                refine ⟨1258506486984510554639123285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 839004324656340369759415523 1258506486984510554639123285)
                ·
                  refine ⟨7374061447174866531088613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1258506486984510554639123285 7374061447174866531088613)
                  ·
                    refine ⟨1382636521345287474579115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7374061447174866531088613 1382636521345287474579115)
                    ·
                      rfl

theorem cell23_8078025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 4].length) (baseStart_8078025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078025 prefixEnd_8078025 := by exact prefixLift 8078025
  have htrace : WordTrace (prefixWord ++ tailWord_8078025) baseStart_8078025 baseEnd_8078025 := by
    simpa [prefixWord, tailWord_8078025, baseEnd_8078025] using wordTrace_append hprefix tailTrace_8078025
  have hstable : (prefixWord ++ tailWord_8078025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078025).length < 2 ^ (prefixWord ++ tailWord_8078025).sum := by decide
  have hdescent : baseEnd_8078025 < baseStart_8078025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078042 : List Nat := [3, 1, 1, 2, 2, 2, 3, 2, 3, 4]
def baseStart_8078042 : Nat := 118140960795 + 8078042 * 2 ^ 59
def prefixEnd_8078042 : Nat := 4983230072969 + 3 ^ 40 * 8078042 * 2
def baseEnd_8078042 : Nat := 1382639431068996285741589

theorem tailTrace_8078042 : CollatzResearch.WordTrace tailWord_8078042 prefixEnd_8078042 1382639431068996285741589 := by
  unfold tailWord_8078042
  simp only [CollatzResearch.WordTrace]
  refine ⟨73657599150160232145393095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196420264400427285721048253 73657599150160232145393095)
  ·
    refine ⟨110486398725240348218089643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73657599150160232145393095 110486398725240348218089643)
    ·
      refine ⟨165729598087860522327134465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110486398725240348218089643 165729598087860522327134465)
      ·
        refine ⟨124297198565895391745350849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165729598087860522327134465 124297198565895391745350849)
        ·
          refine ⟨93222898924421543809013137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124297198565895391745350849 93222898924421543809013137)
          ·
            refine ⟨69917174193316157856759853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93222898924421543809013137 69917174193316157856759853)
            ·
              refine ⟨26218940322493559196284945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69917174193316157856759853 26218940322493559196284945)
              ·
                refine ⟨19664205241870169397213709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26218940322493559196284945 19664205241870169397213709)
                ·
                  refine ⟨7374076965701313523955141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19664205241870169397213709 7374076965701313523955141)
                  ·
                    refine ⟨1382639431068996285741589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7374076965701313523955141 1382639431068996285741589)
                    ·
                      rfl

theorem cell23_8078042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 3, 4].length) (baseStart_8078042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078042 prefixEnd_8078042 := by exact prefixLift 8078042
  have htrace : WordTrace (prefixWord ++ tailWord_8078042) baseStart_8078042 baseEnd_8078042 := by
    simpa [prefixWord, tailWord_8078042, baseEnd_8078042] using wordTrace_append hprefix tailTrace_8078042
  have hstable : (prefixWord ++ tailWord_8078042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078042).length < 2 ^ (prefixWord ++ tailWord_8078042).sum := by decide
  have hdescent : baseEnd_8078042 < baseStart_8078042 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078049 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 4]
def baseStart_8078049 : Nat := 118140960795 + 8078049 * 2 ^ 59
def prefixEnd_8078049 : Nat := 4983230072969 + 3 ^ 40 * 8078049 * 2
def baseEnd_8078049 : Nat := 4147921887571570329837235

theorem tailTrace_8078049 : CollatzResearch.WordTrace tailWord_8078049 prefixEnd_8078049 4147921887571570329837235 := by
  unfold tailWord_8078049
  simp only [CollatzResearch.WordTrace]
  refine ⟨294630651911615568777077201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196420434607743712518051467 294630651911615568777077201)
  ·
    refine ⟨220972988933711676582807901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294630651911615568777077201 220972988933711676582807901)
    ·
      refine ⟨82864870850141878718552963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220972988933711676582807901 82864870850141878718552963)
      ·
        refine ⟨124297306275212818077829445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82864870850141878718552963 124297306275212818077829445)
        ·
          refine ⟨23305744926602403389593021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124297306275212818077829445 23305744926602403389593021)
          ·
            refine ⟨8739654347475901271097383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23305744926602403389593021 8739654347475901271097383)
            ·
              refine ⟨13109481521213851906646075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739654347475901271097383 13109481521213851906646075)
              ·
                refine ⟨19664222281820777859969113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13109481521213851906646075 19664222281820777859969113)
                ·
                  refine ⟨14748166711365583394976835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19664222281820777859969113 14748166711365583394976835)
                  ·
                    refine ⟨22122250067048375092465253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14748166711365583394976835 22122250067048375092465253)
                    ·
                      refine ⟨4147921887571570329837235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22122250067048375092465253 4147921887571570329837235)
                      ·
                        rfl

theorem cell23_8078049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_8078049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078049 prefixEnd_8078049 := by exact prefixLift 8078049
  have htrace : WordTrace (prefixWord ++ tailWord_8078049) baseStart_8078049 baseEnd_8078049 := by
    simpa [prefixWord, tailWord_8078049, baseEnd_8078049] using wordTrace_append hprefix tailTrace_8078049
  have hstable : (prefixWord ++ tailWord_8078049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078049).length < 2 ^ (prefixWord ++ tailWord_8078049).sum := by decide
  have hdescent : baseEnd_8078049 < baseStart_8078049 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078052 : List Nat := [2, 3, 1, 1, 1, 5, 1, 1, 1, 4, 3]
def baseStart_8078052 : Nat := 118140960795 + 8078052 * 2 ^ 59
def prefixEnd_8078052 : Nat := 4983230072969 + 3 ^ 40 * 8078052 * 2
def baseEnd_8078052 : Nat := 4147923428013533818099721

theorem tailTrace_8078052 : CollatzResearch.WordTrace tailWord_8078052 prefixEnd_8078052 4147923428013533818099721 := by
  unfold tailWord_8078052
  simp only [CollatzResearch.WordTrace]
  refine ⟨147315380665302350144718205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196420507553736466859624273 147315380665302350144718205)
  ·
    refine ⟨55243267749488381304269327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147315380665302350144718205 55243267749488381304269327)
    ·
      refine ⟨82864901624232571956403991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55243267749488381304269327 82864901624232571956403991)
      ·
        refine ⟨124297352436348857934605987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82864901624232571956403991 124297352436348857934605987)
        ·
          refine ⟨186446028654523286901908981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124297352436348857934605987 186446028654523286901908981)
          ·
            refine ⟨17479315186361558147053967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186446028654523286901908981 17479315186361558147053967)
            ·
              refine ⟨26218972779542337220580951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17479315186361558147053967 26218972779542337220580951)
              ·
                refine ⟨39328459169313505830871427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26218972779542337220580951 39328459169313505830871427)
                ·
                  refine ⟨58992688753970258746307141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39328459169313505830871427 58992688753970258746307141)
                  ·
                    refine ⟨11061129141369423514932589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58992688753970258746307141 11061129141369423514932589)
                    ·
                      refine ⟨4147923428013533818099721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11061129141369423514932589 4147923428013533818099721)
                      ·
                        rfl

theorem cell23_8078052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_8078052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078052 prefixEnd_8078052 := by exact prefixLift 8078052
  have htrace : WordTrace (prefixWord ++ tailWord_8078052) baseStart_8078052 baseEnd_8078052 := by
    simpa [prefixWord, tailWord_8078052, baseEnd_8078052] using wordTrace_append hprefix tailTrace_8078052
  have hstable : (prefixWord ++ tailWord_8078052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078052).length < 2 ^ (prefixWord ++ tailWord_8078052).sum := by decide
  have hdescent : baseEnd_8078052 < baseStart_8078052 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078085 : List Nat := [1, 3, 1, 1, 2, 1, 1, 3, 5, 5]
def baseStart_8078085 : Nat := 118140960795 + 8078085 * 2 ^ 59
def prefixEnd_8078085 : Nat := 4983230072969 + 3 ^ 40 * 8078085 * 2
def baseEnd_8078085 : Nat := 1382646790958377396329023

theorem tailTrace_8078085 : CollatzResearch.WordTrace tailWord_8078085 prefixEnd_8078085 1382646790958377396329023 := by
  unfold tailWord_8078085
  simp only [CollatzResearch.WordTrace]
  refine ⟨294631964939485146925387709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196421309959656764616925139 294631964939485146925387709)
  ·
    refine ⟨110486986852306930097020391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294631964939485146925387709 110486986852306930097020391)
    ·
      refine ⟨165730480278460395145530587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110486986852306930097020391 165730480278460395145530587)
      ·
        refine ⟨248595720417690592718295881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165730480278460395145530587 248595720417690592718295881)
        ·
          refine ⟨186446790313267944538721911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248595720417690592718295881 186446790313267944538721911)
          ·
            refine ⟨279670185469901916808082867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186446790313267944538721911 279670185469901916808082867)
            ·
              refine ⟨419505278204852875212124301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279670185469901916808082867 419505278204852875212124301)
              ·
                refine ⟨157314479326819828204546613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 419505278204852875212124301 157314479326819828204546613)
                ·
                  refine ⟨14748232436889358894176245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157314479326819828204546613 14748232436889358894176245)
                  ·
                    refine ⟨1382646790958377396329023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14748232436889358894176245 1382646790958377396329023)
                    ·
                      rfl

theorem cell23_8078085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_8078085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078085 prefixEnd_8078085 := by exact prefixLift 8078085
  have htrace : WordTrace (prefixWord ++ tailWord_8078085) baseStart_8078085 baseEnd_8078085 := by
    simpa [prefixWord, tailWord_8078085, baseEnd_8078085] using wordTrace_append hprefix tailTrace_8078085
  have hstable : (prefixWord ++ tailWord_8078085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078085).length < 2 ^ (prefixWord ++ tailWord_8078085).sum := by decide
  have hdescent : baseEnd_8078085 < baseStart_8078085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078115 : List Nat := [1, 1, 1, 4, 2, 1, 1, 3, 3, 6]
def baseStart_8078115 : Nat := 118140960795 + 8078115 * 2 ^ 59
def prefixEnd_8078115 : Nat := 4983230072969 + 3 ^ 40 * 8078115 * 2
def baseEnd_8078115 : Nat := 1382651925764922357203977

theorem tailTrace_8078115 : CollatzResearch.WordTrace tailWord_8078115 prefixEnd_8078115 1382651925764922357203977 := by
  unfold tailWord_8078115
  simp only [CollatzResearch.WordTrace]
  refine ⟨294633059129376462048979799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196422039419584308032653199 294633059129376462048979799)
  ·
    refine ⟨441949588694064693073469699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294633059129376462048979799 441949588694064693073469699)
    ·
      refine ⟨662924383041097039610204549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441949588694064693073469699 662924383041097039610204549)
      ·
        refine ⟨124298321820205694926913353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 662924383041097039610204549 124298321820205694926913353)
        ·
          refine ⟨93223741365154271195185015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124298321820205694926913353 93223741365154271195185015)
          ·
            refine ⟨139835612047731406792777523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93223741365154271195185015 139835612047731406792777523)
            ·
              refine ⟨209753418071597110189166285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139835612047731406792777523 209753418071597110189166285)
              ·
                refine ⟨78657531776848916320937357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209753418071597110189166285 78657531776848916320937357)
                ·
                  refine ⟨29496574416318343620351509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78657531776848916320937357 29496574416318343620351509)
                  ·
                    refine ⟨1382651925764922357203977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29496574416318343620351509 1382651925764922357203977)
                    ·
                      rfl

theorem cell23_8078115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 3, 3, 6].length) (baseStart_8078115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078115 prefixEnd_8078115 := by exact prefixLift 8078115
  have htrace : WordTrace (prefixWord ++ tailWord_8078115) baseStart_8078115 baseEnd_8078115 := by
    simpa [prefixWord, tailWord_8078115, baseEnd_8078115] using wordTrace_append hprefix tailTrace_8078115
  have hstable : (prefixWord ++ tailWord_8078115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078115).length < 2 ^ (prefixWord ++ tailWord_8078115).sum := by decide
  have hdescent : baseEnd_8078115 < baseStart_8078115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078126 : List Nat := [4, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_8078126 : Nat := 118140960795 + 8078126 * 2 ^ 59
def prefixEnd_8078126 : Nat := 4983230072969 + 3 ^ 40 * 8078126 * 2
def baseEnd_8078126 : Nat := 4147961425581966528574381

theorem tailTrace_8078126 : CollatzResearch.WordTrace tailWord_8078126 prefixEnd_8078126 4147961425581966528574381 := by
  unfold tailWord_8078126
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829182541542076365953779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196422306888224407285086821 36829182541542076365953779)
  ·
    refine ⟨55243773812313114548930669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36829182541542076365953779 55243773812313114548930669)
    ·
      refine ⟨20716415179617417955849001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55243773812313114548930669 20716415179617417955849001)
      ·
        refine ⟨15537311384713063466886751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20716415179617417955849001 15537311384713063466886751)
        ·
          refine ⟨23305967077069595200330127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15537311384713063466886751 23305967077069595200330127)
          ·
            refine ⟨34958950615604392800495191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23305967077069595200330127 34958950615604392800495191)
            ·
              refine ⟨52438425923406589200742787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34958950615604392800495191 52438425923406589200742787)
              ·
                refine ⟨78657638885109883801114181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52438425923406589200742787 78657638885109883801114181)
                ·
                  refine ⟨14748307290958103212708909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78657638885109883801114181 14748307290958103212708909)
                  ·
                    refine ⟨5530615234109288704765841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14748307290958103212708909 5530615234109288704765841)
                    ·
                      refine ⟨4147961425581966528574381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530615234109288704765841 4147961425581966528574381)
                      ·
                        rfl

theorem cell23_8078126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_8078126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078126 prefixEnd_8078126 := by exact prefixLift 8078126
  have htrace : WordTrace (prefixWord ++ tailWord_8078126) baseStart_8078126 baseEnd_8078126 := by
    simpa [prefixWord, tailWord_8078126, baseEnd_8078126] using wordTrace_append hprefix tailTrace_8078126
  have hstable : (prefixWord ++ tailWord_8078126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078126).length < 2 ^ (prefixWord ++ tailWord_8078126).sum := by decide
  have hdescent : baseEnd_8078126 < baseStart_8078126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078135 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_8078135 : Nat := 118140960795 + 8078135 * 2 ^ 59
def prefixEnd_8078135 : Nat := 4983230072969 + 3 ^ 40 * 8078135 * 2
def baseEnd_8078135 : Nat := 4147966046907856993361839

theorem tailTrace_8078135 : CollatzResearch.WordTrace tailWord_8078135 prefixEnd_8078135 4147966046907856993361839 := by
  unfold tailWord_8078135
  simp only [CollatzResearch.WordTrace]
  refine ⟨294633788589304005464707859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196422525726202670309805239 294633788589304005464707859)
  ·
    refine ⟨441950682883956008197061789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294633788589304005464707859 441950682883956008197061789)
    ·
      refine ⟨165731506081483503073898171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441950682883956008197061789 165731506081483503073898171)
      ·
        refine ⟨248597259122225254610847257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165731506081483503073898171 248597259122225254610847257)
        ·
          refine ⟨186447944341668940958135443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248597259122225254610847257 186447944341668940958135443)
          ·
            refine ⟨279671916512503411437203165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186447944341668940958135443 279671916512503411437203165)
            ·
              refine ⟨104876968692188779288951187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279671916512503411437203165 104876968692188779288951187)
              ·
                refine ⟨157315453038283168933426781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104876968692188779288951187 157315453038283168933426781)
                ·
                  refine ⟨58993294889356188350035043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157315453038283168933426781 58993294889356188350035043)
                  ·
                    refine ⟨88489942334034282525052565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58993294889356188350035043 88489942334034282525052565)
                    ·
                      refine ⟨4147966046907856993361839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88489942334034282525052565 4147966046907856993361839)
                      ·
                        rfl

theorem cell23_8078135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_8078135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078135 prefixEnd_8078135 := by exact prefixLift 8078135
  have htrace : WordTrace (prefixWord ++ tailWord_8078135) baseStart_8078135 baseEnd_8078135 := by
    simpa [prefixWord, tailWord_8078135, baseEnd_8078135] using wordTrace_append hprefix tailTrace_8078135
  have hstable : (prefixWord ++ tailWord_8078135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078135).length < 2 ^ (prefixWord ++ tailWord_8078135).sum := by decide
  have hdescent : baseEnd_8078135 < baseStart_8078135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078152 : List Nat := [2, 1, 3, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_8078152 : Nat := 118140960795 + 8078152 * 2 ^ 59
def prefixEnd_8078152 : Nat := 4983230072969 + 3 ^ 40 * 8078152 * 2
def baseEnd_8078152 : Nat := 4147974776078983426849261

theorem tailTrace_8078152 : CollatzResearch.WordTrace tailWord_8078152 prefixEnd_8078152 4147974776078983426849261 := by
  unfold tailWord_8078152
  simp only [CollatzResearch.WordTrace]
  refine ⟨147317204315121208684038355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196422939086828278245384473 147317204315121208684038355)
  ·
    refine ⟨220975806472681813026057533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147317204315121208684038355 220975806472681813026057533)
    ·
      refine ⟨82865927427255679884771575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220975806472681813026057533 82865927427255679884771575)
      ·
        refine ⟨124298891140883519827157363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82865927427255679884771575 124298891140883519827157363)
        ·
          refine ⟨186448336711325279740736045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124298891140883519827157363 186448336711325279740736045)
          ·
            refine ⟨69918126266746979902776017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186448336711325279740736045 69918126266746979902776017)
            ·
              refine ⟨52438594700060234927082013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69918126266746979902776017 52438594700060234927082013)
              ·
                refine ⟨19664473012522588097655755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52438594700060234927082013 19664473012522588097655755)
                ·
                  refine ⟨29496709518783882146483633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19664473012522588097655755 29496709518783882146483633)
                  ·
                    refine ⟨22122532139087911609862725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29496709518783882146483633 22122532139087911609862725)
                    ·
                      refine ⟨4147974776078983426849261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22122532139087911609862725 4147974776078983426849261)
                      ·
                        rfl

theorem cell23_8078152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_8078152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078152 prefixEnd_8078152 := by exact prefixLift 8078152
  have htrace : WordTrace (prefixWord ++ tailWord_8078152) baseStart_8078152 baseEnd_8078152 := by
    simpa [prefixWord, tailWord_8078152, baseEnd_8078152] using wordTrace_append hprefix tailTrace_8078152
  have hstable : (prefixWord ++ tailWord_8078152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078152).length < 2 ^ (prefixWord ++ tailWord_8078152).sum := by decide
  have hdescent : baseEnd_8078152 < baseStart_8078152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078156 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 1, 1, 4]
def baseStart_8078156 : Nat := 118140960795 + 8078156 * 2 ^ 59
def prefixEnd_8078156 : Nat := 4983230072969 + 3 ^ 40 * 8078156 * 2
def baseEnd_8078156 : Nat := 4147976830001601411199243

theorem tailTrace_8078156 : CollatzResearch.WordTrace tailWord_8078156 prefixEnd_8078156 4147976830001601411199243 := by
  unfold tailWord_8078156
  simp only [CollatzResearch.WordTrace]
  refine ⟨147317277261113963025611161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196423036348151950700814881 147317277261113963025611161)
  ·
    refine ⟨110487957945835472269208371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147317277261113963025611161 110487957945835472269208371)
    ·
      refine ⟨165731936918753208403812557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110487957945835472269208371 165731936918753208403812557)
      ·
        refine ⟨62149476344532453151429709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165731936918753208403812557 62149476344532453151429709)
        ·
          refine ⟨23306053629199669931786141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62149476344532453151429709 23306053629199669931786141)
          ·
            refine ⟨8739770110949876224419803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23306053629199669931786141 8739770110949876224419803)
            ·
              refine ⟨13109655166424814336629705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8739770110949876224419803 13109655166424814336629705)
              ·
                refine ⟨9832241374818610752472279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13109655166424814336629705 9832241374818610752472279)
                ·
                  refine ⟨14748362062227916128708419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9832241374818610752472279 14748362062227916128708419)
                  ·
                    refine ⟨22122543093341874193062629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14748362062227916128708419 22122543093341874193062629)
                    ·
                      refine ⟨4147976830001601411199243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22122543093341874193062629 4147976830001601411199243)
                      ·
                        rfl

theorem cell23_8078156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_8078156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078156 prefixEnd_8078156 := by exact prefixLift 8078156
  have htrace : WordTrace (prefixWord ++ tailWord_8078156) baseStart_8078156 baseEnd_8078156 := by
    simpa [prefixWord, tailWord_8078156, baseEnd_8078156] using wordTrace_append hprefix tailTrace_8078156
  have hstable : (prefixWord ++ tailWord_8078156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078156).length < 2 ^ (prefixWord ++ tailWord_8078156).sum := by decide
  have hdescent : baseEnd_8078156 < baseStart_8078156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078176 : List Nat := [2, 1, 1, 3, 3, 1, 5, 1, 1, 2, 3]
def baseStart_8078176 : Nat := 118140960795 + 8078176 * 2 ^ 59
def prefixEnd_8078176 : Nat := 4983230072969 + 3 ^ 40 * 8078176 * 2
def baseEnd_8078176 : Nat := 4147987099614691332949151

theorem tailTrace_8078176 : CollatzResearch.WordTrace tailWord_8078176 prefixEnd_8078176 4147987099614691332949151 := by
  unfold tailWord_8078176
  simp only [CollatzResearch.WordTrace]
  refine ⟨147317641991077734733475191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196423522654770312977966921 147317641991077734733475191)
  ·
    refine ⟨220976462986616602100212787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147317641991077734733475191 220976462986616602100212787)
    ·
      refine ⟨331464694479924903150319181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220976462986616602100212787 331464694479924903150319181)
      ·
        refine ⟨124299260429971838681369693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331464694479924903150319181 124299260429971838681369693)
        ·
          refine ⟨46612222661239439505513635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124299260429971838681369693 46612222661239439505513635)
          ·
            refine ⟨69918333991859159258270453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46612222661239439505513635 69918333991859159258270453)
            ·
              refine ⟨6554843811736796180462855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69918333991859159258270453 6554843811736796180462855)
              ·
                refine ⟨9832265717605194270694283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6554843811736796180462855 9832265717605194270694283)
                ·
                  refine ⟨14748398576407791406041425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9832265717605194270694283 14748398576407791406041425)
                  ·
                    refine ⟨11061298932305843554531069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14748398576407791406041425 11061298932305843554531069)
                    ·
                      refine ⟨4147987099614691332949151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11061298932305843554531069 4147987099614691332949151)
                      ·
                        rfl

theorem cell23_8078176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 5, 1, 1, 2, 3].length) (baseStart_8078176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078176 prefixEnd_8078176 := by exact prefixLift 8078176
  have htrace : WordTrace (prefixWord ++ tailWord_8078176) baseStart_8078176 baseEnd_8078176 := by
    simpa [prefixWord, tailWord_8078176, baseEnd_8078176] using wordTrace_append hprefix tailTrace_8078176
  have hstable : (prefixWord ++ tailWord_8078176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078176).length < 2 ^ (prefixWord ++ tailWord_8078176).sum := by decide
  have hdescent : baseEnd_8078176 < baseStart_8078176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078185 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 7]
def baseStart_8078185 : Nat := 118140960795 + 8078185 * 2 ^ 59
def prefixEnd_8078185 : Nat := 4983230072969 + 3 ^ 40 * 8078185 * 2
def baseEnd_8078185 : Nat := 4147991720940581797736609

theorem tailTrace_8078185 : CollatzResearch.WordTrace tailWord_8078185 prefixEnd_8078185 4147991720940581797736609 := by
  unfold tailWord_8078185
  simp only [CollatzResearch.WordTrace]
  refine ⟨294635612239122864004028009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196423741492748576002685339 294635612239122864004028009)
  ·
    refine ⟨220976709179342148003021007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294635612239122864004028009 220976709179342148003021007)
    ·
      refine ⟨331465063769013222004531511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220976709179342148003021007 331465063769013222004531511)
      ·
        refine ⟨497197595653519833006797267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331465063769013222004531511 497197595653519833006797267)
        ·
          refine ⟨745796393480279749510195901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 497197595653519833006797267 745796393480279749510195901)
          ·
            refine ⟨279673647555104906066323463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 745796393480279749510195901 279673647555104906066323463)
            ·
              refine ⟨419510471332657359099485195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279673647555104906066323463 419510471332657359099485195)
              ·
                refine ⟨629265706998986038649227793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419510471332657359099485195 629265706998986038649227793)
                ·
                  refine ⟨471949280249239528986920845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629265706998986038649227793 471949280249239528986920845)
                  ·
                    refine ⟨176980980093464823370095317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 471949280249239528986920845 176980980093464823370095317)
                    ·
                      refine ⟨4147991720940581797736609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176980980093464823370095317 4147991720940581797736609)
                      ·
                        rfl

theorem cell23_8078185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 3, 7].length) (baseStart_8078185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078185 prefixEnd_8078185 := by exact prefixLift 8078185
  have htrace : WordTrace (prefixWord ++ tailWord_8078185) baseStart_8078185 baseEnd_8078185 := by
    simpa [prefixWord, tailWord_8078185, baseEnd_8078185] using wordTrace_append hprefix tailTrace_8078185
  have hstable : (prefixWord ++ tailWord_8078185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078185).length < 2 ^ (prefixWord ++ tailWord_8078185).sum := by decide
  have hdescent : baseEnd_8078185 < baseStart_8078185 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078212 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_8078212 : Nat := 118140960795 + 8078212 * 2 ^ 59
def prefixEnd_8078212 : Nat := 4983230072969 + 3 ^ 40 * 8078212 * 2
def baseEnd_8078212 : Nat := 4148005584918253192098985

theorem tailTrace_8078212 : CollatzResearch.WordTrace tailWord_8078212 prefixEnd_8078212 4148005584918253192098985 := by
  unfold tailWord_8078212
  simp only [CollatzResearch.WordTrace]
  refine ⟨147318298505012523807630445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196424398006683365076840593 147318298505012523807630445)
  ·
    refine ⟨55244361939379696427861417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147318298505012523807630445 55244361939379696427861417)
    ·
      refine ⟨41433271454534772320896063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55244361939379696427861417 41433271454534772320896063)
      ·
        refine ⟨62149907181802158481344095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41433271454534772320896063 62149907181802158481344095)
        ·
          refine ⟨93224860772703237722016143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62149907181802158481344095 93224860772703237722016143)
          ·
            refine ⟨139837291159054856583024215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93224860772703237722016143 139837291159054856583024215)
            ·
              refine ⟨209755936738582284874536323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139837291159054856583024215 209755936738582284874536323)
              ·
                refine ⟨314633905107873427311804485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209755936738582284874536323 314633905107873427311804485)
                ·
                  refine ⟨58993857207726267620963341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314633905107873427311804485 58993857207726267620963341)
                  ·
                    refine ⟨22122696452897350357861253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58993857207726267620963341 22122696452897350357861253)
                    ·
                      refine ⟨4148005584918253192098985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22122696452897350357861253 4148005584918253192098985)
                      ·
                        rfl

theorem cell23_8078212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_8078212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078212 prefixEnd_8078212 := by exact prefixLift 8078212
  have htrace : WordTrace (prefixWord ++ tailWord_8078212) baseStart_8078212 baseEnd_8078212 := by
    simpa [prefixWord, tailWord_8078212, baseEnd_8078212] using wordTrace_append hprefix tailTrace_8078212
  have hstable : (prefixWord ++ tailWord_8078212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078212).length < 2 ^ (prefixWord ++ tailWord_8078212).sum := by decide
  have hdescent : baseEnd_8078212 < baseStart_8078212 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078216 : List Nat := [2, 1, 3, 3, 2, 1, 2, 1, 3, 3, 2]
def baseStart_8078216 : Nat := 118140960795 + 8078216 * 2 ^ 59
def prefixEnd_8078216 : Nat := 4983230072969 + 3 ^ 40 * 8078216 * 2
def baseEnd_8078216 : Nat := 4148007638840871176448967

theorem tailTrace_8078216 : CollatzResearch.WordTrace tailWord_8078216 prefixEnd_8078216 4148007638840871176448967 := by
  unfold tailWord_8078216
  simp only [CollatzResearch.WordTrace]
  refine ⟨147318371451005278149203251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196424495268007037532271001 147318371451005278149203251)
  ·
    refine ⟨220977557176507917223804877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147318371451005278149203251 220977557176507917223804877)
    ·
      refine ⟨82866583941190468958926829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220977557176507917223804877 82866583941190468958926829)
      ·
        refine ⟨31074968977946425859597561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82866583941190468958926829 31074968977946425859597561)
        ·
          refine ⟨23306226733459819394698171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31074968977946425859597561 23306226733459819394698171)
          ·
            refine ⟨34959340100189729092047257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23306226733459819394698171 34959340100189729092047257)
            ·
              refine ⟨26219505075142296819035443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34959340100189729092047257 26219505075142296819035443)
              ·
                refine ⟨39329257612713445228553165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26219505075142296819035443 39329257612713445228553165)
                ·
                  refine ⟨14748471604767541960707437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39329257612713445228553165 14748471604767541960707437)
                  ·
                    refine ⟨5530676851787828235265289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14748471604767541960707437 5530676851787828235265289)
                    ·
                      refine ⟨4148007638840871176448967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5530676851787828235265289 4148007638840871176448967)
                      ·
                        rfl

theorem cell23_8078216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_8078216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078216 prefixEnd_8078216 := by exact prefixLift 8078216
  have htrace : WordTrace (prefixWord ++ tailWord_8078216) baseStart_8078216 baseEnd_8078216 := by
    simpa [prefixWord, tailWord_8078216, baseEnd_8078216] using wordTrace_append hprefix tailTrace_8078216
  have hstable : (prefixWord ++ tailWord_8078216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078216).length < 2 ^ (prefixWord ++ tailWord_8078216).sum := by decide
  have hdescent : baseEnd_8078216 < baseStart_8078216 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078286 : List Nat := [4, 1, 1, 1, 2, 3, 3, 3, 5]
def baseStart_8078286 : Nat := 118140960795 + 8078286 * 2 ^ 59
def prefixEnd_8078286 : Nat := 4983230072969 + 3 ^ 40 * 8078286 * 2
def baseEnd_8078286 : Nat := 460893731387409544730405

theorem tailTrace_8078286 : CollatzResearch.WordTrace tailWord_8078286 prefixEnd_8078286 460893731387409544730405 := by
  unfold tailWord_8078286
  simp only [CollatzResearch.WordTrace]
  refine ⟨36829912001469619781681839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196426197341171305502303141 36829912001469619781681839)
  ·
    refine ⟨55244868002204429672522759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36829912001469619781681839 55244868002204429672522759)
    ·
      refine ⟨82867302003306644508784139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55244868002204429672522759 82867302003306644508784139)
      ·
        refine ⟨124300953004959966763176209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82867302003306644508784139 124300953004959966763176209)
        ·
          refine ⟨93225714753719975072382157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124300953004959966763176209 93225714753719975072382157)
          ·
            refine ⟨34959643032644990652143309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93225714753719975072382157 34959643032644990652143309)
            ·
              refine ⟨13109866137241871494553741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34959643032644990652143309 13109866137241871494553741)
              ·
                refine ⟨4916199801465701810457653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13109866137241871494553741 4916199801465701810457653)
                ·
                  refine ⟨460893731387409544730405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916199801465701810457653 460893731387409544730405)
                  ·
                    rfl

theorem cell23_8078286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 3, 3, 5].length) (baseStart_8078286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078286 prefixEnd_8078286 := by exact prefixLift 8078286
  have htrace : WordTrace (prefixWord ++ tailWord_8078286) baseStart_8078286 baseEnd_8078286 := by
    simpa [prefixWord, tailWord_8078286, baseEnd_8078286] using wordTrace_append hprefix tailTrace_8078286
  have hstable : (prefixWord ++ tailWord_8078286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078286).length < 2 ^ (prefixWord ++ tailWord_8078286).sum := by decide
  have hdescent : baseEnd_8078286 < baseStart_8078286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078303 : List Nat := [1, 1, 2, 3, 5, 1, 3, 2, 5]
def baseStart_8078303 : Nat := 118140960795 + 8078303 * 2 ^ 59
def prefixEnd_8078303 : Nat := 4983230072969 + 3 ^ 40 * 8078303 * 2
def baseEnd_8078303 : Nat := 460894701295312481784563

theorem tailTrace_8078303 : CollatzResearch.WordTrace tailWord_8078303 prefixEnd_8078303 460894701295312481784563 := by
  unfold tailWord_8078303
  simp only [CollatzResearch.WordTrace]
  refine ⟨294639916052695370156823563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196426610701796913437882375 294639916052695370156823563)
  ·
    refine ⟨441959874079043055235235345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294639916052695370156823563 441959874079043055235235345)
    ·
      refine ⟨331469905559282291426426509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441959874079043055235235345 331469905559282291426426509)
      ·
        refine ⟨124301214584730859284909941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331469905559282291426426509 124301214584730859284909941)
        ·
          refine ⟨11653238867318518057960307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124301214584730859284909941 11653238867318518057960307)
          ·
            refine ⟨17479858300977777086940461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11653238867318518057960307 17479858300977777086940461)
            ·
              refine ⟨6554946862866666407602673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17479858300977777086940461 6554946862866666407602673)
              ·
                refine ⟨4916210147149999805702005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554946862866666407602673 4916210147149999805702005)
                ·
                  refine ⟨460894701295312481784563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916210147149999805702005 460894701295312481784563)
                  ·
                    rfl

theorem cell23_8078303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 3, 2, 5].length) (baseStart_8078303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078303 prefixEnd_8078303 := by exact prefixLift 8078303
  have htrace : WordTrace (prefixWord ++ tailWord_8078303) baseStart_8078303 baseEnd_8078303 := by
    simpa [prefixWord, tailWord_8078303, baseEnd_8078303] using wordTrace_append hprefix tailTrace_8078303
  have hstable : (prefixWord ++ tailWord_8078303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078303).length < 2 ^ (prefixWord ++ tailWord_8078303).sum := by decide
  have hdescent : baseEnd_8078303 < baseStart_8078303 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078329 : List Nat := [1, 2, 1, 3, 1, 3, 2, 1, 5, 4]
def baseStart_8078329 : Nat := 118140960795 + 8078329 * 2 ^ 59
def prefixEnd_8078329 : Nat := 4983230072969 + 3 ^ 40 * 8078329 * 2
def baseEnd_8078329 : Nat := 1382688554051609744778649

theorem tailTrace_8078329 : CollatzResearch.WordTrace tailWord_8078329 prefixEnd_8078329 1382688554051609744778649 := by
  unfold tailWord_8078329
  simp only [CollatzResearch.WordTrace]
  refine ⟨294640864350601176597270041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196427242900400784398180027 294640864350601176597270041)
  ·
    refine ⟨220980648262950882447952531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294640864350601176597270041 220980648262950882447952531)
    ·
      refine ⟨331470972394426323671928797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220980648262950882447952531 331470972394426323671928797)
      ·
        refine ⟨124301614647909871376973299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331470972394426323671928797 124301614647909871376973299)
        ·
          refine ⟨186452421971864807065459949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124301614647909871376973299 186452421971864807065459949)
          ·
            refine ⟨69919658239449302649547481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186452421971864807065459949 69919658239449302649547481)
            ·
              refine ⟨52439743679586976987160611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69919658239449302649547481 52439743679586976987160611)
              ·
                refine ⟨78659615519380465480740917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52439743679586976987160611 78659615519380465480740917)
                ·
                  refine ⟨7374338954941918638819461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78659615519380465480740917 7374338954941918638819461)
                  ·
                    refine ⟨1382688554051609744778649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7374338954941918638819461 1382688554051609744778649)
                    ·
                      rfl

theorem cell23_8078329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 1, 5, 4].length) (baseStart_8078329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078329 prefixEnd_8078329 := by exact prefixLift 8078329
  have htrace : WordTrace (prefixWord ++ tailWord_8078329) baseStart_8078329 baseEnd_8078329 := by
    simpa [prefixWord, tailWord_8078329, baseEnd_8078329] using wordTrace_append hprefix tailTrace_8078329
  have hstable : (prefixWord ++ tailWord_8078329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078329).length < 2 ^ (prefixWord ++ tailWord_8078329).sum := by decide
  have hdescent : baseEnd_8078329 < baseStart_8078329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078354 : List Nat := [3, 2, 5, 1, 1, 2, 2, 2, 5]
def baseStart_8078354 : Nat := 118140960795 + 8078354 * 2 ^ 59
def prefixEnd_8078354 : Nat := 4983230072969 + 3 ^ 40 * 8078354 * 2
def baseEnd_8078354 : Nat := 460897611019021292947037

theorem tailTrace_8078354 : CollatzResearch.WordTrace tailWord_8078354 prefixEnd_8078354 460897611019021292947037 := by
  unfold tailWord_8078354
  simp only [CollatzResearch.WordTrace]
  refine ⟨73660444043877651466732529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196427850783673737244620077 73660444043877651466732529)
  ·
    refine ⟨55245333032908238600049397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73660444043877651466732529 55245333032908238600049397)
    ·
      refine ⟨5179249971835147368754631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55245333032908238600049397 5179249971835147368754631)
      ·
        refine ⟨7768874957752721053131947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5179249971835147368754631 7768874957752721053131947)
        ·
          refine ⟨11653312436629081579697921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768874957752721053131947 11653312436629081579697921)
          ·
            refine ⟨8739984327471811184773441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11653312436629081579697921 8739984327471811184773441)
            ·
              refine ⟨6554988245603858388580081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8739984327471811184773441 6554988245603858388580081)
              ·
                refine ⟨4916241184202893791435061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6554988245603858388580081 4916241184202893791435061)
                ·
                  refine ⟨460897611019021292947037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916241184202893791435061 460897611019021292947037)
                  ·
                    rfl

theorem cell23_8078354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_8078354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078354 prefixEnd_8078354 := by exact prefixLift 8078354
  have htrace : WordTrace (prefixWord ++ tailWord_8078354) baseStart_8078354 baseEnd_8078354 := by
    simpa [prefixWord, tailWord_8078354, baseEnd_8078354] using wordTrace_append hprefix tailTrace_8078354
  have hstable : (prefixWord ++ tailWord_8078354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078354).length < 2 ^ (prefixWord ++ tailWord_8078354).sum := by decide
  have hdescent : baseEnd_8078354 < baseStart_8078354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078390 : List Nat := [5, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_8078390 : Nat := 118140960795 + 8078390 * 2 ^ 59
def prefixEnd_8078390 : Nat := 4983230072969 + 3 ^ 40 * 8078390 * 2
def baseEnd_8078390 : Nat := 4148096984474753495673167

theorem tailTrace_8078390 : CollatzResearch.WordTrace tailWord_8078390 prefixEnd_8078390 4148096984474753495673167 := by
  unfold tailWord_8078390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18415193075211261500952539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196428726135586789343493749 18415193075211261500952539)
  ·
    refine ⟨27622789612816892251428809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18415193075211261500952539 27622789612816892251428809)
    ·
      refine ⟨20717092209612669188571607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27622789612816892251428809 20717092209612669188571607)
      ·
        refine ⟨31075638314419003782857411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20717092209612669188571607 31075638314419003782857411)
        ·
          refine ⟨46613457471628505674286117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31075638314419003782857411 46613457471628505674286117)
          ·
            refine ⟨8740023275930344813928647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46613457471628505674286117 8740023275930344813928647)
            ·
              refine ⟨13110034913895517220892971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740023275930344813928647 13110034913895517220892971)
              ·
                refine ⟨19665052370843275831339457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13110034913895517220892971 19665052370843275831339457)
                ·
                  refine ⟨14748789278132456873504593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19665052370843275831339457 14748789278132456873504593)
                  ·
                    refine ⟨11061591958599342655128445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14748789278132456873504593 11061591958599342655128445)
                    ·
                      refine ⟨4148096984474753495673167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11061591958599342655128445 4148096984474753495673167)
                      ·
                        rfl

theorem cell23_8078390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_8078390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078390 prefixEnd_8078390 := by exact prefixLift 8078390
  have htrace : WordTrace (prefixWord ++ tailWord_8078390) baseStart_8078390 baseEnd_8078390 := by
    simpa [prefixWord, tailWord_8078390, baseEnd_8078390] using wordTrace_append hprefix tailTrace_8078390
  have hstable : (prefixWord ++ tailWord_8078390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078390).length < 2 ^ (prefixWord ++ tailWord_8078390).sum := by decide
  have hdescent : baseEnd_8078390 < baseStart_8078390 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078409 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 4]
def baseStart_8078409 : Nat := 118140960795 + 8078409 * 2 ^ 59
def prefixEnd_8078409 : Nat := 4983230072969 + 3 ^ 40 * 8078409 * 2
def baseEnd_8078409 : Nat := 4148106740607188921335579

theorem tailTrace_8078409 : CollatzResearch.WordTrace tailWord_8078409 prefixEnd_8078409 4148106740607188921335579 := by
  unfold tailWord_8078409
  simp only [CollatzResearch.WordTrace]
  refine ⟨294643782190311350260182281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196429188126874233506788187 294643782190311350260182281)
  ·
    refine ⟨220982836642733512695136711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294643782190311350260182281 220982836642733512695136711)
    ·
      refine ⟨331474254964100269042705067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220982836642733512695136711 331474254964100269042705067)
      ·
        refine ⟨497211382446150403564057601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 331474254964100269042705067 497211382446150403564057601)
        ·
          refine ⟨372908536834612802673043201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 497211382446150403564057601 372908536834612802673043201)
          ·
            refine ⟨279681402625959602004782401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372908536834612802673043201 279681402625959602004782401)
            ·
              refine ⟨209761051969469701503586801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279681402625959602004782401 209761051969469701503586801)
              ·
                refine ⟨157320788977102276127690101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209761051969469701503586801 157320788977102276127690101)
                ·
                  refine ⟨14748823966603338386970947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157320788977102276127690101 14748823966603338386970947)
                  ·
                    refine ⟨22123235949905007580456421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14748823966603338386970947 22123235949905007580456421)
                    ·
                      refine ⟨4148106740607188921335579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22123235949905007580456421 4148106740607188921335579)
                      ·
                        rfl

theorem cell23_8078409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_8078409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078409 prefixEnd_8078409 := by exact prefixLift 8078409
  have htrace : WordTrace (prefixWord ++ tailWord_8078409) baseStart_8078409 baseEnd_8078409 := by
    simpa [prefixWord, tailWord_8078409, baseEnd_8078409] using wordTrace_append hprefix tailTrace_8078409
  have hstable : (prefixWord ++ tailWord_8078409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078409).length < 2 ^ (prefixWord ++ tailWord_8078409).sum := by decide
  have hdescent : baseEnd_8078409 < baseStart_8078409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078420 : List Nat := [2, 4, 1, 1, 1, 1, 4, 4, 1, 1, 3]
def baseStart_8078420 : Nat := 118140960795 + 8078420 * 2 ^ 59
def prefixEnd_8078420 : Nat := 4983230072969 + 3 ^ 40 * 8078420 * 2
def baseEnd_8078420 : Nat := 4148112388894388378298029

theorem tailTrace_8078420 : CollatzResearch.WordTrace tailWord_8078420 prefixEnd_8078420 4148112388894388378298029 := by
  unfold tailWord_8078420
  simp only [CollatzResearch.WordTrace]
  refine ⟨147322091696635749569416357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196429455595514332759221809 147322091696635749569416357)
  ·
    refine ⟨27622892193119203044265567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147322091696635749569416357 27622892193119203044265567)
    ·
      refine ⟨41434338289678804566398351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27622892193119203044265567 41434338289678804566398351)
      ·
        refine ⟨62151507434518206849597527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41434338289678804566398351 62151507434518206849597527)
        ·
          refine ⟨93227261151777310274396291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62151507434518206849597527 93227261151777310274396291)
          ·
            refine ⟨139840891727665965411594437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93227261151777310274396291 139840891727665965411594437)
            ·
              refine ⟨26220167198937368514673957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139840891727665965411594437 26220167198937368514673957)
              ·
                refine ⟨4916281349800756596501367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26220167198937368514673957 4916281349800756596501367)
                ·
                  refine ⟨7374422024701134894752051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4916281349800756596501367 7374422024701134894752051)
                  ·
                    refine ⟨11061633037051702342128077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7374422024701134894752051 11061633037051702342128077)
                    ·
                      refine ⟨4148112388894388378298029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11061633037051702342128077 4148112388894388378298029)
                      ·
                        rfl

theorem cell23_8078420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_8078420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078420 prefixEnd_8078420 := by exact prefixLift 8078420
  have htrace : WordTrace (prefixWord ++ tailWord_8078420) baseStart_8078420 baseEnd_8078420 := by
    simpa [prefixWord, tailWord_8078420, baseEnd_8078420] using wordTrace_append hprefix tailTrace_8078420
  have hstable : (prefixWord ++ tailWord_8078420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078420).length < 2 ^ (prefixWord ++ tailWord_8078420).sum := by decide
  have hdescent : baseEnd_8078420 < baseStart_8078420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078440 : List Nat := [2, 1, 4, 4, 1, 1, 2, 2, 1, 5]
def baseStart_8078440 : Nat := 118140960795 + 8078440 * 2 ^ 59
def prefixEnd_8078440 : Nat := 4983230072969 + 3 ^ 40 * 8078440 * 2
def baseEnd_8078440 : Nat := 1382707552835826100015979

theorem tailTrace_8078440 : CollatzResearch.WordTrace tailWord_8078440 prefixEnd_8078440 1382707552835826100015979 := by
  unfold tailWord_8078440
  simp only [CollatzResearch.WordTrace]
  refine ⟨147322456426599521277280387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196429941902132695036373849 147322456426599521277280387)
  ·
    refine ⟨220983684639899281915920581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147322456426599521277280387 220983684639899281915920581)
    ·
      refine ⟨41434440869981115359235109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220983684639899281915920581 41434440869981115359235109)
      ·
        refine ⟨7768957663121459129856583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41434440869981115359235109 7768957663121459129856583)
        ·
          refine ⟨11653436494682188694784875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7768957663121459129856583 11653436494682188694784875)
          ·
            refine ⟨17480154742023283042177313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11653436494682188694784875 17480154742023283042177313)
            ·
              refine ⟨13110116056517462281632985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17480154742023283042177313 13110116056517462281632985)
              ·
                refine ⟨9832587042388096711224739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13110116056517462281632985 9832587042388096711224739)
                ·
                  refine ⟨14748880563582145066837109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9832587042388096711224739 14748880563582145066837109)
                  ·
                    refine ⟨1382707552835826100015979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14748880563582145066837109 1382707552835826100015979)
                    ·
                      rfl

theorem cell23_8078440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_8078440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078440 prefixEnd_8078440 := by exact prefixLift 8078440
  have htrace : WordTrace (prefixWord ++ tailWord_8078440) baseStart_8078440 baseEnd_8078440 := by
    simpa [prefixWord, tailWord_8078440, baseEnd_8078440] using wordTrace_append hprefix tailTrace_8078440
  have hstable : (prefixWord ++ tailWord_8078440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078440).length < 2 ^ (prefixWord ++ tailWord_8078440).sum := by decide
  have hdescent : baseEnd_8078440 < baseStart_8078440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078534 : List Nat := [6, 1, 2, 2, 2, 1, 1, 8]
def baseStart_8078534 : Nat := 118140960795 + 8078534 * 2 ^ 59
def prefixEnd_8078534 : Nat := 4983230072969 + 3 ^ 40 * 8078534 * 2
def baseEnd_8078534 : Nat := 153635960210703738232315

theorem tailTrace_8078534 : CollatzResearch.WordTrace tailWord_8078534 prefixEnd_8078534 153635960210703738232315 := by
  unfold tailWord_8078534
  simp only [CollatzResearch.WordTrace]
  refine ⟨9207760666089328019015083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196432227543238997738988437 9207760666089328019015083)
  ·
    refine ⟨13811640999133992028522625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9207760666089328019015083 13811640999133992028522625)
    ·
      refine ⟨10358730749350494021391969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13811640999133992028522625 10358730749350494021391969)
      ·
        refine ⟨7769048062012870516043977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10358730749350494021391969 7769048062012870516043977)
        ·
          refine ⟨5826786046509652887032983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7769048062012870516043977 5826786046509652887032983)
          ·
            refine ⟨8740179069764479330549475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5826786046509652887032983 8740179069764479330549475)
            ·
              refine ⟨13110268604646718995824213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8740179069764479330549475 13110268604646718995824213)
              ·
                refine ⟨153635960210703738232315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13110268604646718995824213 153635960210703738232315)
                ·
                  rfl

theorem cell23_8078534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 1, 1, 8].length) (baseStart_8078534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078534 prefixEnd_8078534 := by exact prefixLift 8078534
  have htrace : WordTrace (prefixWord ++ tailWord_8078534) baseStart_8078534 baseEnd_8078534 := by
    simpa [prefixWord, tailWord_8078534, baseEnd_8078534] using wordTrace_append hprefix tailTrace_8078534
  have hstable : (prefixWord ++ tailWord_8078534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078534).length < 2 ^ (prefixWord ++ tailWord_8078534).sum := by decide
  have hdescent : baseEnd_8078534 < baseStart_8078534 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078536 : List Nat := [2, 1, 3, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_8078536 : Nat := 118140960795 + 8078536 * 2 ^ 59
def prefixEnd_8078536 : Nat := 4983230072969 + 3 ^ 40 * 8078536 * 2
def baseEnd_8078536 : Nat := 4148171952650309924447495

theorem tailTrace_8078536 : CollatzResearch.WordTrace tailWord_8078536 prefixEnd_8078536 4148171952650309924447495 := by
  unfold tailWord_8078536
  simp only [CollatzResearch.WordTrace]
  refine ⟨147324207130425625475027731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196432276173900833966703641 147324207130425625475027731)
  ·
    refine ⟨220986310695638438212541597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147324207130425625475027731 220986310695638438212541597)
    ·
      refine ⟨82869866510864414329703099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220986310695638438212541597 82869866510864414329703099)
      ·
        refine ⟨124304799766296621494554649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82869866510864414329703099 124304799766296621494554649)
        ·
          refine ⟨93228599824722466120915987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124304799766296621494554649 93228599824722466120915987)
          ·
            refine ⟨139842899737083699181373981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93228599824722466120915987 139842899737083699181373981)
            ·
              refine ⟨52441087401406387193015243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139842899737083699181373981 52441087401406387193015243)
              ·
                refine ⟨78661631102109580789522865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52441087401406387193015243 78661631102109580789522865)
                ·
                  refine ⟨58996223326582185592142149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78661631102109580789522865 58996223326582185592142149)
                  ·
                    refine ⟨11061791873734159798526653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58996223326582185592142149 11061791873734159798526653)
                    ·
                      refine ⟨4148171952650309924447495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11061791873734159798526653 4148171952650309924447495)
                      ·
                        rfl

theorem cell23_8078536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_8078536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078536 prefixEnd_8078536 := by exact prefixLift 8078536
  have htrace : WordTrace (prefixWord ++ tailWord_8078536) baseStart_8078536 baseEnd_8078536 := by
    simpa [prefixWord, tailWord_8078536, baseEnd_8078536] using wordTrace_append hprefix tailTrace_8078536
  have hstable : (prefixWord ++ tailWord_8078536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078536).length < 2 ^ (prefixWord ++ tailWord_8078536).sum := by decide
  have hdescent : baseEnd_8078536 < baseStart_8078536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078586 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 4, 5]
def baseStart_8078586 : Nat := 118140960795 + 8078586 * 2 ^ 59
def prefixEnd_8078586 : Nat := 4983230072969 + 3 ^ 40 * 8078586 * 2
def baseEnd_8078586 : Nat := 1382732542227678242940755

theorem tailTrace_8078586 : CollatzResearch.WordTrace tailWord_8078586 prefixEnd_8078586 1382732542227678242940755 := by
  unfold tailWord_8078586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73662559477667527372343903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196433491940446739659583741 73662559477667527372343903)
  ·
    refine ⟨110493839216501291058515855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73662559477667527372343903 110493839216501291058515855)
    ·
      refine ⟨165740758824751936587773783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110493839216501291058515855 165740758824751936587773783)
      ·
        refine ⟨248611138237127904881660675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165740758824751936587773783 248611138237127904881660675)
        ·
          refine ⟨372916707355691857322491013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248611138237127904881660675 372916707355691857322491013)
          ·
            refine ⟨69921882629192223247967065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372916707355691857322491013 69921882629192223247967065)
            ·
              refine ⟨52441411971894167435975299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69921882629192223247967065 52441411971894167435975299)
              ·
                refine ⟨78662117957841251153962949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52441411971894167435975299 78662117957841251153962949)
                ·
                  refine ⟨14749147117095234591368053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78662117957841251153962949 14749147117095234591368053)
                  ·
                    refine ⟨1382732542227678242940755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14749147117095234591368053 1382732542227678242940755)
                    ·
                      rfl

theorem cell23_8078586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 4, 5].length) (baseStart_8078586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078586 prefixEnd_8078586 := by exact prefixLift 8078586
  have htrace : WordTrace (prefixWord ++ tailWord_8078586) baseStart_8078586 baseEnd_8078586 := by
    simpa [prefixWord, tailWord_8078586, baseEnd_8078586] using wordTrace_append hprefix tailTrace_8078586
  have hstable : (prefixWord ++ tailWord_8078586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078586).length < 2 ^ (prefixWord ++ tailWord_8078586).sum := by decide
  have hdescent : baseEnd_8078586 < baseStart_8078586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078590 : List Nat := [4, 2, 2, 1, 1, 2, 2, 4, 5]
def baseStart_8078590 : Nat := 118140960795 + 8078590 * 2 ^ 59
def prefixEnd_8078590 : Nat := 4983230072969 + 3 ^ 40 * 8078590 * 2
def baseEnd_8078590 : Nat := 460911075622850301463583

theorem tailTrace_8078590 : CollatzResearch.WordTrace tailWord_8078590 prefixEnd_8078590 460911075622850301463583 := by
  unfold tailWord_8078590
  simp only [CollatzResearch.WordTrace]
  refine ⟨36831297975331952271565153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196433589201770412115014149 36831297975331952271565153)
  ·
    refine ⟨27623473481498964203673865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36831297975331952271565153 27623473481498964203673865)
    ·
      refine ⟨20717605111124223152755399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27623473481498964203673865 20717605111124223152755399)
      ·
        refine ⟨31076407666686334729133099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20717605111124223152755399 31076407666686334729133099)
        ·
          refine ⟨46614611500029502093699649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31076407666686334729133099 46614611500029502093699649)
          ·
            refine ⟨34960958625022126570274737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46614611500029502093699649 34960958625022126570274737)
            ·
              refine ⟨26220718968766594927706053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34960958625022126570274737 26220718968766594927706053)
              ·
                refine ⟨4916384806643736548944885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26220718968766594927706053 4916384806643736548944885)
                ·
                  refine ⟨460911075622850301463583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4916384806643736548944885 460911075622850301463583)
                  ·
                    rfl

theorem cell23_8078590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 2, 4, 5].length) (baseStart_8078590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078590 prefixEnd_8078590 := by exact prefixLift 8078590
  have htrace : WordTrace (prefixWord ++ tailWord_8078590) baseStart_8078590 baseEnd_8078590 := by
    simpa [prefixWord, tailWord_8078590, baseEnd_8078590] using wordTrace_append hprefix tailTrace_8078590
  have hstable : (prefixWord ++ tailWord_8078590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078590).length < 2 ^ (prefixWord ++ tailWord_8078590).sum := by decide
  have hdescent : baseEnd_8078590 < baseStart_8078590 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078643 : List Nat := [1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 3]
def baseStart_8078643 : Nat := 118140960795 + 8078643 * 2 ^ 59
def prefixEnd_8078643 : Nat := 4983230072969 + 3 ^ 40 * 8078643 * 2
def baseEnd_8078643 : Nat := 4148226895080341005809503

theorem tailTrace_8078643 : CollatzResearch.WordTrace tailWord_8078643 prefixEnd_8078643 4148226895080341005809503 := by
  unfold tailWord_8078643
  simp only [CollatzResearch.WordTrace]
  refine ⟨294652316871463608224200583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196434877914309072149467055 294652316871463608224200583)
  ·
    refine ⟨441978475307195412336300875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294652316871463608224200583 441978475307195412336300875)
    ·
      refine ⟨662967712960793118504451313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441978475307195412336300875 662967712960793118504451313)
      ·
        refine ⟨497225784720594838878338485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 662967712960793118504451313 497225784720594838878338485)
        ·
          refine ⟨46614917317555766144844233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 497225784720594838878338485 46614917317555766144844233)
          ·
            refine ⟨34961187988166824608633175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46614917317555766144844233 34961187988166824608633175)
            ·
              refine ⟨52441781982250236912949763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34961187988166824608633175 52441781982250236912949763)
              ·
                refine ⟨78662672973375355369424645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52441781982250236912949763 78662672973375355369424645)
                ·
                  refine ⟨14749251182507879131767121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78662672973375355369424645 14749251182507879131767121)
                  ·
                    refine ⟨11061938386880909348825341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14749251182507879131767121 11061938386880909348825341)
                    ·
                      refine ⟨4148226895080341005809503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11061938386880909348825341 4148226895080341005809503)
                      ·
                        rfl

theorem cell23_8078643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_8078643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078643 prefixEnd_8078643 := by exact prefixLift 8078643
  have htrace : WordTrace (prefixWord ++ tailWord_8078643) baseStart_8078643 baseEnd_8078643 := by
    simpa [prefixWord, tailWord_8078643, baseEnd_8078643] using wordTrace_append hprefix tailTrace_8078643
  have hstable : (prefixWord ++ tailWord_8078643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078643).length < 2 ^ (prefixWord ++ tailWord_8078643).sum := by decide
  have hdescent : baseEnd_8078643 < baseStart_8078643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078663 : List Nat := [1, 1, 4, 1, 2, 4, 1, 3, 6]
def baseStart_8078663 : Nat := 118140960795 + 8078663 * 2 ^ 59
def prefixEnd_8078663 : Nat := 4983230072969 + 3 ^ 40 * 8078663 * 2
def baseEnd_8078663 : Nat := 460915240521492325284379

theorem tailTrace_8078663 : CollatzResearch.WordTrace tailWord_8078663 prefixEnd_8078663 460915240521492325284379 := by
  unfold tailWord_8078663
  simp only [CollatzResearch.WordTrace]
  refine ⟨294653046331391151639928643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196435364220927434426619095 294653046331391151639928643)
  ·
    refine ⟨441979569497086727459892965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294653046331391151639928643 441979569497086727459892965)
    ·
      refine ⟨82871169280703761398729931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441979569497086727459892965 82871169280703761398729931)
      ·
        refine ⟨124306753921055642098094897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82871169280703761398729931 124306753921055642098094897)
        ·
          refine ⟨93230065440791731573571173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124306753921055642098094897 93230065440791731573571173)
          ·
            refine ⟨17480637270148449670044595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93230065440791731573571173 17480637270148449670044595)
            ·
              refine ⟨26220955905222674505066893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17480637270148449670044595 26220955905222674505066893)
              ·
                refine ⟨9832858464458502939400085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26220955905222674505066893 9832858464458502939400085)
                ·
                  refine ⟨460915240521492325284379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9832858464458502939400085 460915240521492325284379)
                  ·
                    rfl

theorem cell23_8078663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 3, 6].length) (baseStart_8078663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078663 prefixEnd_8078663 := by exact prefixLift 8078663
  have htrace : WordTrace (prefixWord ++ tailWord_8078663) baseStart_8078663 baseEnd_8078663 := by
    simpa [prefixWord, tailWord_8078663, baseEnd_8078663] using wordTrace_append hprefix tailTrace_8078663
  have hstable : (prefixWord ++ tailWord_8078663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078663).length < 2 ^ (prefixWord ++ tailWord_8078663).sum := by decide
  have hdescent : baseEnd_8078663 < baseStart_8078663 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078666 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6]
def baseStart_8078666 : Nat := 118140960795 + 8078666 * 2 ^ 59
def prefixEnd_8078666 : Nat := 4983230072969 + 3 ^ 40 * 8078666 * 2
def baseEnd_8078666 : Nat := 4148238705135394415821897

theorem tailTrace_8078666 : CollatzResearch.WordTrace tailWord_8078666 prefixEnd_8078666 4148238705135394415821897 := by
  unfold tailWord_8078666
  simp only [CollatzResearch.WordTrace]
  refine ⟨73663288937595070788071963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196435437166920188768191901 73663288937595070788071963)
  ·
    refine ⟨110494933406392606182107945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73663288937595070788071963 110494933406392606182107945)
    ·
      refine ⟨82871200054794454636580959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110494933406392606182107945 82871200054794454636580959)
      ·
        refine ⟨124306800082191681954871439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82871200054794454636580959 124306800082191681954871439)
        ·
          refine ⟨186460200123287522932307159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124306800082191681954871439 186460200123287522932307159)
          ·
            refine ⟨279690300184931284398460739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186460200123287522932307159 279690300184931284398460739)
            ·
              refine ⟨419535450277396926597691109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279690300184931284398460739 419535450277396926597691109)
              ·
                refine ⟨78662896927011923737067083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 419535450277396926597691109 78662896927011923737067083)
                ·
                  refine ⟨117994345390517885605600625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78662896927011923737067083 117994345390517885605600625)
                  ·
                    refine ⟨88495759042888414204200469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117994345390517885605600625 88495759042888414204200469)
                    ·
                      refine ⟨4148238705135394415821897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88495759042888414204200469 4148238705135394415821897)
                      ·
                        rfl

theorem cell23_8078666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 2, 6].length) (baseStart_8078666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078666 prefixEnd_8078666 := by exact prefixLift 8078666
  have htrace : WordTrace (prefixWord ++ tailWord_8078666) baseStart_8078666 baseEnd_8078666 := by
    simpa [prefixWord, tailWord_8078666, baseEnd_8078666] using wordTrace_append hprefix tailTrace_8078666
  have hstable : (prefixWord ++ tailWord_8078666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078666).length < 2 ^ (prefixWord ++ tailWord_8078666).sum := by decide
  have hdescent : baseEnd_8078666 < baseStart_8078666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078713 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 4]
def baseStart_8078713 : Nat := 118140960795 + 8078713 * 2 ^ 59
def prefixEnd_8078713 : Nat := 4983230072969 + 3 ^ 40 * 8078713 * 2
def baseEnd_8078713 : Nat := 4148262838726155731934181

theorem tailTrace_8078713 : CollatzResearch.WordTrace tailWord_8078713 prefixEnd_8078713 4148262838726155731934181 := by
  unfold tailWord_8078713
  simp only [CollatzResearch.WordTrace]
  refine ⟨294654869981210010179248793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196436579987473340119499195 294654869981210010179248793)
  ·
    refine ⟨220991152485907507634436595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294654869981210010179248793 220991152485907507634436595)
    ·
      refine ⟨331486728728861261451654893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220991152485907507634436595 331486728728861261451654893)
      ·
        refine ⟨124307523273322973044370585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 331486728728861261451654893 124307523273322973044370585)
        ·
          refine ⟨93230642454992229783277939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124307523273322973044370585 93230642454992229783277939)
          ·
            refine ⟨139845963682488344674916909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93230642454992229783277939 139845963682488344674916909)
            ·
              refine ⟨52442236380933129253093841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139845963682488344674916909 52442236380933129253093841)
              ·
                refine ⟨39331677285699846939820381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52442236380933129253093841 39331677285699846939820381)
                ·
                  refine ⟨14749378982137442602432643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39331677285699846939820381 14749378982137442602432643)
                  ·
                    refine ⟨22124068473206163903648965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14749378982137442602432643 22124068473206163903648965)
                    ·
                      refine ⟨4148262838726155731934181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22124068473206163903648965 4148262838726155731934181)
                      ·
                        rfl

theorem cell23_8078713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_8078713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078713 prefixEnd_8078713 := by exact prefixLift 8078713
  have htrace : WordTrace (prefixWord ++ tailWord_8078713) baseStart_8078713 baseEnd_8078713 := by
    simpa [prefixWord, tailWord_8078713, baseEnd_8078713] using wordTrace_append hprefix tailTrace_8078713
  have hstable : (prefixWord ++ tailWord_8078713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078713).length < 2 ^ (prefixWord ++ tailWord_8078713).sum := by decide
  have hdescent : baseEnd_8078713 < baseStart_8078713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078723 : List Nat := [1, 1, 1, 3, 5, 1, 1, 3, 1, 6]
def baseStart_8078723 : Nat := 118140960795 + 8078723 * 2 ^ 59
def prefixEnd_8078723 : Nat := 4983230072969 + 3 ^ 40 * 8078723 * 2
def baseEnd_8078723 : Nat := 1382755991177566897603045

theorem tailTrace_8078723 : CollatzResearch.WordTrace tailWord_8078723 prefixEnd_8078723 1382755991177566897603045 := by
  unfold tailWord_8078723
  simp only [CollatzResearch.WordTrace]
  refine ⟨294655234711173781887112823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196436823140782521258075215 294655234711173781887112823)
  ·
    refine ⟨441982852066760672830669235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294655234711173781887112823 441982852066760672830669235)
    ·
      refine ⟨662974278100141009246003853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441982852066760672830669235 662974278100141009246003853)
      ·
        refine ⟨248615354287552878467251445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 662974278100141009246003853 248615354287552878467251445)
        ·
          refine ⟨23307689464458082356304823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248615354287552878467251445 23307689464458082356304823)
          ·
            refine ⟨34961534196687123534457235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23307689464458082356304823 34961534196687123534457235)
            ·
              refine ⟨52442301295030685301685853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34961534196687123534457235 52442301295030685301685853)
              ·
                refine ⟨19665862985636506988132195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52442301295030685301685853 19665862985636506988132195)
                ·
                  refine ⟨29498794478454760482198293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19665862985636506988132195 29498794478454760482198293)
                  ·
                    refine ⟨1382755991177566897603045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29498794478454760482198293 1382755991177566897603045)
                    ·
                      rfl

theorem cell23_8078723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3, 1, 6].length) (baseStart_8078723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078723 prefixEnd_8078723 := by exact prefixLift 8078723
  have htrace : WordTrace (prefixWord ++ tailWord_8078723) baseStart_8078723 baseEnd_8078723 := by
    simpa [prefixWord, tailWord_8078723, baseEnd_8078723] using wordTrace_append hprefix tailTrace_8078723
  have hstable : (prefixWord ++ tailWord_8078723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078723).length < 2 ^ (prefixWord ++ tailWord_8078723).sum := by decide
  have hdescent : baseEnd_8078723 < baseStart_8078723 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078740 : List Nat := [2, 4, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_8078740 : Nat := 118140960795 + 8078740 * 2 ^ 59
def prefixEnd_8078740 : Nat := 4983230072969 + 3 ^ 40 * 8078740 * 2
def baseEnd_8078740 : Nat := 1382758900901275708765519

theorem tailTrace_8078740 : CollatzResearch.WordTrace tailWord_8078740 prefixEnd_8078740 1382758900901275708765519 := by
  unfold tailWord_8078740
  simp only [CollatzResearch.WordTrace]
  refine ⟨147327927376056096895240837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196437236501408129193654449 147327927376056096895240837)
  ·
    refine ⟨27623986383010518167857657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147327927376056096895240837 27623986383010518167857657)
    ·
      refine ⟨20717989787257888625893243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27623986383010518167857657 20717989787257888625893243)
      ·
        refine ⟨31076984680886832938839865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20717989787257888625893243 31076984680886832938839865)
        ·
          refine ⟨23307738510665124704129899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31076984680886832938839865 23307738510665124704129899)
          ·
            refine ⟨34961607765997687056194849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23307738510665124704129899 34961607765997687056194849)
            ·
              refine ⟨26221205824498265292146137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34961607765997687056194849 26221205824498265292146137)
              ·
                refine ⟨19665904368373698969109603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26221205824498265292146137 19665904368373698969109603)
                ·
                  refine ⟨29498856552560548453664405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19665904368373698969109603 29498856552560548453664405)
                  ·
                    refine ⟨1382758900901275708765519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29498856552560548453664405 1382758900901275708765519)
                    ·
                      rfl

theorem cell23_8078740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_8078740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078740 prefixEnd_8078740 := by exact prefixLift 8078740
  have htrace : WordTrace (prefixWord ++ tailWord_8078740) baseStart_8078740 baseEnd_8078740 := by
    simpa [prefixWord, tailWord_8078740, baseEnd_8078740] using wordTrace_append hprefix tailTrace_8078740
  have hstable : (prefixWord ++ tailWord_8078740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078740).length < 2 ^ (prefixWord ++ tailWord_8078740).sum := by decide
  have hdescent : baseEnd_8078740 < baseStart_8078740 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8078744 : List Nat := [2, 1, 2, 5, 2, 2, 2, 1, 1, 5]
def baseStart_8078744 : Nat := 118140960795 + 8078744 * 2 ^ 59
def prefixEnd_8078744 : Nat := 4983230072969 + 3 ^ 40 * 8078744 * 2
def baseEnd_8078744 : Nat := 1382759585542148370215513

theorem tailTrace_8078744 : CollatzResearch.WordTrace tailWord_8078744 prefixEnd_8078744 1382759585542148370215513 := by
  unfold tailWord_8078744
  simp only [CollatzResearch.WordTrace]
  refine ⟨147328000322048851236813643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196437333762731801649084857 147328000322048851236813643)
  ·
    refine ⟨220992000483073276855220465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147328000322048851236813643 220992000483073276855220465)
    ·
      refine ⟨165744000362304957641415349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220992000483073276855220465 165744000362304957641415349)
      ·
        refine ⟨15538500033966089778882689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165744000362304957641415349 15538500033966089778882689)
        ·
          refine ⟨11653875025474567334162017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15538500033966089778882689 11653875025474567334162017)
          ·
            refine ⟨8740406269105925500621513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11653875025474567334162017 8740406269105925500621513)
            ·
              refine ⟨6555304701829444125466135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8740406269105925500621513 6555304701829444125466135)
              ·
                refine ⟨9832957052744166188199203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6555304701829444125466135 9832957052744166188199203)
                ·
                  refine ⟨14749435579116249282298805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9832957052744166188199203 14749435579116249282298805)
                  ·
                    refine ⟨1382759585542148370215513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14749435579116249282298805 1382759585542148370215513)
                    ·
                      rfl

theorem cell23_8078744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 2, 1, 1, 5].length) (baseStart_8078744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8078744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8078744 prefixEnd_8078744 := by exact prefixLift 8078744
  have htrace : WordTrace (prefixWord ++ tailWord_8078744) baseStart_8078744 baseEnd_8078744 := by
    simpa [prefixWord, tailWord_8078744, baseEnd_8078744] using wordTrace_append hprefix tailTrace_8078744
  have hstable : (prefixWord ++ tailWord_8078744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8078744).length < 2 ^ (prefixWord ++ tailWord_8078744).sum := by decide
  have hdescent : baseEnd_8078744 < baseStart_8078744 := by decide
  rcases family_descends (prefixWord ++ tailWord_8078744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
