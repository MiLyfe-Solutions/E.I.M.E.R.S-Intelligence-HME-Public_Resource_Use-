import V185TrunkScan23Chunk0688

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4074397 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 1, 8]
def baseStart_4074397 : Nat := 118140960795 + 4074397 * 2 ^ 59
def prefixEnd_4074397 : Nat := 4983230072969 + 3 ^ 40 * 4074397 * 2
def baseEnd_4074397 : Nat := 697374679412333545566565

theorem tailTrace_4074397 : CollatzResearch.WordTrace tailWord_4074397 prefixEnd_4074397 697374679412333545566565 := by
  unfold tailWord_4074397
  simp only [CollatzResearch.WordTrace]
  refine ⟨148605467020162995453133445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99070311346775330302088963 148605467020162995453133445)
  ·
    refine ⟨27863525066280561647462521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148605467020162995453133445 27863525066280561647462521)
    ·
      refine ⟨20897643799710421235596891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27863525066280561647462521 20897643799710421235596891)
      ·
        refine ⟨31346465699565631853395337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20897643799710421235596891 31346465699565631853395337)
        ·
          refine ⟨23509849274674223890046503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31346465699565631853395337 23509849274674223890046503)
          ·
            refine ⟨35264773912011335835069755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23509849274674223890046503 35264773912011335835069755)
            ·
              refine ⟨52897160868017003752604633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35264773912011335835069755 52897160868017003752604633)
              ·
                refine ⟨39672870651012752814453475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52897160868017003752604633 39672870651012752814453475)
                ·
                  refine ⟨59509305976519129221680213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39672870651012752814453475 59509305976519129221680213)
                  ·
                    refine ⟨697374679412333545566565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59509305976519129221680213 697374679412333545566565)
                    ·
                      rfl

theorem cell23_4074397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 8].length) (baseStart_4074397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074397 prefixEnd_4074397 := by exact prefixLift 4074397
  have htrace : WordTrace (prefixWord ++ tailWord_4074397) baseStart_4074397 baseEnd_4074397 := by
    simpa [prefixWord, tailWord_4074397, baseEnd_4074397] using wordTrace_append hprefix tailTrace_4074397
  have hstable : (prefixWord ++ tailWord_4074397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074397).length < 2 ^ (prefixWord ++ tailWord_4074397).sum := by decide
  have hdescent : baseEnd_4074397 < baseStart_4074397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074464 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 3, 7, 2]
def baseStart_4074464 : Nat := 118140960795 + 4074464 * 2 ^ 59
def prefixEnd_4074464 : Nat := 4983230072969 + 3 ^ 40 * 4074464 * 2
def baseEnd_4074464 : Nat := 2092158441440851874561887

theorem tailTrace_4074464 : CollatzResearch.WordTrace tailWord_4074464 prefixEnd_4074464 2092158441440851874561887 := by
  unfold tailWord_4074464
  simp only [CollatzResearch.WordTrace]
  refine ⟨74303955355460132947911223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99071940473946843930548297 74303955355460132947911223)
  ·
    refine ⟨111455933033190199421866835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74303955355460132947911223 111455933033190199421866835)
    ·
      refine ⟨167183899549785299132800253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111455933033190199421866835 167183899549785299132800253)
      ·
        refine ⟨62693962331169487174800095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167183899549785299132800253 62693962331169487174800095)
        ·
          refine ⟨94040943496754230762200143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62693962331169487174800095 94040943496754230762200143)
          ·
            refine ⟨141061415245131346143300215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94040943496754230762200143 141061415245131346143300215)
            ·
              refine ⟨211592122867697019214950323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141061415245131346143300215 211592122867697019214950323)
              ·
                refine ⟨317388184301545528822425485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211592122867697019214950323 317388184301545528822425485)
                ·
                  refine ⟨119020569113079573308409557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 317388184301545528822425485 119020569113079573308409557)
                  ·
                    refine ⟨2789544588587802499415849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 119020569113079573308409557 2789544588587802499415849)
                    ·
                      refine ⟨2092158441440851874561887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789544588587802499415849 2092158441440851874561887)
                      ·
                        rfl

theorem cell23_4074464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 7, 2].length) (baseStart_4074464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074464 prefixEnd_4074464 := by exact prefixLift 4074464
  have htrace : WordTrace (prefixWord ++ tailWord_4074464) baseStart_4074464 baseEnd_4074464 := by
    simpa [prefixWord, tailWord_4074464, baseEnd_4074464] using wordTrace_append hprefix tailTrace_4074464
  have hstable : (prefixWord ++ tailWord_4074464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074464).length < 2 ^ (prefixWord ++ tailWord_4074464).sum := by decide
  have hdescent : baseEnd_4074464 < baseStart_4074464 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074474 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 4, 5]
def baseStart_4074474 : Nat := 118140960795 + 4074474 * 2 ^ 59
def prefixEnd_4074474 : Nat := 4983230072969 + 3 ^ 40 * 4074474 * 2
def baseEnd_4074474 : Nat := 697387858749132278478947

theorem tailTrace_4074474 : CollatzResearch.WordTrace tailWord_4074474 prefixEnd_4074474 697387858749132278478947 := by
  unfold tailWord_4074474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37152068860221009400921619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99072183627256025069124317 37152068860221009400921619)
  ·
    refine ⟨55728103290331514101382429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37152068860221009400921619 55728103290331514101382429)
    ·
      refine ⟨20898038733874317788018411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55728103290331514101382429 20898038733874317788018411)
      ·
        refine ⟨31347058100811476682027617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20898038733874317788018411 31347058100811476682027617)
        ·
          refine ⟨23510293575608607511520713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31347058100811476682027617 23510293575608607511520713)
          ·
            refine ⟨17632720181706455633640535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23510293575608607511520713 17632720181706455633640535)
            ·
              refine ⟨26449080272559683450460803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17632720181706455633640535 26449080272559683450460803)
              ·
                refine ⟨39673620408839525175691205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26449080272559683450460803 39673620408839525175691205)
                ·
                  refine ⟨7438803826657410970442101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39673620408839525175691205 7438803826657410970442101)
                  ·
                    refine ⟨697387858749132278478947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7438803826657410970442101 697387858749132278478947)
                    ·
                      rfl

theorem cell23_4074474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_4074474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074474 prefixEnd_4074474 := by exact prefixLift 4074474
  have htrace : WordTrace (prefixWord ++ tailWord_4074474) baseStart_4074474 baseEnd_4074474 := by
    simpa [prefixWord, tailWord_4074474, baseEnd_4074474] using wordTrace_append hprefix tailTrace_4074474
  have hstable : (prefixWord ++ tailWord_4074474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074474).length < 2 ^ (prefixWord ++ tailWord_4074474).sum := by decide
  have hdescent : baseEnd_4074474 < baseStart_4074474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074478 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 7]
def baseStart_4074478 : Nat := 118140960795 + 4074478 * 2 ^ 59
def prefixEnd_4074478 : Nat := 4983230072969 + 3 ^ 40 * 4074478 * 2
def baseEnd_4074478 : Nat := 232462847796668313309647

theorem tailTrace_4074478 : CollatzResearch.WordTrace tailWord_4074478 prefixEnd_4074478 232462847796668313309647 := by
  unfold tailWord_4074478
  simp only [CollatzResearch.WordTrace]
  refine ⟨18576052666608693285854011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99072280888579697524554725 18576052666608693285854011)
  ·
    refine ⟨27864078999913039928781017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18576052666608693285854011 27864078999913039928781017)
    ·
      refine ⟨20898059249934779946585763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27864078999913039928781017 20898059249934779946585763)
      ·
        refine ⟨31347088874902169919878645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20898059249934779946585763 31347088874902169919878645)
        ·
          refine ⟨2938789582022078429988623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31347088874902169919878645 2938789582022078429988623)
          ·
            refine ⟨4408184373033117644982935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938789582022078429988623 4408184373033117644982935)
            ·
              refine ⟨6612276559549676467474403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408184373033117644982935 6612276559549676467474403)
              ·
                refine ⟨9918414839324514701211605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612276559549676467474403 9918414839324514701211605)
                ·
                  refine ⟨232462847796668313309647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9918414839324514701211605 232462847796668313309647)
                  ·
                    rfl

theorem cell23_4074478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_4074478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074478 prefixEnd_4074478 := by exact prefixLift 4074478
  have htrace : WordTrace (prefixWord ++ tailWord_4074478) baseStart_4074478 baseEnd_4074478 := by
    simpa [prefixWord, tailWord_4074478, baseEnd_4074478] using wordTrace_append hprefix tailTrace_4074478
  have hstable : (prefixWord ++ tailWord_4074478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074478).length < 2 ^ (prefixWord ++ tailWord_4074478).sum := by decide
  have hdescent : baseEnd_4074478 < baseStart_4074478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074531 : List Nat := [1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 3]
def baseStart_4074531 : Nat := 118140960795 + 4074531 * 2 ^ 59
def prefixEnd_4074531 : Nat := 4983230072969 + 3 ^ 40 * 4074531 * 2
def baseEnd_4074531 : Nat := 2092192844644703112424079

theorem tailTrace_4074531 : CollatzResearch.WordTrace tailWord_4074531 prefixEnd_4074531 2092192844644703112424079 := by
  unfold tailWord_4074531
  simp only [CollatzResearch.WordTrace]
  refine ⟨148610354401677536338511447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99073569601118357559007631 148610354401677536338511447)
  ·
    refine ⟨222915531602516304507767171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148610354401677536338511447 222915531602516304507767171)
    ·
      refine ⟨334373297403774456761650757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222915531602516304507767171 334373297403774456761650757)
      ·
        refine ⟨62694993263207710642809517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334373297403774456761650757 62694993263207710642809517)
        ·
          refine ⟨23510622473702891491053569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62694993263207710642809517 23510622473702891491053569)
          ·
            refine ⟨17632966855277168618290177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23510622473702891491053569 17632966855277168618290177)
            ·
              refine ⟨13224725141457876463717633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17632966855277168618290177 13224725141457876463717633)
              ·
                refine ⟨9918543856093407347788225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13224725141457876463717633 9918543856093407347788225)
                ·
                  refine ⟨7438907892070055510841169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9918543856093407347788225 7438907892070055510841169)
                  ·
                    refine ⟨5579180919052541633130877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7438907892070055510841169 5579180919052541633130877)
                    ·
                      refine ⟨2092192844644703112424079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579180919052541633130877 2092192844644703112424079)
                      ·
                        rfl

theorem cell23_4074531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_4074531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074531 prefixEnd_4074531 := by exact prefixLift 4074531
  have htrace : WordTrace (prefixWord ++ tailWord_4074531) baseStart_4074531 baseEnd_4074531 := by
    simpa [prefixWord, tailWord_4074531, baseEnd_4074531] using wordTrace_append hprefix tailTrace_4074531
  have hstable : (prefixWord ++ tailWord_4074531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074531).length < 2 ^ (prefixWord ++ tailWord_4074531).sum := by decide
  have hdescent : baseEnd_4074531 < baseStart_4074531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074581 : List Nat := [1, 3, 2, 2, 1, 2, 3, 3, 1, 5]
def baseStart_4074581 : Nat := 118140960795 + 4074581 * 2 ^ 59
def prefixEnd_4074581 : Nat := 4983230072969 + 3 ^ 40 * 4074581 * 2
def baseEnd_4074581 : Nat := 697406172892475972266283

theorem tailTrace_4074581 : CollatzResearch.WordTrace tailWord_4074581 prefixEnd_4074581 697406172892475972266283 := by
  unfold tailWord_4074581
  simp only [CollatzResearch.WordTrace]
  refine ⟨148612178051496394877831597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99074785367664263251887731 148612178051496394877831597)
  ·
    refine ⟨55729566769311148079186849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148612178051496394877831597 55729566769311148079186849)
    ·
      refine ⟨41797175076983361059390137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55729566769311148079186849 41797175076983361059390137)
      ·
        refine ⟨31347881307737520794542603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41797175076983361059390137 31347881307737520794542603)
        ·
          refine ⟨47021821961606281191813905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31347881307737520794542603 47021821961606281191813905)
          ·
            refine ⟨35266366471204710893860429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47021821961606281191813905 35266366471204710893860429)
            ·
              refine ⟨13224887426701766585197661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35266366471204710893860429 13224887426701766585197661)
              ·
                refine ⟨4959332785013162469449123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13224887426701766585197661 4959332785013162469449123)
                ·
                  refine ⟨7438999177519743704173685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4959332785013162469449123 7438999177519743704173685)
                  ·
                    refine ⟨697406172892475972266283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7438999177519743704173685 697406172892475972266283)
                    ·
                      rfl

theorem cell23_4074581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 5].length) (baseStart_4074581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074581 prefixEnd_4074581 := by exact prefixLift 4074581
  have htrace : WordTrace (prefixWord ++ tailWord_4074581) baseStart_4074581 baseEnd_4074581 := by
    simpa [prefixWord, tailWord_4074581, baseEnd_4074581] using wordTrace_append hprefix tailTrace_4074581
  have hstable : (prefixWord ++ tailWord_4074581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074581).length < 2 ^ (prefixWord ++ tailWord_4074581).sum := by decide
  have hdescent : baseEnd_4074581 < baseStart_4074581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074588 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 4, 3, 2]
def baseStart_4074588 : Nat := 118140960795 + 4074588 * 2 ^ 59
def prefixEnd_4074588 : Nat := 4983230072969 + 3 ^ 40 * 4074588 * 2
def baseEnd_4074588 : Nat := 2092222113042009389411317

theorem tailTrace_4074588 : CollatzResearch.WordTrace tailWord_4074588 prefixEnd_4074588 2092222113042009389411317 := by
  unfold tailWord_4074588
  simp only [CollatzResearch.WordTrace]
  refine ⟨74306216681235517536668209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99074955574980690048890945 74306216681235517536668209)
  ·
    refine ⟨55729662510926638152501157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74306216681235517536668209 55729662510926638152501157)
    ·
      refine ⟨10449311720798744653593967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55729662510926638152501157 10449311720798744653593967)
      ·
        refine ⟨15673967581198116980390951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10449311720798744653593967 15673967581198116980390951)
        ·
          refine ⟨23510951371797175470586427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15673967581198116980390951 23510951371797175470586427)
          ·
            refine ⟨35266427057695763205879641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23510951371797175470586427 35266427057695763205879641)
            ·
              refine ⟨26449820293271822404409731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35266427057695763205879641 26449820293271822404409731)
              ·
                refine ⟨39674730439907733606614597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26449820293271822404409731 39674730439907733606614597)
                ·
                  refine ⟨7439011957482700051240237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39674730439907733606614597 7439011957482700051240237)
                  ·
                    refine ⟨2789629484056012519215089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7439011957482700051240237 2789629484056012519215089)
                    ·
                      refine ⟨2092222113042009389411317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789629484056012519215089 2092222113042009389411317)
                      ·
                        rfl

theorem cell23_4074588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_4074588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074588 prefixEnd_4074588 := by exact prefixLift 4074588
  have htrace : WordTrace (prefixWord ++ tailWord_4074588) baseStart_4074588 baseEnd_4074588 := by
    simpa [prefixWord, tailWord_4074588, baseEnd_4074588] using wordTrace_append hprefix tailTrace_4074588
  have hstable : (prefixWord ++ tailWord_4074588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074588).length < 2 ^ (prefixWord ++ tailWord_4074588).sum := by decide
  have hdescent : baseEnd_4074588 < baseStart_4074588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074629 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 1, 1, 3]
def baseStart_4074629 : Nat := 118140960795 + 4074629 * 2 ^ 59
def prefixEnd_4074629 : Nat := 4983230072969 + 3 ^ 40 * 4074629 * 2
def baseEnd_4074629 : Nat := 2092243165748843728998629

theorem tailTrace_4074629 : CollatzResearch.WordTrace tailWord_4074629 prefixEnd_4074629 2092243165748843728998629 := by
  unfold tailWord_4074629
  simp only [CollatzResearch.WordTrace]
  refine ⟨148613928755322499075578941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99075952503548332717052627 148613928755322499075578941)
  ·
    refine ⟨55730223283245937153342103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148613928755322499075578941 55730223283245937153342103)
    ·
      refine ⟨83595334924868905730013155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55730223283245937153342103 83595334924868905730013155)
      ·
        refine ⟨125393002387303358595019733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83595334924868905730013155 125393002387303358595019733)
        ·
          refine ⟨2938898493452422467070775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125393002387303358595019733 2938898493452422467070775)
          ·
            refine ⟨4408347740178633700606163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2938898493452422467070775 4408347740178633700606163)
            ·
              refine ⟨6612521610267950550909245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408347740178633700606163 6612521610267950550909245)
              ·
                refine ⟨2479695603850481456590967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6612521610267950550909245 2479695603850481456590967)
                ·
                  refine ⟨3719543405775722184886451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479695603850481456590967 3719543405775722184886451)
                  ·
                    refine ⟨5579315108663583277329677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3719543405775722184886451 5579315108663583277329677)
                    ·
                      refine ⟨2092243165748843728998629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579315108663583277329677 2092243165748843728998629)
                      ·
                        rfl

theorem cell23_4074629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_4074629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074629 prefixEnd_4074629 := by exact prefixLift 4074629
  have htrace : WordTrace (prefixWord ++ tailWord_4074629) baseStart_4074629 baseEnd_4074629 := by
    simpa [prefixWord, tailWord_4074629, baseEnd_4074629] using wordTrace_append hprefix tailTrace_4074629
  have hstable : (prefixWord ++ tailWord_4074629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074629).length < 2 ^ (prefixWord ++ tailWord_4074629).sum := by decide
  have hdescent : baseEnd_4074629 < baseStart_4074629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074638 : List Nat := [4, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5]
def baseStart_4074638 : Nat := 118140960795 + 4074638 * 2 ^ 59
def prefixEnd_4074638 : Nat := 4983230072969 + 3 ^ 40 * 4074638 * 2
def baseEnd_4074638 : Nat := 2092247787074734193786087

theorem tailTrace_4074638 : CollatzResearch.WordTrace tailWord_4074638 prefixEnd_4074638 2092247787074734193786087 := by
  unfold tailWord_4074638
  simp only [CollatzResearch.WordTrace]
  refine ⟨18576782126536236701582071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99076171341526595741771045 18576782126536236701582071)
  ·
    refine ⟨27865173189804355052373107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18576782126536236701582071 27865173189804355052373107)
    ·
      refine ⟨41797759784706532578559661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27865173189804355052373107 41797759784706532578559661)
      ·
        refine ⟨15674159919264949716959873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41797759784706532578559661 15674159919264949716959873)
        ·
          refine ⟨11755619939448712287719905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15674159919264949716959873 11755619939448712287719905)
          ·
            refine ⟨8816714954586534215789929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11755619939448712287719905 8816714954586534215789929)
            ·
              refine ⟨6612536215939900661842447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816714954586534215789929 6612536215939900661842447)
              ·
                refine ⟨9918804323909850992763671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612536215939900661842447 9918804323909850992763671)
                ·
                  refine ⟨14878206485864776489145507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9918804323909850992763671 14878206485864776489145507)
                  ·
                    refine ⟨22317309728797164733718261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14878206485864776489145507 22317309728797164733718261)
                    ·
                      refine ⟨2092247787074734193786087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22317309728797164733718261 2092247787074734193786087)
                      ·
                        rfl

theorem cell23_4074638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_4074638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074638 prefixEnd_4074638 := by exact prefixLift 4074638
  have htrace : WordTrace (prefixWord ++ tailWord_4074638) baseStart_4074638 baseEnd_4074638 := by
    simpa [prefixWord, tailWord_4074638, baseEnd_4074638] using wordTrace_append hprefix tailTrace_4074638
  have hstable : (prefixWord ++ tailWord_4074638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074638).length < 2 ^ (prefixWord ++ tailWord_4074638).sum := by decide
  have hdescent : baseEnd_4074638 < baseStart_4074638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074652 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 3, 2, 2]
def baseStart_4074652 : Nat := 118140960795 + 4074652 * 2 ^ 59
def prefixEnd_4074652 : Nat := 4983230072969 + 3 ^ 40 * 4074652 * 2
def baseEnd_4074652 : Nat := 2092254975803897139011023

theorem tailTrace_4074652 : CollatzResearch.WordTrace tailWord_4074652 prefixEnd_4074652 2092254975803897139011023 := by
  unfold tailWord_4074652
  simp only [CollatzResearch.WordTrace]
  refine ⟨74307383817119587001833105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99076511756159449335777473 74307383817119587001833105)
  ·
    refine ⟨55730537862839690251374829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74307383817119587001833105 55730537862839690251374829)
    ·
      refine ⟨20898951698564883844265561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55730537862839690251374829 20898951698564883844265561)
      ·
        refine ⟨15674213773923662883199171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20898951698564883844265561 15674213773923662883199171)
        ·
          refine ⟨23511320660885494324798757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15674213773923662883199171 23511320660885494324798757)
          ·
            refine ⟨4408372623916030185899767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23511320660885494324798757 4408372623916030185899767)
            ·
              refine ⟨6612558935874045278849651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408372623916030185899767 6612558935874045278849651)
              ·
                refine ⟨9918838403811067918274477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612558935874045278849651 9918838403811067918274477)
                ·
                  refine ⟨3719564401429150469352929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9918838403811067918274477 3719564401429150469352929)
                  ·
                    refine ⟨2789673301071862852014697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3719564401429150469352929 2789673301071862852014697)
                    ·
                      refine ⟨2092254975803897139011023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789673301071862852014697 2092254975803897139011023)
                      ·
                        rfl

theorem cell23_4074652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_4074652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074652 prefixEnd_4074652 := by exact prefixLift 4074652
  have htrace : WordTrace (prefixWord ++ tailWord_4074652) baseStart_4074652 baseEnd_4074652 := by
    simpa [prefixWord, tailWord_4074652, baseEnd_4074652] using wordTrace_append hprefix tailTrace_4074652
  have hstable : (prefixWord ++ tailWord_4074652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074652).length < 2 ^ (prefixWord ++ tailWord_4074652).sum := by decide
  have hdescent : baseEnd_4074652 < baseStart_4074652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074658 : List Nat := [3, 3, 1, 3, 2, 1, 2, 8]
def baseStart_4074658 : Nat := 118140960795 + 4074658 * 2 ^ 59
def prefixEnd_4074658 : Nat := 4983230072969 + 3 ^ 40 * 4074658 * 2
def baseEnd_4074658 : Nat := 77491039136586078353185

theorem tailTrace_4074658 : CollatzResearch.WordTrace tailWord_4074658 prefixEnd_4074658 77491039136586078353185 := by
  unfold tailWord_4074658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37153746618054359257096157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99076657648144958018923085 37153746618054359257096157)
  ·
    refine ⟨13932654981770384721411059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37153746618054359257096157 13932654981770384721411059)
    ·
      refine ⟨20898982472655577082116589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13932654981770384721411059 20898982472655577082116589)
      ·
        refine ⟨7837118427245841405793721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20898982472655577082116589 7837118427245841405793721)
        ·
          refine ⟨5877838820434381054345291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7837118427245841405793721 5877838820434381054345291)
          ·
            refine ⟨8816758230651571581517937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877838820434381054345291 8816758230651571581517937)
            ·
              refine ⟨6612568672988678686138453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816758230651571581517937 6612568672988678686138453)
              ·
                refine ⟨77491039136586078353185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6612568672988678686138453 77491039136586078353185)
                ·
                  rfl

theorem cell23_4074658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 8].length) (baseStart_4074658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074658 prefixEnd_4074658 := by exact prefixLift 4074658
  have htrace : WordTrace (prefixWord ++ tailWord_4074658) baseStart_4074658 baseEnd_4074658 := by
    simpa [prefixWord, tailWord_4074658, baseEnd_4074658] using wordTrace_append hprefix tailTrace_4074658
  have hstable : (prefixWord ++ tailWord_4074658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074658).length < 2 ^ (prefixWord ++ tailWord_4074658).sum := by decide
  have hdescent : baseEnd_4074658 < baseStart_4074658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074702 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3]
def baseStart_4074702 : Nat := 118140960795 + 4074702 * 2 ^ 59
def prefixEnd_4074702 : Nat := 4983230072969 + 3 ^ 40 * 4074702 * 2
def baseEnd_4074702 : Nat := 2092280649836621943385793

theorem tailTrace_4074702 : CollatzResearch.WordTrace tailWord_4074702 prefixEnd_4074702 2092280649836621943385793 := by
  unfold tailWord_4074702
  simp only [CollatzResearch.WordTrace]
  refine ⟨18577073910507254067873295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99077727522705355028657573 18577073910507254067873295)
  ·
    refine ⟨27865610865760881101809943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18577073910507254067873295 27865610865760881101809943)
    ·
      refine ⟨41798416298641321652714915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27865610865760881101809943 41798416298641321652714915)
      ·
        refine ⟨62697624447961982479072373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41798416298641321652714915 62697624447961982479072373)
        ·
          refine ⟨5877902291996435857413035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62697624447961982479072373 5877902291996435857413035)
          ·
            refine ⟨8816853437994653786119553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5877902291996435857413035 8816853437994653786119553)
            ·
              refine ⟨6612640078495990339589665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8816853437994653786119553 6612640078495990339589665)
              ·
                refine ⟨4959480058871992754692249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6612640078495990339589665 4959480058871992754692249)
                ·
                  refine ⟨3719610044153994566019187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4959480058871992754692249 3719610044153994566019187)
                  ·
                    refine ⟨5579415066230991849028781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3719610044153994566019187 5579415066230991849028781)
                    ·
                      refine ⟨2092280649836621943385793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579415066230991849028781 2092280649836621943385793)
                      ·
                        rfl

theorem cell23_4074702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_4074702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074702 prefixEnd_4074702 := by exact prefixLift 4074702
  have htrace : WordTrace (prefixWord ++ tailWord_4074702) baseStart_4074702 baseEnd_4074702 := by
    simpa [prefixWord, tailWord_4074702, baseEnd_4074702] using wordTrace_append hprefix tailTrace_4074702
  have hstable : (prefixWord ++ tailWord_4074702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074702).length < 2 ^ (prefixWord ++ tailWord_4074702).sum := by decide
  have hdescent : baseEnd_4074702 < baseStart_4074702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074711 : List Nat := [1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_4074711 : Nat := 118140960795 + 4074711 * 2 ^ 59
def prefixEnd_4074711 : Nat := 4983230072969 + 3 ^ 40 * 4074711 * 2
def baseEnd_4074711 : Nat := 2092285271162512408173251

theorem tailTrace_4074711 : CollatzResearch.WordTrace tailWord_4074711 prefixEnd_4074711 2092285271162512408173251 := by
  unfold tailWord_4074711
  simp only [CollatzResearch.WordTrace]
  refine ⟨148616919541025427080063987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99077946360683618053375991 148616919541025427080063987)
  ·
    refine ⟨222925379311538140620095981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148616919541025427080063987 222925379311538140620095981)
    ·
      refine ⟨83597017241826802732535993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222925379311538140620095981 83597017241826802732535993)
      ·
        refine ⟨62697762931370102049401995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83597017241826802732535993 62697762931370102049401995)
        ·
          refine ⟨94046644397055153074102993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62697762931370102049401995 94046644397055153074102993)
          ·
            refine ⟨70534983297791364805577245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94046644397055153074102993 70534983297791364805577245)
            ·
              refine ⟨26450618736671761802091467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70534983297791364805577245 26450618736671761802091467)
              ·
                refine ⟨39675928105007642703137201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26450618736671761802091467 39675928105007642703137201)
                ·
                  refine ⟨29756946078755732027352901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39675928105007642703137201 29756946078755732027352901)
                  ·
                    refine ⟨5579427389766699755128669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29756946078755732027352901 5579427389766699755128669)
                    ·
                      refine ⟨2092285271162512408173251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579427389766699755128669 2092285271162512408173251)
                      ·
                        rfl

theorem cell23_4074711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_4074711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074711 prefixEnd_4074711 := by exact prefixLift 4074711
  have htrace : WordTrace (prefixWord ++ tailWord_4074711) baseStart_4074711 baseEnd_4074711 := by
    simpa [prefixWord, tailWord_4074711, baseEnd_4074711] using wordTrace_append hprefix tailTrace_4074711
  have hstable : (prefixWord ++ tailWord_4074711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074711).length < 2 ^ (prefixWord ++ tailWord_4074711).sum := by decide
  have hdescent : baseEnd_4074711 < baseStart_4074711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074721 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 4]
def baseStart_4074721 : Nat := 118140960795 + 4074721 * 2 ^ 59
def prefixEnd_4074721 : Nat := 4983230072969 + 3 ^ 40 * 4074721 * 2
def baseEnd_4074721 : Nat := 2092290405969057369048205

theorem tailTrace_4074721 : CollatzResearch.WordTrace tailWord_4074721 prefixEnd_4074721 2092290405969057369048205 := by
  unfold tailWord_4074721
  simp only [CollatzResearch.WordTrace]
  refine ⟨148617284270989198787928017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99078189513992799191952011 148617284270989198787928017)
  ·
    refine ⟨111462963203241899090946013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148617284270989198787928017 111462963203241899090946013)
    ·
      refine ⟨41798611201215712159104755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111462963203241899090946013 41798611201215712159104755)
      ·
        refine ⟨62697916801823568238657133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41798611201215712159104755 62697916801823568238657133)
        ·
          refine ⟨23511718800683838089496425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62697916801823568238657133 23511718800683838089496425)
          ·
            refine ⟨17633789100512878567122319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23511718800683838089496425 17633789100512878567122319)
            ·
              refine ⟨26450683650769317850683479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17633789100512878567122319 26450683650769317850683479)
              ·
                refine ⟨39676025476153976776025219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26450683650769317850683479 39676025476153976776025219)
                ·
                  refine ⟨59514038214230965164037829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39676025476153976776025219 59514038214230965164037829)
                  ·
                    refine ⟨11158882165168305968257093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59514038214230965164037829 11158882165168305968257093)
                    ·
                      refine ⟨2092290405969057369048205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11158882165168305968257093 2092290405969057369048205)
                      ·
                        rfl

theorem cell23_4074721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_4074721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074721 prefixEnd_4074721 := by exact prefixLift 4074721
  have htrace : WordTrace (prefixWord ++ tailWord_4074721) baseStart_4074721 baseEnd_4074721 := by
    simpa [prefixWord, tailWord_4074721, baseEnd_4074721] using wordTrace_append hprefix tailTrace_4074721
  have hstable : (prefixWord ++ tailWord_4074721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074721).length < 2 ^ (prefixWord ++ tailWord_4074721).sum := by decide
  have hdescent : baseEnd_4074721 < baseStart_4074721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074731 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 7]
def baseStart_4074731 : Nat := 118140960795 + 4074731 * 2 ^ 59
def prefixEnd_4074731 : Nat := 4983230072969 + 3 ^ 40 * 4074731 * 2
def baseEnd_4074731 : Nat := 232477282308400258880351

theorem tailTrace_4074731 : CollatzResearch.WordTrace tailWord_4074731 prefixEnd_4074731 232477282308400258880351 := by
  unfold tailWord_4074731
  simp only [CollatzResearch.WordTrace]
  refine ⟨148617649000952970495792047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99078432667301980330528031 148617649000952970495792047)
  ·
    refine ⟨222926473501429455743688071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148617649000952970495792047 222926473501429455743688071)
    ·
      refine ⟨334389710252144183615532107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222926473501429455743688071 334389710252144183615532107)
      ·
        refine ⟨501584565378216275423298161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334389710252144183615532107 501584565378216275423298161)
        ·
          refine ⟨376188424033662206567473621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501584565378216275423298161 376188424033662206567473621)
          ·
            refine ⟨8816916188288957966425163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 376188424033662206567473621 8816916188288957966425163)
            ·
              refine ⟨13225374282433436949637745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8816916188288957966425163 13225374282433436949637745)
              ·
                refine ⟨9919030711825077712228309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13225374282433436949637745 9919030711825077712228309)
                ·
                  refine ⟨232477282308400258880351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9919030711825077712228309 232477282308400258880351)
                  ·
                    rfl

theorem cell23_4074731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 7].length) (baseStart_4074731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074731 prefixEnd_4074731 := by exact prefixLift 4074731
  have htrace : WordTrace (prefixWord ++ tailWord_4074731) baseStart_4074731 baseEnd_4074731 := by
    simpa [prefixWord, tailWord_4074731, baseEnd_4074731] using wordTrace_append hprefix tailTrace_4074731
  have hstable : (prefixWord ++ tailWord_4074731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074731).length < 2 ^ (prefixWord ++ tailWord_4074731).sum := by decide
  have hdescent : baseEnd_4074731 < baseStart_4074731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074761 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 4, 5]
def baseStart_4074761 : Nat := 118140960795 + 4074761 * 2 ^ 59
def prefixEnd_4074761 : Nat := 4983230072969 + 3 ^ 40 * 4074761 * 2
def baseEnd_4074761 : Nat := 697436981731745737516007

theorem tailTrace_4074761 : CollatzResearch.WordTrace tailWord_4074761 prefixEnd_4074761 697436981731745737516007 := by
  unfold tailWord_4074761
  simp only [CollatzResearch.WordTrace]
  refine ⟨148618743190844285619384137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99079162127229523746256091 148618743190844285619384137)
  ·
    refine ⟨111464057393133214214538103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148618743190844285619384137 111464057393133214214538103)
    ·
      refine ⟨167196086089699821321807155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111464057393133214214538103 167196086089699821321807155)
      ·
        refine ⟨250794129134549731982710733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167196086089699821321807155 250794129134549731982710733)
        ·
          refine ⟨94047798425456149493516525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250794129134549731982710733 94047798425456149493516525)
          ·
            refine ⟨35267924409546056060068697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94047798425456149493516525 35267924409546056060068697)
            ·
              refine ⟨26450943307159542045051523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35267924409546056060068697 26450943307159542045051523)
              ·
                refine ⟨39676414960739313067577285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26450943307159542045051523 39676414960739313067577285)
                ·
                  refine ⟨7439327805138621200170741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39676414960739313067577285 7439327805138621200170741)
                  ·
                    refine ⟨697436981731745737516007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7439327805138621200170741 697436981731745737516007)
                    ·
                      rfl

theorem cell23_4074761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 5].length) (baseStart_4074761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074761 prefixEnd_4074761 := by exact prefixLift 4074761
  have htrace : WordTrace (prefixWord ++ tailWord_4074761) baseStart_4074761 baseEnd_4074761 := by
    simpa [prefixWord, tailWord_4074761, baseEnd_4074761] using wordTrace_append hprefix tailTrace_4074761
  have hstable : (prefixWord ++ tailWord_4074761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074761).length < 2 ^ (prefixWord ++ tailWord_4074761).sum := by decide
  have hdescent : baseEnd_4074761 < baseStart_4074761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074825 : List Nat := [1, 2, 1, 1, 2, 3, 2, 6, 1, 4]
def baseStart_4074825 : Nat := 118140960795 + 4074825 * 2 ^ 59
def prefixEnd_4074825 : Nat := 4983230072969 + 3 ^ 40 * 4074825 * 2
def baseEnd_4074825 : Nat := 697447935985708320715909

theorem tailTrace_4074825 : CollatzResearch.WordTrace tailWord_4074825 prefixEnd_4074825 697447935985708320715909 := by
  unfold tailWord_4074825
  simp only [CollatzResearch.WordTrace]
  refine ⟨148621077462612424549713929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99080718308408283033142619 148621077462612424549713929)
  ·
    refine ⟨111465808096959318412285447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148621077462612424549713929 111465808096959318412285447)
    ·
      refine ⟨167198712145438977618428171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111465808096959318412285447 167198712145438977618428171)
      ·
        refine ⟨250798068218158466427642257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167198712145438977618428171 250798068218158466427642257)
        ·
          refine ⟨188098551163618849820731693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250798068218158466427642257 188098551163618849820731693)
          ·
            refine ⟨70536956686357068682774385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188098551163618849820731693 70536956686357068682774385)
            ·
              refine ⟨52902717514767801512080789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70536956686357068682774385 52902717514767801512080789)
              ·
                refine ⟨2479814883504740695878787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52902717514767801512080789 2479814883504740695878787)
                ·
                  refine ⟨3719722325257111043818181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479814883504740695878787 3719722325257111043818181)
                  ·
                    refine ⟨697447935985708320715909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3719722325257111043818181 697447935985708320715909)
                    ·
                      rfl

theorem cell23_4074825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 6, 1, 4].length) (baseStart_4074825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074825 prefixEnd_4074825 := by exact prefixLift 4074825
  have htrace : WordTrace (prefixWord ++ tailWord_4074825) baseStart_4074825 baseEnd_4074825 := by
    simpa [prefixWord, tailWord_4074825, baseEnd_4074825] using wordTrace_append hprefix tailTrace_4074825
  have hstable : (prefixWord ++ tailWord_4074825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074825).length < 2 ^ (prefixWord ++ tailWord_4074825).sum := by decide
  have hdescent : baseEnd_4074825 < baseStart_4074825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074841 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 6]
def baseStart_4074841 : Nat := 118140960795 + 4074841 * 2 ^ 59
def prefixEnd_4074841 : Nat := 4983230072969 + 3 ^ 40 * 4074841 * 2
def baseEnd_4074841 : Nat := 2092352023647596899547653

theorem tailTrace_4074841 : CollatzResearch.WordTrace tailWord_4074841 prefixEnd_4074841 2092352023647596899547653 := by
  unfold tailWord_4074841
  simp only [CollatzResearch.WordTrace]
  refine ⟨148621661030554459282296377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99081107353702972854864251 148621661030554459282296377)
  ·
    refine ⟨111466245772915844461722283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148621661030554459282296377 111466245772915844461722283)
    ·
      refine ⟨167199368659373766692583425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111466245772915844461722283 167199368659373766692583425)
      ·
        refine ⟨125399526494530325019437569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167199368659373766692583425 125399526494530325019437569)
        ·
          refine ⟨94049644870897743764578177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125399526494530325019437569 94049644870897743764578177)
          ·
            refine ⟨70537233653173307823433633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94049644870897743764578177 70537233653173307823433633)
            ·
              refine ⟨52902925239879980867575225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70537233653173307823433633 52902925239879980867575225)
              ·
                refine ⟨39677193929909985650681419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52902925239879980867575225 39677193929909985650681419)
                ·
                  refine ⟨59515790894864978476022129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39677193929909985650681419 59515790894864978476022129)
                  ·
                    refine ⟨44636843171148733857016597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59515790894864978476022129 44636843171148733857016597)
                    ·
                      refine ⟨2092352023647596899547653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44636843171148733857016597 2092352023647596899547653)
                      ·
                        rfl

theorem cell23_4074841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 2, 6].length) (baseStart_4074841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074841 prefixEnd_4074841 := by exact prefixLift 4074841
  have htrace : WordTrace (prefixWord ++ tailWord_4074841) baseStart_4074841 baseEnd_4074841 := by
    simpa [prefixWord, tailWord_4074841, baseEnd_4074841] using wordTrace_append hprefix tailTrace_4074841
  have hstable : (prefixWord ++ tailWord_4074841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074841).length < 2 ^ (prefixWord ++ tailWord_4074841).sum := by decide
  have hdescent : baseEnd_4074841 < baseStart_4074841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074875 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 2, 3, 2]
def baseStart_4074875 : Nat := 118140960795 + 4074875 * 2 ^ 59
def prefixEnd_4074875 : Nat := 4983230072969 + 3 ^ 40 * 4074875 * 2
def baseEnd_4074875 : Nat := 2092369481989849766522497

theorem tailTrace_4074875 : CollatzResearch.WordTrace tailWord_4074875 prefixEnd_4074875 2092369481989849766522497 := by
  unfold tailWord_4074875
  simp only [CollatzResearch.WordTrace]
  refine ⟨148622901112431283089034079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99081934074954188726022719 148622901112431283089034079)
  ·
    refine ⟨222934351668646924633551119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148622901112431283089034079 222934351668646924633551119)
    ·
      refine ⟨334401527502970386950326679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222934351668646924633551119 334401527502970386950326679)
      ·
        refine ⟨501602291254455580425490019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334401527502970386950326679 501602291254455580425490019)
        ·
          refine ⟨752403436881683370638235029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501602291254455580425490019 752403436881683370638235029)
          ·
            refine ⟨35268911103828907998667267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 752403436881683370638235029 35268911103828907998667267)
            ·
              refine ⟨52903366655743361998000901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35268911103828907998667267 52903366655743361998000901)
              ·
                refine ⟨9919381247951880374625169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52903366655743361998000901 9919381247951880374625169)
                ·
                  refine ⟨7439535935963910280968877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9919381247951880374625169 7439535935963910280968877)
                  ·
                    refine ⟨2789825975986466355363329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7439535935963910280968877 2789825975986466355363329)
                    ·
                      refine ⟨2092369481989849766522497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789825975986466355363329 2092369481989849766522497)
                      ·
                        rfl

theorem cell23_4074875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3, 2].length) (baseStart_4074875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074875 prefixEnd_4074875 := by exact prefixLift 4074875
  have htrace : WordTrace (prefixWord ++ tailWord_4074875) baseStart_4074875 baseEnd_4074875 := by
    simpa [prefixWord, tailWord_4074875, baseEnd_4074875] using wordTrace_append hprefix tailTrace_4074875
  have hstable : (prefixWord ++ tailWord_4074875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074875).length < 2 ^ (prefixWord ++ tailWord_4074875).sum := by decide
  have hdescent : baseEnd_4074875 < baseStart_4074875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074909 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 2, 3, 2]
def baseStart_4074909 : Nat := 118140960795 + 4074909 * 2 ^ 59
def prefixEnd_4074909 : Nat := 4983230072969 + 3 ^ 40 * 4074909 * 2
def baseEnd_4074909 : Nat := 2092386940332102633497341

theorem tailTrace_4074909 : CollatzResearch.WordTrace tailWord_4074909 prefixEnd_4074909 2092386940332102633497341 := by
  unfold tailWord_4074909
  simp only [CollatzResearch.WordTrace]
  refine ⟨148624141194308106895771781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99082760796205404597181187 148624141194308106895771781)
  ·
    refine ⟨27867026473932770042957209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148624141194308106895771781 27867026473932770042957209)
    ·
      refine ⟨20900269855449577532217907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27867026473932770042957209 20900269855449577532217907)
      ·
        refine ⟨31350404783174366298326861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20900269855449577532217907 31350404783174366298326861)
        ·
          refine ⟨11756401793690387361872573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31350404783174366298326861 11756401793690387361872573)
          ·
            refine ⟨4408650672633895260702215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11756401793690387361872573 4408650672633895260702215)
            ·
              refine ⟨6612976008950842891053323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408650672633895260702215 6612976008950842891053323)
              ·
                refine ⟨9919464013426264336579985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6612976008950842891053323 9919464013426264336579985)
                ·
                  refine ⟨7439598010069698252434989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9919464013426264336579985 7439598010069698252434989)
                  ·
                    refine ⟨2789849253776136844663121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7439598010069698252434989 2789849253776136844663121)
                    ·
                      refine ⟨2092386940332102633497341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789849253776136844663121 2092386940332102633497341)
                      ·
                        rfl

theorem cell23_4074909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_4074909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074909 prefixEnd_4074909 := by exact prefixLift 4074909
  have htrace : WordTrace (prefixWord ++ tailWord_4074909) baseStart_4074909 baseEnd_4074909 := by
    simpa [prefixWord, tailWord_4074909, baseEnd_4074909] using wordTrace_append hprefix tailTrace_4074909
  have hstable : (prefixWord ++ tailWord_4074909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074909).length < 2 ^ (prefixWord ++ tailWord_4074909).sum := by decide
  have hdescent : baseEnd_4074909 < baseStart_4074909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074938 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_4074938 : Nat := 118140960795 + 4074938 * 2 ^ 59
def prefixEnd_4074938 : Nat := 4983230072969 + 3 ^ 40 * 4074938 * 2
def baseEnd_4074938 : Nat := 2092401831271083020034707

theorem tailTrace_4074938 : CollatzResearch.WordTrace tailWord_4074938 prefixEnd_4074938 2092401831271083020034707 := by
  unfold tailWord_4074938
  simp only [CollatzResearch.WordTrace]
  refine ⟨37156299727800761212144367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99083465940802029899051645 37156299727800761212144367)
  ·
    refine ⟨55734449591701141818216551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37156299727800761212144367 55734449591701141818216551)
    ·
      refine ⟨83601674387551712727324827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55734449591701141818216551 83601674387551712727324827)
      ·
        refine ⟨125402511581327569090987241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83601674387551712727324827 125402511581327569090987241)
        ·
          refine ⟨94051883685995676818240431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125402511581327569090987241 94051883685995676818240431)
          ·
            refine ⟨141077825528993515227360647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94051883685995676818240431 141077825528993515227360647)
            ·
              refine ⟨211616738293490272841040971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141077825528993515227360647 211616738293490272841040971)
              ·
                refine ⟨317425107440235409261561457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211616738293490272841040971 317425107440235409261561457)
                ·
                  refine ⟨238068830580176556946171093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317425107440235409261561457 238068830580176556946171093)
                  ·
                    refine ⟨5579738216722888053425885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 238068830580176556946171093 5579738216722888053425885)
                    ·
                      refine ⟨2092401831271083020034707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579738216722888053425885 2092401831271083020034707)
                      ·
                        rfl

theorem cell23_4074938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_4074938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074938 prefixEnd_4074938 := by exact prefixLift 4074938
  have htrace : WordTrace (prefixWord ++ tailWord_4074938) baseStart_4074938 baseEnd_4074938 := by
    simpa [prefixWord, tailWord_4074938, baseEnd_4074938] using wordTrace_append hprefix tailTrace_4074938
  have hstable : (prefixWord ++ tailWord_4074938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074938).length < 2 ^ (prefixWord ++ tailWord_4074938).sum := by decide
  have hdescent : baseEnd_4074938 < baseStart_4074938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074955 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 3]
def baseStart_4074955 : Nat := 118140960795 + 4074955 * 2 ^ 59
def prefixEnd_4074955 : Nat := 4983230072969 + 3 ^ 40 * 4074955 * 2
def baseEnd_4074955 : Nat := 2092410560442209453522129

theorem tailTrace_4074955 : CollatzResearch.WordTrace tailWord_4074955 prefixEnd_4074955 2092410560442209453522129 := by
  unfold tailWord_4074955
  simp only [CollatzResearch.WordTrace]
  refine ⟨148625818952141456751946319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99083879301427637834630879 148625818952141456751946319)
  ·
    refine ⟨222938728428212185127919479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148625818952141456751946319 222938728428212185127919479)
    ·
      refine ⟨334408092642318277691879219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222938728428212185127919479 334408092642318277691879219)
      ·
        refine ⟨501612138963477416537818829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334408092642318277691879219 501612138963477416537818829)
        ·
          refine ⟨188104552111304031201682061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501612138963477416537818829 188104552111304031201682061)
          ·
            refine ⟨70539207041739011700630773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188104552111304031201682061 70539207041739011700630773)
            ·
              refine ⟨6613050660163032346934135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70539207041739011700630773 6613050660163032346934135)
              ·
                refine ⟨9919575990244548520401203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613050660163032346934135 9919575990244548520401203)
                ·
                  refine ⟨14879363985366822780601805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9919575990244548520401203 14879363985366822780601805)
                  ·
                    refine ⟨5579761494512558542725677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879363985366822780601805 5579761494512558542725677)
                    ·
                      refine ⟨2092410560442209453522129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579761494512558542725677 2092410560442209453522129)
                      ·
                        rfl

theorem cell23_4074955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 1, 3, 3].length) (baseStart_4074955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074955 prefixEnd_4074955 := by exact prefixLift 4074955
  have htrace : WordTrace (prefixWord ++ tailWord_4074955) baseStart_4074955 baseEnd_4074955 := by
    simpa [prefixWord, tailWord_4074955, baseEnd_4074955] using wordTrace_append hprefix tailTrace_4074955
  have hstable : (prefixWord ++ tailWord_4074955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074955).length < 2 ^ (prefixWord ++ tailWord_4074955).sum := by decide
  have hdescent : baseEnd_4074955 < baseStart_4074955 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074958 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_4074958 : Nat := 118140960795 + 4074958 * 2 ^ 59
def prefixEnd_4074958 : Nat := 4983230072969 + 3 ^ 40 * 4074958 * 2
def baseEnd_4074958 : Nat := 697470700294724313928205

theorem tailTrace_4074958 : CollatzResearch.WordTrace tailWord_4074958 prefixEnd_4074958 697470700294724313928205 := by
  unfold tailWord_4074958
  simp only [CollatzResearch.WordTrace]
  refine ⟨18578241046391323533038191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99083952247420392176203685 18578241046391323533038191)
  ·
    refine ⟨27867361569586985299557287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18578241046391323533038191 27867361569586985299557287)
    ·
      refine ⟨41801042354380477949335931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27867361569586985299557287 41801042354380477949335931)
      ·
        refine ⟨62701563531570716924003897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41801042354380477949335931 62701563531570716924003897)
        ·
          refine ⟨47026172648678037693002923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62701563531570716924003897 47026172648678037693002923)
          ·
            refine ⟨70539258973017056539504385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47026172648678037693002923 70539258973017056539504385)
            ·
              refine ⟨52904444229762792404628289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70539258973017056539504385 52904444229762792404628289)
              ·
                refine ⟨39678333172322094303471217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52904444229762792404628289 39678333172322094303471217)
                ·
                  refine ⟨29758749879241570727603413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39678333172322094303471217 29758749879241570727603413)
                  ·
                    refine ⟨697470700294724313928205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29758749879241570727603413 697470700294724313928205)
                    ·
                      rfl

theorem cell23_4074958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_4074958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074958 prefixEnd_4074958 := by exact prefixLift 4074958
  have htrace : WordTrace (prefixWord ++ tailWord_4074958) baseStart_4074958 baseEnd_4074958 := by
    simpa [prefixWord, tailWord_4074958, baseEnd_4074958] using wordTrace_append hprefix tailTrace_4074958
  have hstable : (prefixWord ++ tailWord_4074958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074958).length < 2 ^ (prefixWord ++ tailWord_4074958).sum := by decide
  have hdescent : baseEnd_4074958 < baseStart_4074958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074968 : List Nat := [2, 1, 2, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_4074968 : Nat := 118140960795 + 4074968 * 2 ^ 59
def prefixEnd_4074968 : Nat := 4983230072969 + 3 ^ 40 * 4074968 * 2
def baseEnd_4074968 : Nat := 2092417235690717902659569

theorem tailTrace_4074968 : CollatzResearch.WordTrace tailWord_4074968 prefixEnd_4074968 2092417235690717902659569 := by
  unfold tailWord_4074968
  simp only [CollatzResearch.WordTrace]
  refine ⟨74313146550547179986084779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99084195400729573314779705 74313146550547179986084779)
  ·
    refine ⟨111469719825820769979127169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74313146550547179986084779 111469719825820769979127169)
    ·
      refine ⟨83602289869365577484345377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111469719825820769979127169 83602289869365577484345377)
      ·
        refine ⟨62701717402024183113259033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83602289869365577484345377 62701717402024183113259033)
        ·
          refine ⟨47026288051518137334944275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62701717402024183113259033 47026288051518137334944275)
          ·
            refine ⟨70539432077277206002416413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47026288051518137334944275 70539432077277206002416413)
            ·
              refine ⟨26452287028978952250906155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70539432077277206002416413 26452287028978952250906155)
              ·
                refine ⟨39678430543468428376359233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26452287028978952250906155 39678430543468428376359233)
                ·
                  refine ⟨29758822907601321282269425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39678430543468428376359233 29758822907601321282269425)
                  ·
                    refine ⟨22319117180700990961702069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29758822907601321282269425 22319117180700990961702069)
                    ·
                      refine ⟨2092417235690717902659569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22319117180700990961702069 2092417235690717902659569)
                      ·
                        rfl

theorem cell23_4074968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_4074968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074968 prefixEnd_4074968 := by exact prefixLift 4074968
  have htrace : WordTrace (prefixWord ++ tailWord_4074968) baseStart_4074968 baseEnd_4074968 := by
    simpa [prefixWord, tailWord_4074968, baseEnd_4074968] using wordTrace_append hprefix tailTrace_4074968
  have hstable : (prefixWord ++ tailWord_4074968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074968).length < 2 ^ (prefixWord ++ tailWord_4074968).sum := by decide
  have hdescent : baseEnd_4074968 < baseStart_4074968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074973 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_4074973 : Nat := 118140960795 + 4074973 * 2 ^ 59
def prefixEnd_4074973 : Nat := 4983230072969 + 3 ^ 40 * 4074973 * 2
def baseEnd_4074973 : Nat := 2092419803093990383097047

theorem tailTrace_4074973 : CollatzResearch.WordTrace tailWord_4074973 prefixEnd_4074973 2092419803093990383097047 := by
  unfold tailWord_4074973
  simp only [CollatzResearch.WordTrace]
  refine ⟨148626475466076245826101573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99084316977384163884067715 148626475466076245826101573)
  ·
    refine ⟨27867464149889296092394045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148626475466076245826101573 27867464149889296092394045)
    ·
      refine ⟨10450299056208486034647767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27867464149889296092394045 10450299056208486034647767)
      ·
        refine ⟨15675448584312729051971651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10450299056208486034647767 15675448584312729051971651)
        ·
          refine ⟨23513172876469093577957477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15675448584312729051971651 23513172876469093577957477)
          ·
            refine ⟨4408719914337955045867027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23513172876469093577957477 4408719914337955045867027)
            ·
              refine ⟨6613079871506932568800541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4408719914337955045867027 6613079871506932568800541)
              ·
                refine ⟨2479904951815099713300203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6613079871506932568800541 2479904951815099713300203)
                ·
                  refine ⟨3719857427722649569950305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2479904951815099713300203 3719857427722649569950305)
                  ·
                    refine ⟨2789893070791987177462729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3719857427722649569950305 2789893070791987177462729)
                    ·
                      refine ⟨2092419803093990383097047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789893070791987177462729 2092419803093990383097047)
                      ·
                        rfl

theorem cell23_4074973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_4074973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074973 prefixEnd_4074973 := by exact prefixLift 4074973
  have htrace : WordTrace (prefixWord ++ tailWord_4074973) baseStart_4074973 baseEnd_4074973 := by
    simpa [prefixWord, tailWord_4074973, baseEnd_4074973] using wordTrace_append hprefix tailTrace_4074973
  have hstable : (prefixWord ++ tailWord_4074973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074973).length < 2 ^ (prefixWord ++ tailWord_4074973).sum := by decide
  have hdescent : baseEnd_4074973 < baseStart_4074973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074988 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 2, 6]
def baseStart_4074988 : Nat := 118140960795 + 4074988 * 2 ^ 59
def prefixEnd_4074988 : Nat := 4983230072969 + 3 ^ 40 * 4074988 * 2
def baseEnd_4074988 : Nat := 697475835101269274803159

theorem tailTrace_4074988 : CollatzResearch.WordTrace tailWord_4074988 prefixEnd_4074988 697475835101269274803159 := by
  unfold tailWord_4074988
  simp only [CollatzResearch.WordTrace]
  refine ⟨74313511280510951693948809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99084681707347935591931745 74313511280510951693948809)
  ·
    refine ⟨55735133460383213770461607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74313511280510951693948809 55735133460383213770461607)
    ·
      refine ⟨83602700190574820655692411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55735133460383213770461607 83602700190574820655692411)
      ·
        refine ⟨125404050285862230983538617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83602700190574820655692411 125404050285862230983538617)
        ·
          refine ⟨94053037714396673237653963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125404050285862230983538617 94053037714396673237653963)
          ·
            refine ⟨141079556571595009856480945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94053037714396673237653963 141079556571595009856480945)
            ·
              refine ⟨105809667428696257392360709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141079556571595009856480945 105809667428696257392360709)
              ·
                refine ⟨19839312642880548261067633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105809667428696257392360709 19839312642880548261067633)
                ·
                  refine ⟨14879484482160411195800725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19839312642880548261067633 14879484482160411195800725)
                  ·
                    refine ⟨697475835101269274803159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14879484482160411195800725 697475835101269274803159)
                    ·
                      rfl

theorem cell23_4074988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 6].length) (baseStart_4074988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074988 prefixEnd_4074988 := by exact prefixLift 4074988
  have htrace : WordTrace (prefixWord ++ tailWord_4074988) baseStart_4074988 baseEnd_4074988 := by
    simpa [prefixWord, tailWord_4074988, baseEnd_4074988] using wordTrace_append hprefix tailTrace_4074988
  have hstable : (prefixWord ++ tailWord_4074988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074988).length < 2 ^ (prefixWord ++ tailWord_4074988).sum := by decide
  have hdescent : baseEnd_4074988 < baseStart_4074988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4074995 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 5, 4, 2]
def baseStart_4074995 : Nat := 118140960795 + 4074995 * 2 ^ 59
def prefixEnd_4074995 : Nat := 4983230072969 + 3 ^ 40 * 4074995 * 2
def baseEnd_4074995 : Nat := 2092431099668389297021945

theorem tailTrace_4074995 : CollatzResearch.WordTrace tailWord_4074995 prefixEnd_4074995 2092431099668389297021945 := by
  unfold tailWord_4074995
  simp only [CollatzResearch.WordTrace]
  refine ⟨148627277871996543583402439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99084851914664362388934959 148627277871996543583402439)
  ·
    refine ⟨222940916807994815375103659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148627277871996543583402439 222940916807994815375103659)
    ·
      refine ⟨334411375211992223062655489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222940916807994815375103659 334411375211992223062655489)
      ·
        refine ⟨250808531408994167296991617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334411375211992223062655489 250808531408994167296991617)
        ·
          refine ⟨188106398556745625472743713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250808531408994167296991617 188106398556745625472743713)
          ·
            refine ⟨141079798917559219104557785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188106398556745625472743713 141079798917559219104557785)
            ·
              refine ⟨105809849188169414328418339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141079798917559219104557785 105809849188169414328418339)
              ·
                refine ⟨158714773782254121492627509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105809849188169414328418339 158714773782254121492627509)
                ·
                  refine ⟨14879510042086323889933829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158714773782254121492627509 14879510042086323889933829)
                  ·
                    refine ⟨2789908132891185729362593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14879510042086323889933829 2789908132891185729362593)
                    ·
                      refine ⟨2092431099668389297021945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2789908132891185729362593 2092431099668389297021945)
                      ·
                        rfl

theorem cell23_4074995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 5, 4, 2].length) (baseStart_4074995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4074995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4074995 prefixEnd_4074995 := by exact prefixLift 4074995
  have htrace : WordTrace (prefixWord ++ tailWord_4074995) baseStart_4074995 baseEnd_4074995 := by
    simpa [prefixWord, tailWord_4074995, baseEnd_4074995] using wordTrace_append hprefix tailTrace_4074995
  have hstable : (prefixWord ++ tailWord_4074995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4074995).length < 2 ^ (prefixWord ++ tailWord_4074995).sum := by decide
  have hdescent : baseEnd_4074995 < baseStart_4074995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4074995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075015 : List Nat := [1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_4075015 : Nat := 118140960795 + 4075015 * 2 ^ 59
def prefixEnd_4075015 : Nat := 4983230072969 + 3 ^ 40 * 4075015 * 2
def baseEnd_4075015 : Nat := 2092441369281479218771853

theorem tailTrace_4075015 : CollatzResearch.WordTrace tailWord_4075015 prefixEnd_4075015 2092441369281479218771853 := by
  unfold tailWord_4075015
  simp only [CollatzResearch.WordTrace]
  refine ⟨148628007331924086999130499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99085338221282724666086999 148628007331924086999130499)
  ·
    refine ⟨222942010997886130498695749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148628007331924086999130499 222942010997886130498695749)
    ·
      refine ⟨41801627062103649468505453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222942010997886130498695749 41801627062103649468505453)
      ·
        refine ⟨15675610148288868550689545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41801627062103649468505453 15675610148288868550689545)
        ·
          refine ⟨11756707611216651413017159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15675610148288868550689545 11756707611216651413017159)
          ·
            refine ⟨17635061416824977119525739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11756707611216651413017159 17635061416824977119525739)
            ·
              refine ⟨26452592125237465679288609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17635061416824977119525739 26452592125237465679288609)
              ·
                refine ⟨19839444093928099259466457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26452592125237465679288609 19839444093928099259466457)
                ·
                  refine ⟨14879583070446074444599843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19839444093928099259466457 14879583070446074444599843)
                  ·
                    refine ⟨22319374605669111666899765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14879583070446074444599843 22319374605669111666899765)
                    ·
                      refine ⟨2092441369281479218771853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22319374605669111666899765 2092441369281479218771853)
                      ·
                        rfl

theorem cell23_4075015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_4075015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075015 prefixEnd_4075015 := by exact prefixLift 4075015
  have htrace : WordTrace (prefixWord ++ tailWord_4075015) baseStart_4075015 baseEnd_4075015 := by
    simpa [prefixWord, tailWord_4075015, baseEnd_4075015] using wordTrace_append hprefix tailTrace_4075015
  have hstable : (prefixWord ++ tailWord_4075015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075015).length < 2 ^ (prefixWord ++ tailWord_4075015).sum := by decide
  have hdescent : baseEnd_4075015 < baseStart_4075015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075045 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 3]
def baseStart_4075045 : Nat := 118140960795 + 4075045 * 2 ^ 59
def prefixEnd_4075045 : Nat := 4983230072969 + 3 ^ 40 * 4075045 * 2
def baseEnd_4075045 : Nat := 2092456773701114101396715

theorem tailTrace_4075045 : CollatzResearch.WordTrace tailWord_4075045 prefixEnd_4075045 2092456773701114101396715 := by
  unfold tailWord_4075045
  simp only [CollatzResearch.WordTrace]
  refine ⟨148629101521815402122722589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99086067681210268081815059 148629101521815402122722589)
  ·
    refine ⟨55735913070680775796020971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148629101521815402122722589 55735913070680775796020971)
    ·
      refine ⟨83603869606021163694031457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55735913070680775796020971 83603869606021163694031457)
      ·
        refine ⟨62702902204515872770523593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83603869606021163694031457 62702902204515872770523593)
        ·
          refine ⟨47027176653386904577892695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62702902204515872770523593 47027176653386904577892695)
          ·
            refine ⟨70540764980080356866839043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47027176653386904577892695 70540764980080356866839043)
            ·
              refine ⟨105811147470120535300258565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70540764980080356866839043 105811147470120535300258565)
              ·
                refine ⟨19839590150647600368798481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105811147470120535300258565 19839590150647600368798481)
                ·
                  refine ⟨14879692612985700276598861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19839590150647600368798481 14879692612985700276598861)
                  ·
                    refine ⟨5579884729869637603724573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14879692612985700276598861 5579884729869637603724573)
                    ·
                      refine ⟨2092456773701114101396715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579884729869637603724573 2092456773701114101396715)
                      ·
                        rfl

theorem cell23_4075045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_4075045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075045 prefixEnd_4075045 := by exact prefixLift 4075045
  have htrace : WordTrace (prefixWord ++ tailWord_4075045) baseStart_4075045 baseEnd_4075045 := by
    simpa [prefixWord, tailWord_4075045, baseEnd_4075045] using wordTrace_append hprefix tailTrace_4075045
  have hstable : (prefixWord ++ tailWord_4075045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075045).length < 2 ^ (prefixWord ++ tailWord_4075045).sum := by decide
  have hdescent : baseEnd_4075045 < baseStart_4075045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075122 : List Nat := [3, 2, 1, 2, 3, 1, 1, 2, 1, 4, 3]
def baseStart_4075122 : Nat := 118140960795 + 4075122 * 2 ^ 59
def prefixEnd_4075122 : Nat := 4983230072969 + 3 ^ 40 * 4075122 * 2
def baseEnd_4075122 : Nat := 2092496311711510300133861

theorem tailTrace_4075122 : CollatzResearch.WordTrace tailWord_4075122 prefixEnd_4075122 2092496311711510300133861 := by
  unfold tailWord_4075122
  simp only [CollatzResearch.WordTrace]
  refine ⟨37157977485634111068318905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99087939961690962848850413 37157977485634111068318905)
  ·
    refine ⟨27868483114225583301239179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37157977485634111068318905 27868483114225583301239179)
    ·
      refine ⟨41802724671338374951858769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27868483114225583301239179 41802724671338374951858769)
      ·
        refine ⟨31352043503503781213894077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41802724671338374951858769 31352043503503781213894077)
        ·
          refine ⟨11757016313813917955210279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31352043503503781213894077 11757016313813917955210279)
          ·
            refine ⟨17635524470720876932815419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757016313813917955210279 17635524470720876932815419)
            ·
              refine ⟨26453286706081315399223129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17635524470720876932815419 26453286706081315399223129)
              ·
                refine ⟨19839965029560986549417347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26453286706081315399223129 19839965029560986549417347)
                ·
                  refine ⟨29759947544341479824126021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19839965029560986549417347 29759947544341479824126021)
                  ·
                    refine ⟨5579990164564027467023629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29759947544341479824126021 5579990164564027467023629)
                    ·
                      refine ⟨2092496311711510300133861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5579990164564027467023629 2092496311711510300133861)
                      ·
                        rfl

theorem cell23_4075122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_4075122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075122 prefixEnd_4075122 := by exact prefixLift 4075122
  have htrace : WordTrace (prefixWord ++ tailWord_4075122) baseStart_4075122 baseEnd_4075122 := by
    simpa [prefixWord, tailWord_4075122, baseEnd_4075122] using wordTrace_append hprefix tailTrace_4075122
  have hstable : (prefixWord ++ tailWord_4075122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075122).length < 2 ^ (prefixWord ++ tailWord_4075122).sum := by decide
  have hdescent : baseEnd_4075122 < baseStart_4075122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075146 : List Nat := [3, 1, 2, 3, 2, 1, 3, 3, 1, 4]
def baseStart_4075146 : Nat := 118140960795 + 4075146 * 2 ^ 59
def prefixEnd_4075146 : Nat := 4983230072969 + 3 ^ 40 * 4075146 * 2
def baseEnd_4075146 : Nat := 697502878415739402077917

theorem tailTrace_4075146 : CollatzResearch.WordTrace tailWord_4075146 prefixEnd_4075146 697502878415739402077917 := by
  unfold tailWord_4075146
  simp only [CollatzResearch.WordTrace]
  refine ⟨37158196323612374093037323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99088523529632997581432861 37158196323612374093037323)
  ·
    refine ⟨55737294485418561139555985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37158196323612374093037323 55737294485418561139555985)
    ·
      refine ⟨41802970864063920854666989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55737294485418561139555985 41802970864063920854666989)
      ·
        refine ⟨15676114074023970320500121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41802970864063920854666989 15676114074023970320500121)
        ·
          refine ⟨11757085555517977740375091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15676114074023970320500121 11757085555517977740375091)
          ·
            refine ⟨17635628333276966610562637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757085555517977740375091 17635628333276966610562637)
            ·
              refine ⟨6613360624978862478960989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17635628333276966610562637 6613360624978862478960989)
              ·
                refine ⟨2480010234367073429610371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6613360624978862478960989 2480010234367073429610371)
                ·
                  refine ⟨3720015351550610144415557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480010234367073429610371 3720015351550610144415557)
                  ·
                    refine ⟨697502878415739402077917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3720015351550610144415557 697502878415739402077917)
                    ·
                      rfl

theorem cell23_4075146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_4075146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075146 prefixEnd_4075146 := by exact prefixLift 4075146
  have htrace : WordTrace (prefixWord ++ tailWord_4075146) baseStart_4075146 baseEnd_4075146 := by
    simpa [prefixWord, tailWord_4075146, baseEnd_4075146] using wordTrace_append hprefix tailTrace_4075146
  have hstable : (prefixWord ++ tailWord_4075146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075146).length < 2 ^ (prefixWord ++ tailWord_4075146).sum := by decide
  have hdescent : baseEnd_4075146 < baseStart_4075146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075152 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 5, 1, 3]
def baseStart_4075152 : Nat := 118140960795 + 4075152 * 2 ^ 59
def prefixEnd_4075152 : Nat := 4983230072969 + 3 ^ 40 * 4075152 * 2
def baseEnd_4075152 : Nat := 2092511716131145182758723

theorem tailTrace_4075152 : CollatzResearch.WordTrace tailWord_4075152 prefixEnd_4075152 2092511716131145182758723 := by
  unfold tailWord_4075152
  simp only [CollatzResearch.WordTrace]
  refine ⟨74316502066213879698433855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99088669421618506264578473 74316502066213879698433855)
  ·
    refine ⟨111474753099320819547650783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74316502066213879698433855 111474753099320819547650783)
    ·
      refine ⟨167212129648981229321476175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111474753099320819547650783 167212129648981229321476175)
      ·
        refine ⟨250818194473471843982214263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167212129648981229321476175 250818194473471843982214263)
        ·
          refine ⟨376227291710207765973321395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250818194473471843982214263 376227291710207765973321395)
          ·
            refine ⟨564340937565311648959982093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376227291710207765973321395 564340937565311648959982093)
            ·
              refine ⟨211627851586991868359993285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564340937565311648959982093 211627851586991868359993285)
              ·
                refine ⟨39680222172560975317498741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211627851586991868359993285 39680222172560975317498741)
                ·
                  refine ⟨3720020828677591436015507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39680222172560975317498741 3720020828677591436015507)
                  ·
                    refine ⟨5580031243016387154023261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720020828677591436015507 5580031243016387154023261)
                    ·
                      refine ⟨2092511716131145182758723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580031243016387154023261 2092511716131145182758723)
                      ·
                        rfl

theorem cell23_4075152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 5, 1, 3].length) (baseStart_4075152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075152 prefixEnd_4075152 := by exact prefixLift 4075152
  have htrace : WordTrace (prefixWord ++ tailWord_4075152) baseStart_4075152 baseEnd_4075152 := by
    simpa [prefixWord, tailWord_4075152, baseEnd_4075152] using wordTrace_append hprefix tailTrace_4075152
  have hstable : (prefixWord ++ tailWord_4075152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075152).length < 2 ^ (prefixWord ++ tailWord_4075152).sum := by decide
  have hdescent : baseEnd_4075152 < baseStart_4075152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075156 : List Nat := [2, 4, 2, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_4075156 : Nat := 118140960795 + 4075156 * 2 ^ 59
def prefixEnd_4075156 : Nat := 4983230072969 + 3 ^ 40 * 4075156 * 2
def baseEnd_4075156 : Nat := 2092513770053763167108705

theorem tailTrace_4075156 : CollatzResearch.WordTrace tailWord_4075156 prefixEnd_4075156 2092513770053763167108705 := by
  unfold tailWord_4075156
  simp only [CollatzResearch.WordTrace]
  refine ⟨74316575012206634040006661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99088766682942178720008881 74316575012206634040006661)
  ·
    refine ⟨13934357814788743882501249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74316575012206634040006661 13934357814788743882501249)
    ·
      refine ⟨10450768361091557911875937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13934357814788743882501249 10450768361091557911875937)
      ·
        refine ⟨7838076270818668433906953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10450768361091557911875937 7838076270818668433906953)
        ·
          refine ⟨5878557203114001325430215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7838076270818668433906953 5878557203114001325430215)
          ·
            refine ⟨8817835804671001988145323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5878557203114001325430215 8817835804671001988145323)
            ·
              refine ⟨13226753707006502982217985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8817835804671001988145323 13226753707006502982217985)
              ·
                refine ⟨9920065280254877236663489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13226753707006502982217985 9920065280254877236663489)
                ·
                  refine ⟨7440048960191157927497617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9920065280254877236663489 7440048960191157927497617)
                  ·
                    refine ⟨5580036720143368445623213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440048960191157927497617 5580036720143368445623213)
                    ·
                      refine ⟨2092513770053763167108705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580036720143368445623213 2092513770053763167108705)
                      ·
                        rfl

theorem cell23_4075156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_4075156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075156 prefixEnd_4075156 := by exact prefixLift 4075156
  have htrace : WordTrace (prefixWord ++ tailWord_4075156) baseStart_4075156 baseEnd_4075156 := by
    simpa [prefixWord, tailWord_4075156, baseEnd_4075156] using wordTrace_append hprefix tailTrace_4075156
  have hstable : (prefixWord ++ tailWord_4075156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075156).length < 2 ^ (prefixWord ++ tailWord_4075156).sum := by decide
  have hdescent : baseEnd_4075156 < baseStart_4075156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075165 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 7]
def baseStart_4075165 : Nat := 118140960795 + 4075165 * 2 ^ 59
def prefixEnd_4075165 : Nat := 4983230072969 + 3 ^ 40 * 4075165 * 2
def baseEnd_4075165 : Nat := 2092518391379653631896163

theorem tailTrace_4075165 : CollatzResearch.WordTrace tailWord_4075165 prefixEnd_4075165 2092518391379653631896163 := by
  unfold tailWord_4075165
  simp only [CollatzResearch.WordTrace]
  refine ⟨148633478281380662617090949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99088985520920441744727299 148633478281380662617090949)
  ·
    refine ⟨27868777177758874240704553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148633478281380662617090949 27868777177758874240704553)
    ·
      refine ⟨20901582883319155680528415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27868777177758874240704553 20901582883319155680528415)
      ·
        refine ⟨31352374324978733520792623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20901582883319155680528415 31352374324978733520792623)
        ·
          refine ⟨47028561487468100281188935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31352374324978733520792623 47028561487468100281188935)
          ·
            refine ⟨70542842231202150421783403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47028561487468100281188935 70542842231202150421783403)
            ·
              refine ⟨105814263346803225632675105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70542842231202150421783403 105814263346803225632675105)
              ·
                refine ⟨79360697510102419224506329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105814263346803225632675105 79360697510102419224506329)
                ·
                  refine ⟨59520523132576814418379747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79360697510102419224506329 59520523132576814418379747)
                  ·
                    refine ⟨89280784698865221627569621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59520523132576814418379747 89280784698865221627569621)
                    ·
                      refine ⟨2092518391379653631896163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89280784698865221627569621 2092518391379653631896163)
                      ·
                        rfl

theorem cell23_4075165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_4075165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075165 prefixEnd_4075165 := by exact prefixLift 4075165
  have htrace : WordTrace (prefixWord ++ tailWord_4075165) baseStart_4075165 baseEnd_4075165 := by
    simpa [prefixWord, tailWord_4075165, baseEnd_4075165] using wordTrace_append hprefix tailTrace_4075165
  have hstable : (prefixWord ++ tailWord_4075165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075165).length < 2 ^ (prefixWord ++ tailWord_4075165).sum := by decide
  have hdescent : baseEnd_4075165 < baseStart_4075165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075189 : List Nat := [1, 3, 3, 3, 2, 1, 1, 1, 3, 5]
def baseStart_4075189 : Nat := 118140960795 + 4075189 * 2 ^ 59
def prefixEnd_4075189 : Nat := 4983230072969 + 3 ^ 40 * 4075189 * 2
def baseEnd_4075189 : Nat := 697510238305120512665351

theorem tailTrace_4075189 : CollatzResearch.WordTrace tailWord_4075189 prefixEnd_4075189 697510238305120512665351 := by
  unfold tailWord_4075189
  simp only [CollatzResearch.WordTrace]
  refine ⟨148634353633293714715964621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99089569088862476477309747 148634353633293714715964621)
  ·
    refine ⟨55737882612485143018486733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148634353633293714715964621 55737882612485143018486733)
    ·
      refine ⟨20901705979681928631932525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55737882612485143018486733 20901705979681928631932525)
      ·
        refine ⟨7838139742380723236974697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20901705979681928631932525 7838139742380723236974697)
        ·
          refine ⟨5878604806785542427731023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7838139742380723236974697 5878604806785542427731023)
          ·
            refine ⟨8817907210178313641596535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5878604806785542427731023 8817907210178313641596535)
            ·
              refine ⟨13226860815267470462394803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8817907210178313641596535 13226860815267470462394803)
              ·
                refine ⟨19840291222901205693592205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13226860815267470462394803 19840291222901205693592205)
                ·
                  refine ⟨7440109208587952135097077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19840291222901205693592205 7440109208587952135097077)
                  ·
                    refine ⟨697510238305120512665351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7440109208587952135097077 697510238305120512665351)
                    ·
                      rfl

theorem cell23_4075189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 5].length) (baseStart_4075189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075189 prefixEnd_4075189 := by exact prefixLift 4075189
  have htrace : WordTrace (prefixWord ++ tailWord_4075189) baseStart_4075189 baseEnd_4075189 := by
    simpa [prefixWord, tailWord_4075189, baseEnd_4075189] using wordTrace_append hprefix tailTrace_4075189
  have hstable : (prefixWord ++ tailWord_4075189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075189).length < 2 ^ (prefixWord ++ tailWord_4075189).sum := by decide
  have hdescent : baseEnd_4075189 < baseStart_4075189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075192 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 2, 6, 2]
def baseStart_4075192 : Nat := 118140960795 + 4075192 * 2 ^ 59
def prefixEnd_4075192 : Nat := 4983230072969 + 3 ^ 40 * 4075192 * 2
def baseEnd_4075192 : Nat := 2092532255357325026258539

theorem tailTrace_4075192 : CollatzResearch.WordTrace tailWord_4075192 prefixEnd_4075192 2092532255357325026258539 := by
  unfold tailWord_4075192
  simp only [CollatzResearch.WordTrace]
  refine ⟨74317231526141423114161915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99089642034855230818882553 74317231526141423114161915)
  ·
    refine ⟨111475847289212134671242873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74317231526141423114161915 111475847289212134671242873)
    ·
      refine ⟨83606885466909101003432155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111475847289212134671242873 83606885466909101003432155)
      ·
        refine ⟨125410328200363651505148233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83606885466909101003432155 125410328200363651505148233)
        ·
          refine ⟨94057746150272738628861175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125410328200363651505148233 94057746150272738628861175)
          ·
            refine ⟨141086619225409107943291763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94057746150272738628861175 141086619225409107943291763)
            ·
              refine ⟨211629928838113661914937645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141086619225409107943291763 211629928838113661914937645)
              ·
                refine ⟨79361223314292623218101617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211629928838113661914937645 79361223314292623218101617)
                ·
                  refine ⟨59520917485719467413576213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79361223314292623218101617 59520917485719467413576213)
                  ·
                    refine ⟨2790043007143100035011385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59520917485719467413576213 2790043007143100035011385)
                    ·
                      refine ⟨2092532255357325026258539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790043007143100035011385 2092532255357325026258539)
                      ·
                        rfl

theorem cell23_4075192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 2, 6, 2].length) (baseStart_4075192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075192 prefixEnd_4075192 := by exact prefixLift 4075192
  have htrace : WordTrace (prefixWord ++ tailWord_4075192) baseStart_4075192 baseEnd_4075192 := by
    simpa [prefixWord, tailWord_4075192, baseEnd_4075192] using wordTrace_append hprefix tailTrace_4075192
  have hstable : (prefixWord ++ tailWord_4075192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075192).length < 2 ^ (prefixWord ++ tailWord_4075192).sum := by decide
  have hdescent : baseEnd_4075192 < baseStart_4075192 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075195 : List Nat := [1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5]
def baseStart_4075195 : Nat := 118140960795 + 4075195 * 2 ^ 59
def prefixEnd_4075195 : Nat := 4983230072969 + 3 ^ 40 * 4075195 * 2
def baseEnd_4075195 : Nat := 2092533795799288514521025

theorem tailTrace_4075195 : CollatzResearch.WordTrace tailWord_4075195 prefixEnd_4075195 2092533795799288514521025 := by
  unfold tailWord_4075195
  simp only [CollatzResearch.WordTrace]
  refine ⟨148634572471271977740683039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99089714980847985160455359 148634572471271977740683039)
  ·
    refine ⟨222951858706907966611024559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148634572471271977740683039 222951858706907966611024559)
    ·
      refine ⟨334427788060361949916536839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222951858706907966611024559 334427788060361949916536839)
      ·
        refine ⟨501641682090542924874805259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334427788060361949916536839 501641682090542924874805259)
        ·
          refine ⟨752462523135814387312207889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501641682090542924874805259 752462523135814387312207889)
          ·
            refine ⟨564346892351860790484155917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752462523135814387312207889 564346892351860790484155917)
            ·
              refine ⟨211630084631947796431558469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 564346892351860790484155917 211630084631947796431558469)
              ·
                refine ⟨39680640868490211830917213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211630084631947796431558469 39680640868490211830917213)
                ·
                  refine ⟨14880240325683829436593955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39680640868490211830917213 14880240325683829436593955)
                  ·
                    refine ⟨22320360488525744154890933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14880240325683829436593955 22320360488525744154890933)
                    ·
                      refine ⟨2092533795799288514521025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22320360488525744154890933 2092533795799288514521025)
                      ·
                        rfl

theorem cell23_4075195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_4075195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075195 prefixEnd_4075195 := by exact prefixLift 4075195
  have htrace : WordTrace (prefixWord ++ tailWord_4075195) baseStart_4075195 baseEnd_4075195 := by
    simpa [prefixWord, tailWord_4075195, baseEnd_4075195] using wordTrace_append hprefix tailTrace_4075195
  have hstable : (prefixWord ++ tailWord_4075195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075195).length < 2 ^ (prefixWord ++ tailWord_4075195).sum := by decide
  have hdescent : baseEnd_4075195 < baseStart_4075195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075196 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 2, 3, 2]
def baseStart_4075196 : Nat := 118140960795 + 4075196 * 2 ^ 59
def prefixEnd_4075196 : Nat := 4983230072969 + 3 ^ 40 * 4075196 * 2
def baseEnd_4075196 : Nat := 2092534309279943010608521

theorem tailTrace_4075196 : CollatzResearch.WordTrace tailWord_4075196 prefixEnd_4075196 2092534309279943010608521 := by
  unfold tailWord_4075196
  simp only [CollatzResearch.WordTrace]
  refine ⟨74317304472134177455734721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99089739296178903274312961 74317304472134177455734721)
  ·
    refine ⟨55737978354100633091801041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74317304472134177455734721 55737978354100633091801041)
    ·
      refine ⟨41803483765575474818850781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55737978354100633091801041 41803483765575474818850781)
      ·
        refine ⟨15676306412090803057069043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41803483765575474818850781 15676306412090803057069043)
        ·
          refine ⟨23514459618136204585603565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15676306412090803057069043 23514459618136204585603565)
          ·
            refine ⟨8817922356801076719601337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23514459618136204585603565 8817922356801076719601337)
            ·
              refine ⟨6613441767600807539701003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8817922356801076719601337 6613441767600807539701003)
              ·
                refine ⟨9920162651401211309551505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613441767600807539701003 9920162651401211309551505)
                ·
                  refine ⟨7440121988550908482163629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9920162651401211309551505 7440121988550908482163629)
                  ·
                    refine ⟨2790045745706590680811361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7440121988550908482163629 2790045745706590680811361)
                    ·
                      refine ⟨2092534309279943010608521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790045745706590680811361 2092534309279943010608521)
                      ·
                        rfl

theorem cell23_4075196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_4075196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075196 prefixEnd_4075196 := by exact prefixLift 4075196
  have htrace : WordTrace (prefixWord ++ tailWord_4075196) baseStart_4075196 baseEnd_4075196 := by
    simpa [prefixWord, tailWord_4075196, baseEnd_4075196] using wordTrace_append hprefix tailTrace_4075196
  have hstable : (prefixWord ++ tailWord_4075196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075196).length < 2 ^ (prefixWord ++ tailWord_4075196).sum := by decide
  have hdescent : baseEnd_4075196 < baseStart_4075196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075213 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 2, 3, 2]
def baseStart_4075213 : Nat := 118140960795 + 4075213 * 2 ^ 59
def prefixEnd_4075213 : Nat := 4983230072969 + 3 ^ 40 * 4075213 * 2
def baseEnd_4075213 : Nat := 2092543038451069444095943

theorem tailTrace_4075213 : CollatzResearch.WordTrace tailWord_4075213 prefixEnd_4075213 2092543038451069444095943 := by
  unfold tailWord_4075213
  simp only [CollatzResearch.WordTrace]
  refine ⟨148635228985206766814838293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99090152656804511209892195 148635228985206766814838293)
  ·
    refine ⟨6967276358681567194445545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 148635228985206766814838293 6967276358681567194445545)
    ·
      refine ⟨5225457269011175395834159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6967276358681567194445545 5225457269011175395834159)
      ·
        refine ⟨7838185903516763093751239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225457269011175395834159 7838185903516763093751239)
        ·
          refine ⟨11757278855275144640626859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838185903516763093751239 11757278855275144640626859)
          ·
            refine ⟨17635918282912716960940289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757278855275144640626859 17635918282912716960940289)
            ·
              refine ⟨13226938712184537720705217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17635918282912716960940289 13226938712184537720705217)
              ·
                refine ⟨9920204034138403290528913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13226938712184537720705217 9920204034138403290528913)
                ·
                  refine ⟨7440153025603802467896685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9920204034138403290528913 7440153025603802467896685)
                  ·
                    refine ⟨2790057384601425925461257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7440153025603802467896685 2790057384601425925461257)
                    ·
                      refine ⟨2092543038451069444095943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790057384601425925461257 2092543038451069444095943)
                      ·
                        rfl

theorem cell23_4075213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_4075213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075213 prefixEnd_4075213 := by exact prefixLift 4075213
  have htrace : WordTrace (prefixWord ++ tailWord_4075213) baseStart_4075213 baseEnd_4075213 := by
    simpa [prefixWord, tailWord_4075213, baseEnd_4075213] using wordTrace_append hprefix tailTrace_4075213
  have hstable : (prefixWord ++ tailWord_4075213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075213).length < 2 ^ (prefixWord ++ tailWord_4075213).sum := by decide
  have hdescent : baseEnd_4075213 < baseStart_4075213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075220 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4075220 : Nat := 118140960795 + 4075220 * 2 ^ 59
def prefixEnd_4075220 : Nat := 4983230072969 + 3 ^ 40 * 4075220 * 2
def baseEnd_4075220 : Nat := 2092546632815650916708411

theorem tailTrace_4075220 : CollatzResearch.WordTrace tailWord_4075220 prefixEnd_4075220 2092546632815650916708411 := by
  unfold tailWord_4075220
  simp only [CollatzResearch.WordTrace]
  refine ⟨74317742148090703505171557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99090322864120938006895409 74317742148090703505171557)
  ·
    refine ⟨13934576652767006907219667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74317742148090703505171557 13934576652767006907219667)
    ·
      refine ⟨20901864979150510360829501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13934576652767006907219667 20901864979150510360829501)
      ·
        refine ⟨7838199367181441385311063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20901864979150510360829501 7838199367181441385311063)
        ·
          refine ⟨11757299050772162077966595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838199367181441385311063 11757299050772162077966595)
          ·
            refine ⟨17635948576158243116949893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757299050772162077966595 17635948576158243116949893)
            ·
              refine ⟨3306740358029670584428105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17635948576158243116949893 3306740358029670584428105)
              ·
                refine ⟨2480055268522252938321079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306740358029670584428105 2480055268522252938321079)
                ·
                  refine ⟨3720082902783379407481619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480055268522252938321079 3720082902783379407481619)
                  ·
                    refine ⟨5580124354175069111222429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720082902783379407481619 5580124354175069111222429)
                    ·
                      refine ⟨2092546632815650916708411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580124354175069111222429 2092546632815650916708411)
                      ·
                        rfl

theorem cell23_4075220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4075220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075220 prefixEnd_4075220 := by exact prefixLift 4075220
  have htrace : WordTrace (prefixWord ++ tailWord_4075220) baseStart_4075220 baseEnd_4075220 := by
    simpa [prefixWord, tailWord_4075220, baseEnd_4075220] using wordTrace_append hprefix tailTrace_4075220
  have hstable : (prefixWord ++ tailWord_4075220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075220).length < 2 ^ (prefixWord ++ tailWord_4075220).sum := by decide
  have hdescent : baseEnd_4075220 < baseStart_4075220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075276 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 2, 1, 3]
def baseStart_4075276 : Nat := 118140960795 + 4075276 * 2 ^ 59
def prefixEnd_4075276 : Nat := 4983230072969 + 3 ^ 40 * 4075276 * 2
def baseEnd_4075276 : Nat := 2092575387732302697608153

theorem tailTrace_4075276 : CollatzResearch.WordTrace tailWord_4075276 prefixEnd_4075276 2092575387732302697608153 := by
  unfold tailWord_4075276
  simp only [CollatzResearch.WordTrace]
  refine ⟨74318763391989264287190841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99091684522652352382921121 74318763391989264287190841)
  ·
    refine ⟨55739072543991948215393131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74318763391989264287190841 55739072543991948215393131)
    ·
      refine ⟨83608608815987922323089697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55739072543991948215393131 83608608815987922323089697)
      ·
        refine ⟨62706456611990941742317273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83608608815987922323089697 62706456611990941742317273)
        ·
          refine ⟨47029842458993206306737955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62706456611990941742317273 47029842458993206306737955)
          ·
            refine ⟨70544763688489809460106933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47029842458993206306737955 70544763688489809460106933)
            ·
              refine ⟨6613571595795919636885025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70544763688489809460106933 6613571595795919636885025)
              ·
                refine ⟨4960178696846939727663769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6613571595795919636885025 4960178696846939727663769)
                ·
                  refine ⟨3720134022635204795747827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960178696846939727663769 3720134022635204795747827)
                  ·
                    refine ⟨5580201033952807193621741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720134022635204795747827 5580201033952807193621741)
                    ·
                      refine ⟨2092575387732302697608153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580201033952807193621741 2092575387732302697608153)
                      ·
                        rfl

theorem cell23_4075276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_4075276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075276 prefixEnd_4075276 := by exact prefixLift 4075276
  have htrace : WordTrace (prefixWord ++ tailWord_4075276) baseStart_4075276 baseEnd_4075276 := by
    simpa [prefixWord, tailWord_4075276, baseEnd_4075276] using wordTrace_append hprefix tailTrace_4075276
  have hstable : (prefixWord ++ tailWord_4075276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075276).length < 2 ^ (prefixWord ++ tailWord_4075276).sum := by decide
  have hdescent : baseEnd_4075276 < baseStart_4075276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075292 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_4075292 : Nat := 118140960795 + 4075292 * 2 ^ 59
def prefixEnd_4075292 : Nat := 4983230072969 + 3 ^ 40 * 4075292 * 2
def baseEnd_4075292 : Nat := 697527867807591545002693

theorem tailTrace_4075292 : CollatzResearch.WordTrace tailWord_4075292 prefixEnd_4075292 697527867807591545002693 := by
  unfold tailWord_4075292
  simp only [CollatzResearch.WordTrace]
  refine ⟨74319055175960281653482065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99092073567947042204642753 74319055175960281653482065)
  ·
    refine ⟨55739291381970211240111549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74319055175960281653482065 55739291381970211240111549)
    ·
      refine ⟨20902234268238829215041831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55739291381970211240111549 20902234268238829215041831)
      ·
        refine ⟨31353351402358243822562747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20902234268238829215041831 31353351402358243822562747)
        ·
          refine ⟨47030027103537365733844121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31353351402358243822562747 47030027103537365733844121)
          ·
            refine ⟨35272520327653024300383091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47030027103537365733844121 35272520327653024300383091)
            ·
              refine ⟨52908780491479536450574637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35272520327653024300383091 52908780491479536450574637)
              ·
                refine ⟨19840792684304826168965489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52908780491479536450574637 19840792684304826168965489)
                ·
                  refine ⟨14880594513228619626724117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19840792684304826168965489 14880594513228619626724117)
                  ·
                    refine ⟨697527867807591545002693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14880594513228619626724117 697527867807591545002693)
                    ·
                      rfl

theorem cell23_4075292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_4075292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075292 prefixEnd_4075292 := by exact prefixLift 4075292
  have htrace : WordTrace (prefixWord ++ tailWord_4075292) baseStart_4075292 baseEnd_4075292 := by
    simpa [prefixWord, tailWord_4075292, baseEnd_4075292] using wordTrace_append hprefix tailTrace_4075292
  have hstable : (prefixWord ++ tailWord_4075292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075292).length < 2 ^ (prefixWord ++ tailWord_4075292).sum := by decide
  have hdescent : baseEnd_4075292 < baseStart_4075292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075390 : List Nat := [4, 2, 3, 1, 1, 1, 4, 2, 5]
def baseStart_4075390 : Nat := 118140960795 + 4075390 * 2 ^ 59
def prefixEnd_4075390 : Nat := 4983230072969 + 3 ^ 40 * 4075390 * 2
def baseEnd_4075390 : Nat := 232514880502990583509181

theorem tailTrace_4075390 : CollatzResearch.WordTrace tailWord_4075390 prefixEnd_4075390 232514880502990583509181 := by
  unfold tailWord_4075390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18580210588195690755503953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99094456470377017362687749 18580210588195690755503953)
  ·
    refine ⟨13935157941146768066627965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18580210588195690755503953 13935157941146768066627965)
    ·
      refine ⟨5225684227930038024985487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13935157941146768066627965 5225684227930038024985487)
      ·
        refine ⟨7838526341895057037478231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225684227930038024985487 7838526341895057037478231)
        ·
          refine ⟨11757789512842585556217347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838526341895057037478231 11757789512842585556217347)
          ·
            refine ⟨17636684269263878334326021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11757789512842585556217347 17636684269263878334326021)
            ·
              refine ⟨3306878300486977187686129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17636684269263878334326021 3306878300486977187686129)
              ·
                refine ⟨2480158725365232890764597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3306878300486977187686129 2480158725365232890764597)
                ·
                  refine ⟨232514880502990583509181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2480158725365232890764597 232514880502990583509181)
                  ·
                    rfl

theorem cell23_4075390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_4075390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075390 prefixEnd_4075390 := by exact prefixLift 4075390
  have htrace : WordTrace (prefixWord ++ tailWord_4075390) baseStart_4075390 baseEnd_4075390 := by
    simpa [prefixWord, tailWord_4075390, baseEnd_4075390] using wordTrace_append hprefix tailTrace_4075390
  have hstable : (prefixWord ++ tailWord_4075390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075390).length < 2 ^ (prefixWord ++ tailWord_4075390).sum := by decide
  have hdescent : baseEnd_4075390 < baseStart_4075390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075392 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_4075392 : Nat := 118140960795 + 4075392 * 2 ^ 59
def prefixEnd_4075392 : Nat := 4983230072969 + 3 ^ 40 * 4075392 * 2
def baseEnd_4075392 : Nat := 2092634951488224243757619

theorem tailTrace_4075392 : CollatzResearch.WordTrace tailWord_4075392 prefixEnd_4075392 2092634951488224243757619 := by
  unfold tailWord_4075392
  simp only [CollatzResearch.WordTrace]
  refine ⟨74320878825779140192802215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99094505101038853590402953 74320878825779140192802215)
  ·
    refine ⟨111481318238668710289203323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74320878825779140192802215 111481318238668710289203323)
    ·
      refine ⟨167221977358003065433804985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111481318238668710289203323 167221977358003065433804985)
      ·
        refine ⟨125416483018502299075353739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167221977358003065433804985 125416483018502299075353739)
        ·
          refine ⟨188124724527753448613030609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125416483018502299075353739 188124724527753448613030609)
          ·
            refine ⟨141093543395815086459772957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188124724527753448613030609 141093543395815086459772957)
            ·
              refine ⟨52910078773430657422414859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141093543395815086459772957 52910078773430657422414859)
              ·
                refine ⟨79365118160145986133622289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52910078773430657422414859 79365118160145986133622289)
                ·
                  refine ⟨59523838620109489600216717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79365118160145986133622289 59523838620109489600216717)
                  ·
                    refine ⟨22321439482541058600081269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59523838620109489600216717 22321439482541058600081269)
                    ·
                      refine ⟨2092634951488224243757619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22321439482541058600081269 2092634951488224243757619)
                      ·
                        rfl

theorem cell23_4075392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_4075392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075392 prefixEnd_4075392 := by exact prefixLift 4075392
  have htrace : WordTrace (prefixWord ++ tailWord_4075392) baseStart_4075392 baseEnd_4075392 := by
    simpa [prefixWord, tailWord_4075392, baseEnd_4075392] using wordTrace_append hprefix tailTrace_4075392
  have hstable : (prefixWord ++ tailWord_4075392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075392).length < 2 ^ (prefixWord ++ tailWord_4075392).sum := by decide
  have hdescent : baseEnd_4075392 < baseStart_4075392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075409 : List Nat := [1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 3]
def baseStart_4075409 : Nat := 118140960795 + 4075409 * 2 ^ 59
def prefixEnd_4075409 : Nat := 4983230072969 + 3 ^ 40 * 4075409 * 2
def baseEnd_4075409 : Nat := 2092643680659350677245041

theorem tailTrace_4075409 : CollatzResearch.WordTrace tailWord_4075409 prefixEnd_4075409 2092643680659350677245041 := by
  unfold tailWord_4075409
  simp only [CollatzResearch.WordTrace]
  refine ⟨148642377692496692288973281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99094918461664461525982187 148642377692496692288973281)
  ·
    refine ⟨111481783269372519216729961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148642377692496692288973281 111481783269372519216729961)
    ·
      refine ⟨83611337452029389412547471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111481783269372519216729961 83611337452029389412547471)
      ·
        refine ⟨125417006178044084118821207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83611337452029389412547471 125417006178044084118821207)
        ·
          refine ⟨188125509267066126178231811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125417006178044084118821207 188125509267066126178231811)
          ·
            refine ⟨282188263900599189267347717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188125509267066126178231811 282188263900599189267347717)
            ·
              refine ⟨52910299481362347987627697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282188263900599189267347717 52910299481362347987627697)
              ·
                refine ⟨39682724611021760990720773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52910299481362347987627697 39682724611021760990720773)
                ·
                  refine ⟨7440510864566580185760145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39682724611021760990720773 7440510864566580185760145)
                  ·
                    refine ⟨5580383148424935139320109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440510864566580185760145 5580383148424935139320109)
                    ·
                      refine ⟨2092643680659350677245041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580383148424935139320109 2092643680659350677245041)
                      ·
                        rfl

theorem cell23_4075409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 3].length) (baseStart_4075409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075409 prefixEnd_4075409 := by exact prefixLift 4075409
  have htrace : WordTrace (prefixWord ++ tailWord_4075409) baseStart_4075409 baseEnd_4075409 := by
    simpa [prefixWord, tailWord_4075409, baseEnd_4075409] using wordTrace_append hprefix tailTrace_4075409
  have hstable : (prefixWord ++ tailWord_4075409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075409).length < 2 ^ (prefixWord ++ tailWord_4075409).sum := by decide
  have hdescent : baseEnd_4075409 < baseStart_4075409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075423 : List Nat := [1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 4]
def baseStart_4075423 : Nat := 118140960795 + 4075423 * 2 ^ 59
def prefixEnd_4075423 : Nat := 4983230072969 + 3 ^ 40 * 4075423 * 2
def baseEnd_4075423 : Nat := 2092650869388513622469977

theorem tailTrace_4075423 : CollatzResearch.WordTrace tailWord_4075423 prefixEnd_4075423 2092650869388513622469977 := by
  unfold tailWord_4075423
  simp only [CollatzResearch.WordTrace]
  refine ⟨148642888314445972679982923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99095258876297315119988615 148642888314445972679982923)
  ·
    refine ⟨222964332471668959019974385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148642888314445972679982923 222964332471668959019974385)
    ·
      refine ⟨167223249353751719264980789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222964332471668959019974385 167223249353751719264980789)
      ·
        refine ⟨15677179626914223681091949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167223249353751719264980789 15677179626914223681091949)
        ·
          refine ⟨5878942360092833880409481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15677179626914223681091949 5878942360092833880409481)
          ·
            refine ⟨4409206770069625410307111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5878942360092833880409481 4409206770069625410307111)
            ·
              refine ⟨6613810155104438115460667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409206770069625410307111 6613810155104438115460667)
              ·
                refine ⟨9920715232656657173191001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6613810155104438115460667 9920715232656657173191001)
                ·
                  refine ⟨7440536424492492879893251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9920715232656657173191001 7440536424492492879893251)
                  ·
                    refine ⟨11160804636738739319839877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7440536424492492879893251 11160804636738739319839877)
                    ·
                      refine ⟨2092650869388513622469977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11160804636738739319839877 2092650869388513622469977)
                      ·
                        rfl

theorem cell23_4075423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_4075423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075423 prefixEnd_4075423 := by exact prefixLift 4075423
  have htrace : WordTrace (prefixWord ++ tailWord_4075423) baseStart_4075423 baseEnd_4075423 := by
    simpa [prefixWord, tailWord_4075423, baseEnd_4075423] using wordTrace_append hprefix tailTrace_4075423
  have hstable : (prefixWord ++ tailWord_4075423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075423).length < 2 ^ (prefixWord ++ tailWord_4075423).sum := by decide
  have hdescent : baseEnd_4075423 < baseStart_4075423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075466 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_4075466 : Nat := 118140960795 + 4075466 * 2 ^ 59
def prefixEnd_4075466 : Nat := 4983230072969 + 3 ^ 40 * 4075466 * 2
def baseEnd_4075466 : Nat := 2092672949056656954232279

theorem tailTrace_4075466 : CollatzResearch.WordTrace tailWord_4075466 prefixEnd_4075466 2092672949056656954232279 := by
  unfold tailWord_4075466
  simp only [CollatzResearch.WordTrace]
  refine ⟨37161114163322547755949563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99096304435526794015865501 37161114163322547755949563)
  ·
    refine ⟨55741671244983821633924345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37161114163322547755949563 55741671244983821633924345)
    ·
      refine ⟨41806253433737866225443259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55741671244983821633924345 41806253433737866225443259)
      ·
        refine ⟨62709380150606799338164889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41806253433737866225443259 62709380150606799338164889)
        ·
          refine ⟨47032035112955099503623667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62709380150606799338164889 47032035112955099503623667)
          ·
            refine ⟨70548052669432649255435501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47032035112955099503623667 70548052669432649255435501)
            ·
              refine ⟨26455519751037243470788313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70548052669432649255435501 26455519751037243470788313)
              ·
                refine ⟨19841639813277932603091235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26455519751037243470788313 19841639813277932603091235)
                ·
                  refine ⟨29762459719916898904636853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19841639813277932603091235 29762459719916898904636853)
                  ·
                    refine ⟨2790230598742209272309705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29762459719916898904636853 2790230598742209272309705)
                    ·
                      refine ⟨2092672949056656954232279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790230598742209272309705 2092672949056656954232279)
                      ·
                        rfl

theorem cell23_4075466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_4075466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075466 prefixEnd_4075466 := by exact prefixLift 4075466
  have htrace : WordTrace (prefixWord ++ tailWord_4075466) baseStart_4075466 baseEnd_4075466 := by
    simpa [prefixWord, tailWord_4075466, baseEnd_4075466] using wordTrace_append hprefix tailTrace_4075466
  have hstable : (prefixWord ++ tailWord_4075466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075466).length < 2 ^ (prefixWord ++ tailWord_4075466).sum := by decide
  have hdescent : baseEnd_4075466 < baseStart_4075466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075489 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 1, 6]
def baseStart_4075489 : Nat := 118140960795 + 4075489 * 2 ^ 59
def prefixEnd_4075489 : Nat := 4983230072969 + 3 ^ 40 * 4075489 * 2
def baseEnd_4075489 : Nat := 697561586370570121414891

theorem tailTrace_4075489 : CollatzResearch.WordTrace tailWord_4075489 prefixEnd_4075489 697561586370570121414891 := by
  unfold tailWord_4075489
  simp only [CollatzResearch.WordTrace]
  refine ⟨148645295532206865951885521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99096863688137910634590347 148645295532206865951885521)
  ·
    refine ⟨111483971649155149463914141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148645295532206865951885521 111483971649155149463914141)
    ·
      refine ⟨41806489368433181048967803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111483971649155149463914141 41806489368433181048967803)
      ·
        refine ⟨62709734052649771573451705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41806489368433181048967803 62709734052649771573451705)
        ·
          refine ⟨47032300539487328680088779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62709734052649771573451705 47032300539487328680088779)
          ·
            refine ⟨70548450809230993020133169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47032300539487328680088779 70548450809230993020133169)
            ·
              refine ⟨52911338106923244765099877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70548450809230993020133169 52911338106923244765099877)
              ·
                refine ⟨9920875895048108393456227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52911338106923244765099877 9920875895048108393456227)
                ·
                  refine ⟨14881313842572162590184341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9920875895048108393456227 14881313842572162590184341)
                  ·
                    refine ⟨697561586370570121414891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14881313842572162590184341 697561586370570121414891)
                    ·
                      rfl

theorem cell23_4075489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_4075489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075489 prefixEnd_4075489 := by exact prefixLift 4075489
  have htrace : WordTrace (prefixWord ++ tailWord_4075489) baseStart_4075489 baseEnd_4075489 := by
    simpa [prefixWord, tailWord_4075489, baseEnd_4075489] using wordTrace_append hprefix tailTrace_4075489
  have hstable : (prefixWord ++ tailWord_4075489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075489).length < 2 ^ (prefixWord ++ tailWord_4075489).sum := by decide
  have hdescent : baseEnd_4075489 < baseStart_4075489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075516 : List Nat := [2, 2, 2, 1, 2, 2, 2, 2, 3, 2, 3]
def baseStart_4075516 : Nat := 118140960795 + 4075516 * 2 ^ 59
def prefixEnd_4075516 : Nat := 4983230072969 + 3 ^ 40 * 4075516 * 2
def baseEnd_4075516 : Nat := 2092698623089381758607049

theorem tailTrace_4075516 : CollatzResearch.WordTrace tailWord_4075516 prefixEnd_4075516 2092698623089381758607049 := by
  unfold tailWord_4075516
  simp only [CollatzResearch.WordTrace]
  refine ⟨74323140151554524781559201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99097520202072699708745601 74323140151554524781559201)
  ·
    refine ⟨55742355113665893586169401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74323140151554524781559201 55742355113665893586169401)
    ·
      refine ⟨41806766335249420189627051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55742355113665893586169401 41806766335249420189627051)
      ·
        refine ⟨62710149502874130284440577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41806766335249420189627051 62710149502874130284440577)
        ·
          refine ⟨47032612127155597713330433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62710149502874130284440577 47032612127155597713330433)
          ·
            refine ⟨35274459095366698284997825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47032612127155597713330433 35274459095366698284997825)
            ·
              refine ⟨26455844321525023713748369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35274459095366698284997825 26455844321525023713748369)
              ·
                refine ⟨19841883241143767785311277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26455844321525023713748369 19841883241143767785311277)
                ·
                  refine ⟨7440706215428912919491729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19841883241143767785311277 7440706215428912919491729)
                  ·
                    refine ⟨5580529661571684689618797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7440706215428912919491729 5580529661571684689618797)
                    ·
                      refine ⟨2092698623089381758607049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580529661571684689618797 2092698623089381758607049)
                      ·
                        rfl

theorem cell23_4075516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 2, 3, 2, 3].length) (baseStart_4075516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075516 prefixEnd_4075516 := by exact prefixLift 4075516
  have htrace : WordTrace (prefixWord ++ tailWord_4075516) baseStart_4075516 baseEnd_4075516 := by
    simpa [prefixWord, tailWord_4075516, baseEnd_4075516] using wordTrace_append hprefix tailTrace_4075516
  have hstable : (prefixWord ++ tailWord_4075516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075516).length < 2 ^ (prefixWord ++ tailWord_4075516).sum := by decide
  have hdescent : baseEnd_4075516 < baseStart_4075516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075530 : List Nat := [3, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_4075530 : Nat := 118140960795 + 4075530 * 2 ^ 59
def prefixEnd_4075530 : Nat := 4983230072969 + 3 ^ 40 * 4075530 * 2
def baseEnd_4075530 : Nat := 2092705811818544703831985

theorem tailTrace_4075530 : CollatzResearch.WordTrace tailWord_4075530 prefixEnd_4075530 2092705811818544703831985 := by
  unfold tailWord_4075530
  simp only [CollatzResearch.WordTrace]
  refine ⟨37161697731264582488532011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99097860616705553302752029 37161697731264582488532011)
  ·
    refine ⟨55742546596896873732798017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37161697731264582488532011 55742546596896873732798017)
    ·
      refine ⟨41806909947672655299598513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55742546596896873732798017 41806909947672655299598513)
      ·
        refine ⟨31355182460754491474698885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41806909947672655299598513 31355182460754491474698885)
        ·
          refine ⟨5879096711391467151506041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31355182460754491474698885 5879096711391467151506041)
          ·
            refine ⟨4409322533543600363629531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879096711391467151506041 4409322533543600363629531)
            ·
              refine ⟨6613983800315400545444297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4409322533543600363629531 6613983800315400545444297)
              ·
                refine ⟨4960487850236550409083223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6613983800315400545444297 4960487850236550409083223)
                ·
                  refine ⟨7440731775354825613624835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960487850236550409083223 7440731775354825613624835)
                  ·
                    refine ⟨11161097663032238420437253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7440731775354825613624835 11161097663032238420437253)
                    ·
                      refine ⟨2092705811818544703831985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11161097663032238420437253 2092705811818544703831985)
                      ·
                        rfl

theorem cell23_4075530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_4075530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075530 prefixEnd_4075530 := by exact prefixLift 4075530
  have htrace : WordTrace (prefixWord ++ tailWord_4075530) baseStart_4075530 baseEnd_4075530 := by
    simpa [prefixWord, tailWord_4075530, baseEnd_4075530] using wordTrace_append hprefix tailTrace_4075530
  have hstable : (prefixWord ++ tailWord_4075530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075530).length < 2 ^ (prefixWord ++ tailWord_4075530).sum := by decide
  have hdescent : baseEnd_4075530 < baseStart_4075530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075540 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 1, 6]
def baseStart_4075540 : Nat := 118140960795 + 4075540 * 2 ^ 59
def prefixEnd_4075540 : Nat := 4983230072969 + 3 ^ 40 * 4075540 * 2
def baseEnd_4075540 : Nat := 697570315541696554902313

theorem tailTrace_4075540 : CollatzResearch.WordTrace tailWord_4075540 prefixEnd_4075540 697570315541696554902313 := by
  unfold tailWord_4075540
  simp only [CollatzResearch.WordTrace]
  refine ⟨74323577827511050830996037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99098103770014734441328049 74323577827511050830996037)
  ·
    refine ⟨13935670842658322030811757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74323577827511050830996037 13935670842658322030811757)
    ·
      refine ⟨5225876565996870761554409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13935670842658322030811757 5225876565996870761554409)
      ·
        refine ⟨3919407424497653071165807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5225876565996870761554409 3919407424497653071165807)
        ·
          refine ⟨5879111136746479606748711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919407424497653071165807 5879111136746479606748711)
          ·
            refine ⟨8818666705119719410123067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879111136746479606748711 8818666705119719410123067)
            ·
              refine ⟨13228000057679579115184601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8818666705119719410123067 13228000057679579115184601)
              ·
                refine ⟨9921000043259684336388451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13228000057679579115184601 9921000043259684336388451)
                ·
                  refine ⟨14881500064889526504582677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921000043259684336388451 14881500064889526504582677)
                  ·
                    refine ⟨697570315541696554902313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14881500064889526504582677 697570315541696554902313)
                    ·
                      rfl

theorem cell23_4075540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_4075540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075540 prefixEnd_4075540 := by exact prefixLift 4075540
  have htrace : WordTrace (prefixWord ++ tailWord_4075540) baseStart_4075540 baseEnd_4075540 := by
    simpa [prefixWord, tailWord_4075540, baseEnd_4075540] using wordTrace_append hprefix tailTrace_4075540
  have hstable : (prefixWord ++ tailWord_4075540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075540).length < 2 ^ (prefixWord ++ tailWord_4075540).sum := by decide
  have hdescent : baseEnd_4075540 < baseStart_4075540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075543 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 4]
def baseStart_4075543 : Nat := 118140960795 + 4075543 * 2 ^ 59
def prefixEnd_4075543 : Nat := 4983230072969 + 3 ^ 40 * 4075543 * 2
def baseEnd_4075543 : Nat := 2092712487067053152969425

theorem tailTrace_4075543 : CollatzResearch.WordTrace tailWord_4075543 prefixEnd_4075543 2092712487067053152969425 := by
  unfold tailWord_4075543
  simp only [CollatzResearch.WordTrace]
  refine ⟨148647265074011233174351283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99098176716007488782900855 148647265074011233174351283)
  ·
    refine ⟨222970897611016849761526925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148647265074011233174351283 222970897611016849761526925)
    ·
      refine ⟨83614086604131318660572597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222970897611016849761526925 83614086604131318660572597)
      ·
        refine ⟨7838820619137311124428681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83614086604131318660572597 7838820619137311124428681)
        ·
          refine ⟨5879115464352983343321511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7838820619137311124428681 5879115464352983343321511)
          ·
            refine ⟨8818673196529475014982267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879115464352983343321511 8818673196529475014982267)
            ·
              refine ⟨13228009794794212522473401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8818673196529475014982267 13228009794794212522473401)
              ·
                refine ⟨9921007346095659391855051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13228009794794212522473401 9921007346095659391855051)
                ·
                  refine ⟨14881511019143489087782577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921007346095659391855051 14881511019143489087782577)
                  ·
                    refine ⟨11161133264357616815836933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14881511019143489087782577 11161133264357616815836933)
                    ·
                      refine ⟨2092712487067053152969425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11161133264357616815836933 2092712487067053152969425)
                      ·
                        rfl

theorem cell23_4075543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_4075543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075543 prefixEnd_4075543 := by exact prefixLift 4075543
  have htrace : WordTrace (prefixWord ++ tailWord_4075543) baseStart_4075543 baseEnd_4075543 := by
    simpa [prefixWord, tailWord_4075543, baseEnd_4075543] using wordTrace_append hprefix tailTrace_4075543
  have hstable : (prefixWord ++ tailWord_4075543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075543).length < 2 ^ (prefixWord ++ tailWord_4075543).sum := by decide
  have hdescent : baseEnd_4075543 < baseStart_4075543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075546 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_4075546 : Nat := 118140960795 + 4075546 * 2 ^ 59
def prefixEnd_4075546 : Nat := 4983230072969 + 3 ^ 40 * 4075546 * 2
def baseEnd_4075546 : Nat := 2092714027509016641231911

theorem tailTrace_4075546 : CollatzResearch.WordTrace tailWord_4075546 prefixEnd_4075546 2092714027509016641231911 := by
  unfold tailWord_4075546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37161843623250091171677623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99098249662000243124473661 37161843623250091171677623)
  ·
    refine ⟨55742765434875136757516435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37161843623250091171677623 55742765434875136757516435)
    ·
      refine ⟨83614148152312705136274653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55742765434875136757516435 83614148152312705136274653)
      ·
        refine ⟨31355305557117264426102995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83614148152312705136274653 31355305557117264426102995)
        ·
          refine ⟨47032958335675896639154493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31355305557117264426102995 47032958335675896639154493)
          ·
            refine ⟨17637359375878461239682935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47032958335675896639154493 17637359375878461239682935)
            ·
              refine ⟨26456039063817691859524403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17637359375878461239682935 26456039063817691859524403)
              ·
                refine ⟨39684058595726537789286605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26456039063817691859524403 39684058595726537789286605)
                ·
                  refine ⟨14881521973397451670982477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39684058595726537789286605 14881521973397451670982477)
                  ·
                    refine ⟨5580570740024044376618429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14881521973397451670982477 5580570740024044376618429)
                    ·
                      refine ⟨2092714027509016641231911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580570740024044376618429 2092714027509016641231911)
                      ·
                        rfl

theorem cell23_4075546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_4075546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075546 prefixEnd_4075546 := by exact prefixLift 4075546
  have htrace : WordTrace (prefixWord ++ tailWord_4075546) baseStart_4075546 baseEnd_4075546 := by
    simpa [prefixWord, tailWord_4075546, baseEnd_4075546] using wordTrace_append hprefix tailTrace_4075546
  have hstable : (prefixWord ++ tailWord_4075546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075546).length < 2 ^ (prefixWord ++ tailWord_4075546).sum := by decide
  have hdescent : baseEnd_4075546 < baseStart_4075546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075566 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 2, 7]
def baseStart_4075566 : Nat := 118140960795 + 4075566 * 2 ^ 59
def prefixEnd_4075566 : Nat := 4983230072969 + 3 ^ 40 * 4075566 * 2
def baseEnd_4075566 : Nat := 697574765707368854327273

theorem tailTrace_4075566 : CollatzResearch.WordTrace tailWord_4075566 prefixEnd_4075566 697574765707368854327273 := by
  unfold tailWord_4075566
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581012994115988512804819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99098735968618605401625701 18581012994115988512804819)
  ·
    refine ⟨27871519491173982769207229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18581012994115988512804819 27871519491173982769207229)
    ·
      refine ⟨10451819809190243538452711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27871519491173982769207229 10451819809190243538452711)
      ·
        refine ⟨15677729713785365307679067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10451819809190243538452711 15677729713785365307679067)
        ·
          refine ⟨23516594570678047961518601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15677729713785365307679067 23516594570678047961518601)
          ·
            refine ⟨17637445928008535971138951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23516594570678047961518601 17637445928008535971138951)
            ·
              refine ⟨26456168892012803956708427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17637445928008535971138951 26456168892012803956708427)
              ·
                refine ⟨39684253338019205935062641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26456168892012803956708427 39684253338019205935062641)
                ·
                  refine ⟨29763190003514404451296981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39684253338019205935062641 29763190003514404451296981)
                  ·
                    refine ⟨697574765707368854327273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29763190003514404451296981 697574765707368854327273)
                    ·
                      rfl

theorem cell23_4075566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_4075566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075566 prefixEnd_4075566 := by exact prefixLift 4075566
  have htrace : WordTrace (prefixWord ++ tailWord_4075566) baseStart_4075566 baseEnd_4075566 := by
    simpa [prefixWord, tailWord_4075566, baseEnd_4075566] using wordTrace_append hprefix tailTrace_4075566
  have hstable : (prefixWord ++ tailWord_4075566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075566).length < 2 ^ (prefixWord ++ tailWord_4075566).sum := by decide
  have hdescent : baseEnd_4075566 < baseStart_4075566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075573 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 3, 3, 2]
def baseStart_4075573 : Nat := 118140960795 + 4075573 * 2 ^ 59
def prefixEnd_4075573 : Nat := 4983230072969 + 3 ^ 40 * 4075573 * 2
def baseEnd_4075573 : Nat := 2092727891486688035594287

theorem tailTrace_4075573 : CollatzResearch.WordTrace tailWord_4075573 prefixEnd_4075573 2092727891486688035594287 := by
  unfold tailWord_4075573
  simp only [CollatzResearch.WordTrace]
  refine ⟨148648359263902548297943373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99098906175935032198628915 148648359263902548297943373)
  ·
    refine ⟨55743134723963455611728765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148648359263902548297943373 55743134723963455611728765)
    ·
      refine ⟨20903675521486295854398287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55743134723963455611728765 20903675521486295854398287)
      ·
        refine ⟨31355513282229443781597431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20903675521486295854398287 31355513282229443781597431)
        ·
          refine ⟨47033269923344165672396147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31355513282229443781597431 47033269923344165672396147)
          ·
            refine ⟨70549904885016248508594221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47033269923344165672396147 70549904885016248508594221)
            ·
              refine ⟨26456214331881093190722833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70549904885016248508594221 26456214331881093190722833)
              ·
                refine ⟨19842160748910819893042125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26456214331881093190722833 19842160748910819893042125)
                ·
                  refine ⟨7440810280841557459890797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19842160748910819893042125 7440810280841557459890797)
                  ·
                    refine ⟨2790303855315584047459049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7440810280841557459890797 2790303855315584047459049)
                    ·
                      refine ⟨2092727891486688035594287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790303855315584047459049 2092727891486688035594287)
                      ·
                        rfl

theorem cell23_4075573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_4075573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075573 prefixEnd_4075573 := by exact prefixLift 4075573
  have htrace : WordTrace (prefixWord ++ tailWord_4075573) baseStart_4075573 baseEnd_4075573 := by
    simpa [prefixWord, tailWord_4075573, baseEnd_4075573] using wordTrace_append hprefix tailTrace_4075573
  have hstable : (prefixWord ++ tailWord_4075573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075573).length < 2 ^ (prefixWord ++ tailWord_4075573).sum := by decide
  have hdescent : baseEnd_4075573 < baseStart_4075573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075579 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 2, 6]
def baseStart_4075579 : Nat := 118140960795 + 4075579 * 2 ^ 59
def prefixEnd_4075579 : Nat := 4983230072969 + 3 ^ 40 * 4075579 * 2
def baseEnd_4075579 : Nat := 697576990790205004039753

theorem tailTrace_4075579 : CollatzResearch.WordTrace tailWord_4075579 prefixEnd_4075579 697576990790205004039753 := by
  unfold tailWord_4075579
  simp only [CollatzResearch.WordTrace]
  refine ⟨148648578101880811322661791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99099052067920540881774527 148648578101880811322661791)
  ·
    refine ⟨222972867152821216983992687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148648578101880811322661791 222972867152821216983992687)
    ·
      refine ⟨334459300729231825475989031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222972867152821216983992687 334459300729231825475989031)
      ·
        refine ⟨501688951093847738213983547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334459300729231825475989031 501688951093847738213983547)
        ·
          refine ⟨752533426640771607320975321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501688951093847738213983547 752533426640771607320975321)
          ·
            refine ⟨564400069980578705490731491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752533426640771607320975321 564400069980578705490731491)
            ·
              refine ⟨846600104970868058236097237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564400069980578705490731491 846600104970868058236097237)
              ·
                refine ⟨19842189960254720114908529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 846600104970868058236097237 19842189960254720114908529)
                ·
                  refine ⟨14881642470191040086181397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19842189960254720114908529 14881642470191040086181397)
                  ·
                    refine ⟨697576990790205004039753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14881642470191040086181397 697576990790205004039753)
                    ·
                      rfl

theorem cell23_4075579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 2, 6].length) (baseStart_4075579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075579 prefixEnd_4075579 := by exact prefixLift 4075579
  have htrace : WordTrace (prefixWord ++ tailWord_4075579) baseStart_4075579 baseEnd_4075579 := by
    simpa [prefixWord, tailWord_4075579, baseEnd_4075579] using wordTrace_append hprefix tailTrace_4075579
  have hstable : (prefixWord ++ tailWord_4075579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075579).length < 2 ^ (prefixWord ++ tailWord_4075579).sum := by decide
  have hdescent : baseEnd_4075579 < baseStart_4075579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075609 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 9]
def baseStart_4075609 : Nat := 118140960795 + 4075609 * 2 ^ 59
def prefixEnd_4075609 : Nat := 4983230072969 + 3 ^ 40 * 4075609 * 2
def baseEnd_4075609 : Nat := 232527375198916654971569

theorem tailTrace_4075609 : CollatzResearch.WordTrace tailWord_4075609 prefixEnd_4075609 232527375198916654971569 := by
  unfold tailWord_4075609
  simp only [CollatzResearch.WordTrace]
  refine ⟨148649672291772126446253881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99099781527848084297502587 148649672291772126446253881)
  ·
    refine ⟨111487254218829094834690411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148649672291772126446253881 111487254218829094834690411)
    ·
      refine ⟨167230881328243642252035617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111487254218829094834690411 167230881328243642252035617)
      ·
        refine ⟨125423160996182731689026713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167230881328243642252035617 125423160996182731689026713)
        ·
          refine ⟨94067370747137048766770035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125423160996182731689026713 94067370747137048766770035)
          ·
            refine ⟨141101056120705573150155053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94067370747137048766770035 141101056120705573150155053)
            ·
              refine ⟨52912896045264589931308145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141101056120705573150155053 52912896045264589931308145)
              ·
                refine ⟨39684672033948442448481109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52912896045264589931308145 39684672033948442448481109)
                ·
                  refine ⟨232527375198916654971569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 39684672033948442448481109 232527375198916654971569)
                  ·
                    rfl

theorem cell23_4075609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 9].length) (baseStart_4075609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075609 prefixEnd_4075609 := by exact prefixLift 4075609
  have htrace : WordTrace (prefixWord ++ tailWord_4075609) baseStart_4075609 baseEnd_4075609 := by
    simpa [prefixWord, tailWord_4075609, baseEnd_4075609] using wordTrace_append hprefix tailTrace_4075609
  have hstable : (prefixWord ++ tailWord_4075609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075609).length < 2 ^ (prefixWord ++ tailWord_4075609).sum := by decide
  have hdescent : baseEnd_4075609 < baseStart_4075609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075613 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 2, 6]
def baseStart_4075613 : Nat := 118140960795 + 4075613 * 2 ^ 59
def prefixEnd_4075613 : Nat := 4983230072969 + 3 ^ 40 * 4075613 * 2
def baseEnd_4075613 : Nat := 697582810237622626364701

theorem tailTrace_4075613 : CollatzResearch.WordTrace tailWord_4075613 prefixEnd_4075613 697582810237622626364701 := by
  unfold tailWord_4075613
  simp only [CollatzResearch.WordTrace]
  refine ⟨148649818183757635129399493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99099878789171756752932995 148649818183757635129399493)
  ·
    refine ⟨27871840909454556586762405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148649818183757635129399493 27871840909454556586762405)
    ·
      refine ⟨5225970170522729360017951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27871840909454556586762405 5225970170522729360017951)
      ·
        refine ⟨7838955255784094040026927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225970170522729360017951 7838955255784094040026927)
        ·
          refine ⟨11758432883676141060040391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838955255784094040026927 11758432883676141060040391)
          ·
            refine ⟨17637649325514211590060587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11758432883676141060040391 17637649325514211590060587)
            ·
              refine ⟨26456473988271317385090881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17637649325514211590060587 26456473988271317385090881)
              ·
                refine ⟨19842355491203488038818161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26456473988271317385090881 19842355491203488038818161)
                ·
                  refine ⟨14881766618402616029113621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19842355491203488038818161 14881766618402616029113621)
                  ·
                    refine ⟨697582810237622626364701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14881766618402616029113621 697582810237622626364701)
                    ·
                      rfl

theorem cell23_4075613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_4075613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075613 prefixEnd_4075613 := by exact prefixLift 4075613
  have htrace : WordTrace (prefixWord ++ tailWord_4075613) baseStart_4075613 baseEnd_4075613 := by
    simpa [prefixWord, tailWord_4075613, baseEnd_4075613] using wordTrace_append hprefix tailTrace_4075613
  have hstable : (prefixWord ++ tailWord_4075613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075613).length < 2 ^ (prefixWord ++ tailWord_4075613).sum := by decide
  have hdescent : baseEnd_4075613 < baseStart_4075613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075614 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_4075614 : Nat := 118140960795 + 4075614 * 2 ^ 59
def prefixEnd_4075614 : Nat := 4983230072969 + 3 ^ 40 * 4075614 * 2
def baseEnd_4075614 : Nat := 2092748944193522375181599

theorem tailTrace_4075614 : CollatzResearch.WordTrace tailWord_4075614 prefixEnd_4075614 2092748944193522375181599 := by
  unfold tailWord_4075614
  simp only [CollatzResearch.WordTrace]
  refine ⟨18581231832094251537523237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99099903104502674866790597 18581231832094251537523237)
  ·
    refine ⟨3483980968517672163285607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18581231832094251537523237 3483980968517672163285607)
    ·
      refine ⟨5225971452776508244928411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3483980968517672163285607 5225971452776508244928411)
      ·
        refine ⟨7838957179164762367392617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225971452776508244928411 7838957179164762367392617)
        ·
          refine ⟨5879217884373571775544463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7838957179164762367392617 5879217884373571775544463)
          ·
            refine ⟨8818826826560357663316695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879217884373571775544463 8818826826560357663316695)
            ·
              refine ⟨13228240239840536494975043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8818826826560357663316695 13228240239840536494975043)
              ·
                refine ⟨19842360359760804742462565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228240239840536494975043 19842360359760804742462565)
                ·
                  refine ⟨3720442567455150889211731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19842360359760804742462565 3720442567455150889211731)
                  ·
                    refine ⟨5580663851182726333817597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720442567455150889211731 5580663851182726333817597)
                    ·
                      refine ⟨2092748944193522375181599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580663851182726333817597 2092748944193522375181599)
                      ·
                        rfl

theorem cell23_4075614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_4075614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075614 prefixEnd_4075614 := by exact prefixLift 4075614
  have htrace : WordTrace (prefixWord ++ tailWord_4075614) baseStart_4075614 baseEnd_4075614 := by
    simpa [prefixWord, tailWord_4075614, baseEnd_4075614] using wordTrace_append hprefix tailTrace_4075614
  have hstable : (prefixWord ++ tailWord_4075614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075614).length < 2 ^ (prefixWord ++ tailWord_4075614).sum := by decide
  have hdescent : baseEnd_4075614 < baseStart_4075614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075616 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_4075616 : Nat := 118140960795 + 4075616 * 2 ^ 59
def prefixEnd_4075616 : Nat := 4983230072969 + 3 ^ 40 * 4075616 * 2
def baseEnd_4075616 : Nat := 2092749971154831367356589

theorem tailTrace_4075616 : CollatzResearch.WordTrace tailWord_4075616 prefixEnd_4075616 2092749971154831367356589 := by
  unfold tailWord_4075616
  simp only [CollatzResearch.WordTrace]
  refine ⟨74324963801373383320879351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99099951735164511094505801 74324963801373383320879351)
  ·
    refine ⟨111487445702060074981319027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74324963801373383320879351 111487445702060074981319027)
    ·
      refine ⟨167231168553090112471978541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111487445702060074981319027 167231168553090112471978541)
      ·
        refine ⟨62711688207408792176991953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167231168553090112471978541 62711688207408792176991953)
        ·
          refine ⟨47033766155556594132743965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62711688207408792176991953 47033766155556594132743965)
          ·
            refine ⟨17637662308333722799778987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47033766155556594132743965 17637662308333722799778987)
            ·
              refine ⟨26456493462500584199668481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17637662308333722799778987 26456493462500584199668481)
              ·
                refine ⟨19842370096875438149751361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26456493462500584199668481 19842370096875438149751361)
                ·
                  refine ⟨14881777572656578612313521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19842370096875438149751361 14881777572656578612313521)
                  ·
                    refine ⟨11161333179492433959235141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14881777572656578612313521 11161333179492433959235141)
                    ·
                      refine ⟨2092749971154831367356589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11161333179492433959235141 2092749971154831367356589)
                      ·
                        rfl

theorem cell23_4075616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_4075616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075616 prefixEnd_4075616 := by exact prefixLift 4075616
  have htrace : WordTrace (prefixWord ++ tailWord_4075616) baseStart_4075616 baseEnd_4075616 := by
    simpa [prefixWord, tailWord_4075616, baseEnd_4075616] using wordTrace_append hprefix tailTrace_4075616
  have hstable : (prefixWord ++ tailWord_4075616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075616).length < 2 ^ (prefixWord ++ tailWord_4075616).sum := by decide
  have hdescent : baseEnd_4075616 < baseStart_4075616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075706 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_4075706 : Nat := 118140960795 + 4075706 * 2 ^ 59
def prefixEnd_4075706 : Nat := 4983230072969 + 3 ^ 40 * 4075706 * 2
def baseEnd_4075706 : Nat := 2092796184413736015231175

theorem tailTrace_4075706 : CollatzResearch.WordTrace tailWord_4075706 prefixEnd_4075706 2092796184413736015231175 := by
  unfold tailWord_4075706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37163302543105178003133743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99102140114947141341689981 37163302543105178003133743)
  ·
    refine ⟨55744953814657767004700615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37163302543105178003133743 55744953814657767004700615)
    ·
      refine ⟨83617430721986650507050923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55744953814657767004700615 83617430721986650507050923)
      ·
        refine ⟨125426146082979975760576385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83617430721986650507050923 125426146082979975760576385)
        ·
          refine ⟨94069609562234981820432289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125426146082979975760576385 94069609562234981820432289)
          ·
            refine ⟨70552207171676236365324217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94069609562234981820432289 70552207171676236365324217)
            ·
              refine ⟨52914155378757177273993163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70552207171676236365324217 52914155378757177273993163)
              ·
                refine ⟨79371233068135765910989745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52914155378757177273993163 79371233068135765910989745)
                ·
                  refine ⟨59528424801101824433242309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79371233068135765910989745 59528424801101824433242309)
                  ·
                    refine ⟨11161579650206592081232933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 59528424801101824433242309 11161579650206592081232933)
                    ·
                      refine ⟨2092796184413736015231175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11161579650206592081232933 2092796184413736015231175)
                      ·
                        rfl

theorem cell23_4075706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_4075706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075706 prefixEnd_4075706 := by exact prefixLift 4075706
  have htrace : WordTrace (prefixWord ++ tailWord_4075706) baseStart_4075706 baseEnd_4075706 := by
    simpa [prefixWord, tailWord_4075706, baseEnd_4075706] using wordTrace_append hprefix tailTrace_4075706
  have hstable : (prefixWord ++ tailWord_4075706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075706).length < 2 ^ (prefixWord ++ tailWord_4075706).sum := by decide
  have hdescent : baseEnd_4075706 < baseStart_4075706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075720 : List Nat := [2, 1, 3, 1, 2, 1, 1, 7, 1, 4]
def baseStart_4075720 : Nat := 118140960795 + 4075720 * 2 ^ 59
def prefixEnd_4075720 : Nat := 4983230072969 + 3 ^ 40 * 4075720 * 2
def baseEnd_4075720 : Nat := 697601124380966320152037

theorem tailTrace_4075720 : CollatzResearch.WordTrace tailWord_4075720 prefixEnd_4075720 697601124380966320152037 := by
  unfold tailWord_4075720
  simp only [CollatzResearch.WordTrace]
  refine ⟨74326860397184996201772307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99102480529579994935696409 74326860397184996201772307)
  ·
    refine ⟨111490290595777494302658461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74326860397184996201772307 111490290595777494302658461)
    ·
      refine ⟨41808858973416560363496923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111490290595777494302658461 41808858973416560363496923)
      ·
        refine ⟨62713288460124840545245385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41808858973416560363496923 62713288460124840545245385)
        ·
          refine ⟨47034966345093630408934039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62713288460124840545245385 47034966345093630408934039)
          ·
            refine ⟨70552449517640445613401059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47034966345093630408934039 70552449517640445613401059)
            ·
              refine ⟨105828674276460668420101589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70552449517640445613401059 105828674276460668420101589)
              ·
                refine ⟨2480359553354546916096131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105828674276460668420101589 2480359553354546916096131)
                ·
                  refine ⟨3720539330031820374144197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480359553354546916096131 3720539330031820374144197)
                  ·
                    refine ⟨697601124380966320152037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3720539330031820374144197 697601124380966320152037)
                    ·
                      rfl

theorem cell23_4075720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 7, 1, 4].length) (baseStart_4075720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075720 prefixEnd_4075720 := by exact prefixLift 4075720
  have htrace : WordTrace (prefixWord ++ tailWord_4075720) baseStart_4075720 baseEnd_4075720 := by
    simpa [prefixWord, tailWord_4075720, baseEnd_4075720] using wordTrace_append hprefix tailTrace_4075720
  have hstable : (prefixWord ++ tailWord_4075720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075720).length < 2 ^ (prefixWord ++ tailWord_4075720).sum := by decide
  have hdescent : baseEnd_4075720 < baseStart_4075720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075730 : List Nat := [3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 3]
def baseStart_4075730 : Nat := 118140960795 + 4075730 * 2 ^ 59
def prefixEnd_4075730 : Nat := 4983230072969 + 3 ^ 40 * 4075730 * 2
def baseEnd_4075730 : Nat := 2092808507949443921331065

theorem tailTrace_4075730 : CollatzResearch.WordTrace tailWord_4075730 prefixEnd_4075730 2092808507949443921331065 := by
  unfold tailWord_4075730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37163521381083441027852161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99102723682889176074272429 37163521381083441027852161)
  ·
    refine ⟨27872641035812580770889121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37163521381083441027852161 27872641035812580770889121)
    ·
      refine ⟨20904480776859435578166841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27872641035812580770889121 20904480776859435578166841)
      ·
        refine ⟨15678360582644576683625131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20904480776859435578166841 15678360582644576683625131)
        ·
          refine ⟨23517540873966865025437697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15678360582644576683625131 23517540873966865025437697)
          ·
            refine ⟨17638155655475148769078273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23517540873966865025437697 17638155655475148769078273)
            ·
              refine ⟨13228616741606361576808705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17638155655475148769078273 13228616741606361576808705)
              ·
                refine ⟨9921462556204771182606529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13228616741606361576808705 9921462556204771182606529)
                ·
                  refine ⟨7441096917153578386954897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9921462556204771182606529 7441096917153578386954897)
                  ·
                    refine ⟨5580822687865183790216173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7441096917153578386954897 5580822687865183790216173)
                    ·
                      refine ⟨2092808507949443921331065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580822687865183790216173 2092808507949443921331065)
                      ·
                        rfl

theorem cell23_4075730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_4075730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075730 prefixEnd_4075730 := by exact prefixLift 4075730
  have htrace : WordTrace (prefixWord ++ tailWord_4075730) baseStart_4075730 baseEnd_4075730 := by
    simpa [prefixWord, tailWord_4075730, baseEnd_4075730] using wordTrace_append hprefix tailTrace_4075730
  have hstable : (prefixWord ++ tailWord_4075730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075730).length < 2 ^ (prefixWord ++ tailWord_4075730).sum := by decide
  have hdescent : baseEnd_4075730 < baseStart_4075730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075737 : List Nat := [1, 2, 1, 2, 3, 1, 6, 2, 1, 4]
def baseStart_4075737 : Nat := 118140960795 + 4075737 * 2 ^ 59
def prefixEnd_4075737 : Nat := 4983230072969 + 3 ^ 40 * 4075737 * 2
def baseEnd_4075737 : Nat := 697604034104675131314511

theorem tailTrace_4075737 : CollatzResearch.WordTrace tailWord_4075737 prefixEnd_4075737 697604034104675131314511 := by
  unfold tailWord_4075737
  simp only [CollatzResearch.WordTrace]
  refine ⟨148654340835308404306913465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99102893890205602871275643 148654340835308404306913465)
  ·
    refine ⟨111490755626481303230185099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148654340835308404306913465 111490755626481303230185099)
    ·
      refine ⟨167236133439721954845277649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111490755626481303230185099 167236133439721954845277649)
      ·
        refine ⟨125427100079791466133958237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167236133439721954845277649 125427100079791466133958237)
        ·
          refine ⟨47035162529921799800234339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125427100079791466133958237 47035162529921799800234339)
          ·
            refine ⟨70552743794882699700351509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47035162529921799800234339 70552743794882699700351509)
            ·
              refine ⟨3307159865385126548453977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70552743794882699700351509 3307159865385126548453977)
              ·
                refine ⟨2480369899038844911340483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3307159865385126548453977 2480369899038844911340483)
                ·
                  refine ⟨3720554848558267367010725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480369899038844911340483 3720554848558267367010725)
                  ·
                    refine ⟨697604034104675131314511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3720554848558267367010725 697604034104675131314511)
                    ·
                      rfl

theorem cell23_4075737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 6, 2, 1, 4].length) (baseStart_4075737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075737 prefixEnd_4075737 := by exact prefixLift 4075737
  have htrace : WordTrace (prefixWord ++ tailWord_4075737) baseStart_4075737 baseEnd_4075737 := by
    simpa [prefixWord, tailWord_4075737, baseEnd_4075737] using wordTrace_append hprefix tailTrace_4075737
  have hstable : (prefixWord ++ tailWord_4075737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075737).length < 2 ^ (prefixWord ++ tailWord_4075737).sum := by decide
  have hdescent : baseEnd_4075737 < baseStart_4075737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075753 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 3, 5, 2]
def baseStart_4075753 : Nat := 118140960795 + 4075753 * 2 ^ 59
def prefixEnd_4075753 : Nat := 4983230072969 + 3 ^ 40 * 4075753 * 2
def baseEnd_4075753 : Nat := 2092820318004497331343459

theorem tailTrace_4075753 : CollatzResearch.WordTrace tailWord_4075753 prefixEnd_4075753 2092820318004497331343459 := by
  unfold tailWord_4075753
  simp only [CollatzResearch.WordTrace]
  refine ⟨148654924403250439039495913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99103282935500292692997275 148654924403250439039495913)
  ·
    refine ⟨111491193302437829279621935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148654924403250439039495913 111491193302437829279621935)
    ·
      refine ⟨167236789953656743919432903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111491193302437829279621935 167236789953656743919432903)
      ·
        refine ⟨250855184930485115879149355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167236789953656743919432903 250855184930485115879149355)
        ·
          refine ⟨376282777395727673818724033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250855184930485115879149355 376282777395727673818724033)
          ·
            refine ⟨282212083046795755364043025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 376282777395727673818724033 282212083046795755364043025)
            ·
              refine ⟨211659062285096816523032269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282212083046795755364043025 211659062285096816523032269)
              ·
                refine ⟨79372148356911306196137101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211659062285096816523032269 79372148356911306196137101)
                ·
                  refine ⟨29764555633841739823551413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79372148356911306196137101 29764555633841739823551413)
                  ·
                    refine ⟨2790427090672663108457945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29764555633841739823551413 2790427090672663108457945)
                    ·
                      refine ⟨2092820318004497331343459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790427090672663108457945 2092820318004497331343459)
                      ·
                        rfl

theorem cell23_4075753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 5, 2].length) (baseStart_4075753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075753 prefixEnd_4075753 := by exact prefixLift 4075753
  have htrace : WordTrace (prefixWord ++ tailWord_4075753) baseStart_4075753 baseEnd_4075753 := by
    simpa [prefixWord, tailWord_4075753, baseEnd_4075753] using wordTrace_append hprefix tailTrace_4075753
  have hstable : (prefixWord ++ tailWord_4075753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075753).length < 2 ^ (prefixWord ++ tailWord_4075753).sum := by decide
  have hdescent : baseEnd_4075753 < baseStart_4075753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075756 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_4075756 : Nat := 118140960795 + 4075756 * 2 ^ 59
def prefixEnd_4075756 : Nat := 4983230072969 + 3 ^ 40 * 4075756 * 2
def baseEnd_4075756 : Nat := 2092821858446460819605945

theorem tailTrace_4075756 : CollatzResearch.WordTrace tailWord_4075756 prefixEnd_4075756 2092821858446460819605945 := by
  unfold tailWord_4075756
  simp only [CollatzResearch.WordTrace]
  refine ⟨74327516911119785275927561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99103355881493047034570081 74327516911119785275927561)
  ·
    refine ⟨55745637683339838956945671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74327516911119785275927561 55745637683339838956945671)
    ·
      refine ⟨83618456525009758435418507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55745637683339838956945671 83618456525009758435418507)
      ·
        refine ⟨125427684787514637653127761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83618456525009758435418507 125427684787514637653127761)
        ·
          refine ⟨94070763590635978239845821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125427684787514637653127761 94070763590635978239845821)
          ·
            refine ⟨35276536346488491839942183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94070763590635978239845821 35276536346488491839942183)
            ·
              refine ⟨52914804519732737759913275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35276536346488491839942183 52914804519732737759913275)
              ·
                refine ⟨79372206779599106639869913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52914804519732737759913275 79372206779599106639869913)
                ·
                  refine ⟨59529155084699329979902435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79372206779599106639869913 59529155084699329979902435)
                  ·
                    refine ⟨89293732627048994969853653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 59529155084699329979902435 89293732627048994969853653)
                    ·
                      refine ⟨2092821858446460819605945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89293732627048994969853653 2092821858446460819605945)
                      ·
                        rfl

theorem cell23_4075756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_4075756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075756 prefixEnd_4075756 := by exact prefixLift 4075756
  have htrace : WordTrace (prefixWord ++ tailWord_4075756) baseStart_4075756 baseEnd_4075756 := by
    simpa [prefixWord, tailWord_4075756, baseEnd_4075756] using wordTrace_append hprefix tailTrace_4075756
  have hstable : (prefixWord ++ tailWord_4075756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075756).length < 2 ^ (prefixWord ++ tailWord_4075756).sum := by decide
  have hdescent : baseEnd_4075756 < baseStart_4075756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075763 : List Nat := [1, 1, 1, 2, 2, 4, 2, 4, 1, 5]
def baseStart_4075763 : Nat := 118140960795 + 4075763 * 2 ^ 59
def prefixEnd_4075763 : Nat := 4983230072969 + 3 ^ 40 * 4075763 * 2
def baseEnd_4075763 : Nat := 697608484270347430739471

theorem tailTrace_4075763 : CollatzResearch.WordTrace tailWord_4075763 prefixEnd_4075763 697608484270347430739471 := by
  unfold tailWord_4075763
  simp only [CollatzResearch.WordTrace]
  refine ⟨148655289133214210747359943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99103526088809473831573295 148655289133214210747359943)
  ·
    refine ⟨222982933699821316121039915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148655289133214210747359943 222982933699821316121039915)
    ·
      refine ⟨334474400549731974181559873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222982933699821316121039915 334474400549731974181559873)
      ·
        refine ⟨250855800412298980636169905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334474400549731974181559873 250855800412298980636169905)
        ·
          refine ⟨188141850309224235477127429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250855800412298980636169905 188141850309224235477127429)
          ·
            refine ⟨35276596932979544151961393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188141850309224235477127429 35276596932979544151961393)
            ·
              refine ⟨26457447699734658113971045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35276596932979544151961393 26457447699734658113971045)
              ·
                refine ⟨4960771443700248396369571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26457447699734658113971045 4960771443700248396369571)
                ·
                  refine ⟨7441157165550372594554357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960771443700248396369571 7441157165550372594554357)
                  ·
                    refine ⟨697608484270347430739471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7441157165550372594554357 697608484270347430739471)
                    ·
                      rfl

theorem cell23_4075763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 5].length) (baseStart_4075763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075763 prefixEnd_4075763 := by exact prefixLift 4075763
  have htrace : WordTrace (prefixWord ++ tailWord_4075763) baseStart_4075763 baseEnd_4075763 := by
    simpa [prefixWord, tailWord_4075763, baseEnd_4075763] using wordTrace_append hprefix tailTrace_4075763
  have hstable : (prefixWord ++ tailWord_4075763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075763).length < 2 ^ (prefixWord ++ tailWord_4075763).sum := by decide
  have hdescent : baseEnd_4075763 < baseStart_4075763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075770 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2]
def baseStart_4075770 : Nat := 118140960795 + 4075770 * 2 ^ 59
def prefixEnd_4075770 : Nat := 4983230072969 + 3 ^ 40 * 4075770 * 2
def baseEnd_4075770 : Nat := 2092829047175623764830881

theorem tailTrace_4075770 : CollatzResearch.WordTrace tailWord_4075770 prefixEnd_4075770 2092829047175623764830881 := by
  unfold tailWord_4075770
  simp only [CollatzResearch.WordTrace]
  refine ⟨37163886111047212735716191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99103696296125900628576509 37163886111047212735716191)
  ·
    refine ⟨55745829166570819103574287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37163886111047212735716191 55745829166570819103574287)
    ·
      refine ⟨83618743749856228655361431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55745829166570819103574287 83618743749856228655361431)
      ·
        refine ⟨125428115624784342983042147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83618743749856228655361431 125428115624784342983042147)
        ·
          refine ⟨188142173437176514474563221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125428115624784342983042147 188142173437176514474563221)
          ·
            refine ⟨8819164379867649115995151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188142173437176514474563221 8819164379867649115995151)
            ·
              refine ⟨13228746569801473673992727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819164379867649115995151 13228746569801473673992727)
              ·
                refine ⟨19843119854702210510989091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13228746569801473673992727 19843119854702210510989091)
                ·
                  refine ⟨29764679782053315766483637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19843119854702210510989091 29764679782053315766483637)
                  ·
                    refine ⟨2790438729567498353107841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29764679782053315766483637 2790438729567498353107841)
                    ·
                      refine ⟨2092829047175623764830881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790438729567498353107841 2092829047175623764830881)
                      ·
                        rfl

theorem cell23_4075770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_4075770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075770 prefixEnd_4075770 := by exact prefixLift 4075770
  have htrace : WordTrace (prefixWord ++ tailWord_4075770) baseStart_4075770 baseEnd_4075770 := by
    simpa [prefixWord, tailWord_4075770, baseEnd_4075770] using wordTrace_append hprefix tailTrace_4075770
  have hstable : (prefixWord ++ tailWord_4075770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075770).length < 2 ^ (prefixWord ++ tailWord_4075770).sum := by decide
  have hdescent : baseEnd_4075770 < baseStart_4075770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075803 : List Nat := [1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 3]
def baseStart_4075803 : Nat := 118140960795 + 4075803 * 2 ^ 59
def prefixEnd_4075803 : Nat := 4983230072969 + 3 ^ 40 * 4075803 * 2
def baseEnd_4075803 : Nat := 2092845992037222135718229

theorem tailTrace_4075803 : CollatzResearch.WordTrace tailWord_4075803 prefixEnd_4075803 2092845992037222135718229 := by
  unfold tailWord_4075803
  simp only [CollatzResearch.WordTrace]
  refine ⟨148656748053069297578816063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99104498702046198385877375 148656748053069297578816063)
  ·
    refine ⟨222985122079603946368224095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148656748053069297578816063 222985122079603946368224095)
    ·
      refine ⟨334477683119405919552336143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222985122079603946368224095 334477683119405919552336143)
      ·
        refine ⟨501716524679108879328504215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334477683119405919552336143 501716524679108879328504215)
        ·
          refine ⟨752574787018663318992756323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501716524679108879328504215 752574787018663318992756323)
          ·
            refine ⟨1128862180527994978489134485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 752574787018663318992756323 1128862180527994978489134485)
            ·
              refine ⟨52915414712249764616678179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1128862180527994978489134485 52915414712249764616678179)
              ·
                refine ⟨79373122068374646925017269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52915414712249764616678179 79373122068374646925017269)
                ·
                  refine ⟨7441230193910123149220369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79373122068374646925017269 7441230193910123149220369)
                  ·
                    refine ⟨5580922645432592361915277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7441230193910123149220369 5580922645432592361915277)
                    ·
                      refine ⟨2092845992037222135718229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580922645432592361915277 2092845992037222135718229)
                      ·
                        rfl

theorem cell23_4075803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 3].length) (baseStart_4075803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075803 prefixEnd_4075803 := by exact prefixLift 4075803
  have htrace : WordTrace (prefixWord ++ tailWord_4075803) baseStart_4075803 baseEnd_4075803 := by
    simpa [prefixWord, tailWord_4075803, baseEnd_4075803] using wordTrace_append hprefix tailTrace_4075803
  have hstable : (prefixWord ++ tailWord_4075803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075803).length < 2 ^ (prefixWord ++ tailWord_4075803).sum := by decide
  have hdescent : baseEnd_4075803 < baseStart_4075803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075810 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 1, 6]
def baseStart_4075810 : Nat := 118140960795 + 4075810 * 2 ^ 59
def prefixEnd_4075810 : Nat := 4983230072969 + 3 ^ 40 * 4075810 * 2
def baseEnd_4075810 : Nat := 697616528800601202776899

theorem tailTrace_4075810 : CollatzResearch.WordTrace tailWord_4075810 prefixEnd_4075810 697616528800601202776899 := by
  unfold tailWord_4075810
  simp only [CollatzResearch.WordTrace]
  refine ⟨37164250841010984443580221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99104668909362625182880589 37164250841010984443580221)
  ·
    refine ⟨13936594065379119166342583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37164250841010984443580221 13936594065379119166342583)
    ·
      refine ⟨20904891098068678749513875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13936594065379119166342583 20904891098068678749513875)
      ·
        refine ⟨31357336647103018124270813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20904891098068678749513875 31357336647103018124270813)
        ·
          refine ⟨11759001242663631796601555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31357336647103018124270813 11759001242663631796601555)
          ·
            refine ⟨17638501863995447694902333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11759001242663631796601555 17638501863995447694902333)
            ·
              refine ⟨6614438198998292885588375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17638501863995447694902333 6614438198998292885588375)
              ·
                refine ⟨9921657298497439328382563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6614438198998292885588375 9921657298497439328382563)
                ·
                  refine ⟨14882485947746158992573845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9921657298497439328382563 14882485947746158992573845)
                  ·
                    refine ⟨697616528800601202776899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14882485947746158992573845 697616528800601202776899)
                    ·
                      rfl

theorem cell23_4075810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_4075810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075810 prefixEnd_4075810 := by exact prefixLift 4075810
  have htrace : WordTrace (prefixWord ++ tailWord_4075810) baseStart_4075810 baseEnd_4075810 := by
    simpa [prefixWord, tailWord_4075810, baseEnd_4075810] using wordTrace_append hprefix tailTrace_4075810
  have hstable : (prefixWord ++ tailWord_4075810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075810).length < 2 ^ (prefixWord ++ tailWord_4075810).sum := by decide
  have hdescent : baseEnd_4075810 < baseStart_4075810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075820 : List Nat := [2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 3]
def baseStart_4075820 : Nat := 118140960795 + 4075820 * 2 ^ 59
def prefixEnd_4075820 : Nat := 4983230072969 + 3 ^ 40 * 4075820 * 2
def baseEnd_4075820 : Nat := 2092854721208348569205651

theorem tailTrace_4075820 : CollatzResearch.WordTrace tailWord_4075820 prefixEnd_4075820 2092854721208348569205651 := by
  unfold tailWord_4075820
  simp only [CollatzResearch.WordTrace]
  refine ⟨74328684047003854741092457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99104912062671806321456609 74328684047003854741092457)
  ·
    refine ⟨55746513035252891055819343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74328684047003854741092457 55746513035252891055819343)
    ·
      refine ⟨83619769552879336583729015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55746513035252891055819343 83619769552879336583729015)
      ·
        refine ⟨125429654329319004875593523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83619769552879336583729015 125429654329319004875593523)
        ·
          refine ⟨188144481493978507313390285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125429654329319004875593523 188144481493978507313390285)
          ·
            refine ⟨70554180560241940242521357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188144481493978507313390285 70554180560241940242521357)
            ·
              refine ⟨26457817710090727590945509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70554180560241940242521357 26457817710090727590945509)
              ·
                refine ⟨4960840820642011423302283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26457817710090727590945509 4960840820642011423302283)
                ·
                  refine ⟨7441261230963017134953425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4960840820642011423302283 7441261230963017134953425)
                  ·
                    refine ⟨5580945923222262851215069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7441261230963017134953425 5580945923222262851215069)
                    ·
                      refine ⟨2092854721208348569205651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5580945923222262851215069 2092854721208348569205651)
                      ·
                        rfl

theorem cell23_4075820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 3].length) (baseStart_4075820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075820 prefixEnd_4075820 := by exact prefixLift 4075820
  have htrace : WordTrace (prefixWord ++ tailWord_4075820) baseStart_4075820 baseEnd_4075820 := by
    simpa [prefixWord, tailWord_4075820, baseEnd_4075820] using wordTrace_append hprefix tailTrace_4075820
  have hstable : (prefixWord ++ tailWord_4075820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075820).length < 2 ^ (prefixWord ++ tailWord_4075820).sum := by decide
  have hdescent : baseEnd_4075820 < baseStart_4075820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075823 : List Nat := [1, 1, 2, 1, 2, 1, 8, 7]
def baseStart_4075823 : Nat := 118140960795 + 4075823 * 2 ^ 59
def prefixEnd_4075823 : Nat := 4983230072969 + 3 ^ 40 * 4075823 * 2
def baseEnd_4075823 : Nat := 77513194875937483609931

theorem tailTrace_4075823 : CollatzResearch.WordTrace tailWord_4075823 prefixEnd_4075823 77513194875937483609931 := by
  unfold tailWord_4075823
  simp only [CollatzResearch.WordTrace]
  refine ⟨148657477512996840994544123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99104985008664560663029415 148657477512996840994544123)
  ·
    refine ⟨222986216269495261491816185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148657477512996840994544123 222986216269495261491816185)
    ·
      refine ⟨167239662202121446118862139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222986216269495261491816185 167239662202121446118862139)
      ·
        refine ⟨250859493303182169178293209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167239662202121446118862139 250859493303182169178293209)
        ·
          refine ⟨188144619977386626883719907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250859493303182169178293209 188144619977386626883719907)
          ·
            refine ⟨282216929966079940325579861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188144619977386626883719907 282216929966079940325579861)
            ·
              refine ⟨3307229648039999300690389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 282216929966079940325579861 3307229648039999300690389)
              ·
                refine ⟨77513194875937483609931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3307229648039999300690389 77513194875937483609931)
                ·
                  rfl

theorem cell23_4075823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 8, 7].length) (baseStart_4075823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075823 prefixEnd_4075823 := by exact prefixLift 4075823
  have htrace : WordTrace (prefixWord ++ tailWord_4075823) baseStart_4075823 baseEnd_4075823 := by
    simpa [prefixWord, tailWord_4075823, baseEnd_4075823] using wordTrace_append hprefix tailTrace_4075823
  have hstable : (prefixWord ++ tailWord_4075823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075823).length < 2 ^ (prefixWord ++ tailWord_4075823).sum := by decide
  have hdescent : baseEnd_4075823 < baseStart_4075823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075861 : List Nat := [1, 3, 2, 2, 5, 1, 2, 1, 2, 4]
def baseStart_4075861 : Nat := 118140960795 + 4075861 * 2 ^ 59
def prefixEnd_4075861 : Nat := 4983230072969 + 3 ^ 40 * 4075861 * 2
def baseEnd_4075861 : Nat := 697625257971727636264321

theorem tailTrace_4075861 : CollatzResearch.WordTrace tailWord_4075861 prefixEnd_4075861 697625257971727636264321 := by
  unfold tailWord_4075861
  simp only [CollatzResearch.WordTrace]
  refine ⟨148658863486859173484427437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99105908991239448989618291 148658863486859173484427437)
  ·
    refine ⟨55747073807572190056660289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148658863486859173484427437 55747073807572190056660289)
    ·
      refine ⟨41810305355679142542495217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55747073807572190056660289 41810305355679142542495217)
      ·
        refine ⟨31357729016759356906871413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41810305355679142542495217 31357729016759356906871413)
        ·
          refine ⟨2939787095321189710019195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31357729016759356906871413 2939787095321189710019195)
          ·
            refine ⟨4409680642981784565028793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2939787095321189710019195 4409680642981784565028793)
            ·
              refine ⟨3307260482236338423771595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4409680642981784565028793 3307260482236338423771595)
              ·
                refine ⟨4960890723354507635657393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307260482236338423771595 4960890723354507635657393)
                ·
                  refine ⟨3720668042515880726743045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4960890723354507635657393 3720668042515880726743045)
                  ·
                    refine ⟨697625257971727636264321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3720668042515880726743045 697625257971727636264321)
                    ·
                      rfl

theorem cell23_4075861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 2, 1, 2, 4].length) (baseStart_4075861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075861 prefixEnd_4075861 := by exact prefixLift 4075861
  have htrace : WordTrace (prefixWord ++ tailWord_4075861) baseStart_4075861 baseEnd_4075861 := by
    simpa [prefixWord, tailWord_4075861, baseEnd_4075861] using wordTrace_append hprefix tailTrace_4075861
  have hstable : (prefixWord ++ tailWord_4075861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075861).length < 2 ^ (prefixWord ++ tailWord_4075861).sum := by decide
  have hdescent : baseEnd_4075861 < baseStart_4075861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075877 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 3, 3, 2]
def baseStart_4075877 : Nat := 118140960795 + 4075877 * 2 ^ 59
def prefixEnd_4075877 : Nat := 4983230072969 + 3 ^ 40 * 4075877 * 2
def baseEnd_4075877 : Nat := 2092883989605654846192889

theorem tailTrace_4075877 : CollatzResearch.WordTrace tailWord_4075877 prefixEnd_4075877 2092883989605654846192889 := by
  unfold tailWord_4075877
  simp only [CollatzResearch.WordTrace]
  refine ⟨148659447054801208217009885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99106298036534138811339923 148659447054801208217009885)
  ·
    refine ⟨55747292645550453081378707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148659447054801208217009885 55747292645550453081378707)
    ·
      refine ⟨83620938968325679622068061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55747292645550453081378707 83620938968325679622068061)
      ·
        refine ⟨31357852113122129858275523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83620938968325679622068061 31357852113122129858275523)
        ·
          refine ⟨47036778169683194787413285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31357852113122129858275523 47036778169683194787413285)
          ·
            refine ⟨8819395906815599022639991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47036778169683194787413285 8819395906815599022639991)
            ·
              refine ⟨13229093860223398533959987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819395906815599022639991 13229093860223398533959987)
              ·
                refine ⟨19843640790335097800939981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13229093860223398533959987 19843640790335097800939981)
                ·
                  refine ⟨7441365296375661675352493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19843640790335097800939981 7441365296375661675352493)
                  ·
                    refine ⟨2790511986140873128257185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7441365296375661675352493 2790511986140873128257185)
                    ·
                      refine ⟨2092883989605654846192889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790511986140873128257185 2092883989605654846192889)
                      ·
                        rfl

theorem cell23_4075877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_4075877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075877 prefixEnd_4075877 := by exact prefixLift 4075877
  have htrace : WordTrace (prefixWord ++ tailWord_4075877) baseStart_4075877 baseEnd_4075877 := by
    simpa [prefixWord, tailWord_4075877, baseEnd_4075877] using wordTrace_append hprefix tailTrace_4075877
  have hstable : (prefixWord ++ tailWord_4075877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075877).length < 2 ^ (prefixWord ++ tailWord_4075877).sum := by decide
  have hdescent : baseEnd_4075877 < baseStart_4075877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075903 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 4]
def baseStart_4075903 : Nat := 118140960795 + 4075903 * 2 ^ 59
def prefixEnd_4075903 : Nat := 4983230072969 + 3 ^ 40 * 4075903 * 2
def baseEnd_4075903 : Nat := 2092897340102671744467769

theorem tailTrace_4075903 : CollatzResearch.WordTrace tailWord_4075903 prefixEnd_4075903 2092897340102671744467769 := by
  unfold tailWord_4075903
  simp only [CollatzResearch.WordTrace]
  refine ⟨148660395352707014657456363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99106930235138009771637575 148660395352707014657456363)
  ·
    refine ⟨222990593029060521986184545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148660395352707014657456363 222990593029060521986184545)
    ·
      refine ⟨167242944771795391489638409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222990593029060521986184545 167242944771795391489638409)
      ·
        refine ⟨125432208578846543617228807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167242944771795391489638409 125432208578846543617228807)
        ·
          refine ⟨188148312868269815425843211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125432208578846543617228807 188148312868269815425843211)
          ·
            refine ⟨282222469302404723138764817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188148312868269815425843211 282222469302404723138764817)
            ·
              refine ⟨211666851976803542354073613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282222469302404723138764817 211666851976803542354073613)
              ·
                refine ⟨79375069491301328382777605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 211666851976803542354073613 79375069491301328382777605)
                ·
                  refine ⟨14882825529618999071770801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79375069491301328382777605 14882825529618999071770801)
                  ·
                    refine ⟨11162119147214249303828101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14882825529618999071770801 11162119147214249303828101)
                    ·
                      refine ⟨2092897340102671744467769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11162119147214249303828101 2092897340102671744467769)
                      ·
                        rfl

theorem cell23_4075903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_4075903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075903 prefixEnd_4075903 := by exact prefixLift 4075903
  have htrace : WordTrace (prefixWord ++ tailWord_4075903) baseStart_4075903 baseEnd_4075903 := by
    simpa [prefixWord, tailWord_4075903, baseEnd_4075903] using wordTrace_append hprefix tailTrace_4075903
  have hstable : (prefixWord ++ tailWord_4075903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075903).length < 2 ^ (prefixWord ++ tailWord_4075903).sum := by decide
  have hdescent : baseEnd_4075903 < baseStart_4075903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075930 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 7]
def baseStart_4075930 : Nat := 118140960795 + 4075930 * 2 ^ 59
def prefixEnd_4075930 : Nat := 4983230072969 + 3 ^ 40 * 4075930 * 2
def baseEnd_4075930 : Nat := 232545689342260348758905

theorem tailTrace_4075930 : CollatzResearch.WordTrace tailWord_4075930 prefixEnd_4075930 232545689342260348758905 := by
  unfold tailWord_4075930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37165345030902299567172311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99107586749072798845792829 37165345030902299567172311)
  ·
    refine ⟨55748017546353449350758467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37165345030902299567172311 55748017546353449350758467)
    ·
      refine ⟨83622026319530174026137701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55748017546353449350758467 83622026319530174026137701)
      ·
        refine ⟨15679129934911907629900819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83622026319530174026137701 15679129934911907629900819)
        ·
          refine ⟨23518694902367861444851229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679129934911907629900819 23518694902367861444851229)
          ·
            refine ⟨8819510588387948041819211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23518694902367861444851229 8819510588387948041819211)
            ·
              refine ⟨13229265882581922062728817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8819510588387948041819211 13229265882581922062728817)
              ·
                refine ⟨9921949411936441547046613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13229265882581922062728817 9921949411936441547046613)
                ·
                  refine ⟨232545689342260348758905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9921949411936441547046613 232545689342260348758905)
                  ·
                    rfl

theorem cell23_4075930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 7].length) (baseStart_4075930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075930 prefixEnd_4075930 := by exact prefixLift 4075930
  have htrace : WordTrace (prefixWord ++ tailWord_4075930) baseStart_4075930 baseEnd_4075930 := by
    simpa [prefixWord, tailWord_4075930, baseEnd_4075930] using wordTrace_append hprefix tailTrace_4075930
  have hstable : (prefixWord ++ tailWord_4075930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075930).length < 2 ^ (prefixWord ++ tailWord_4075930).sum := by decide
  have hdescent : baseEnd_4075930 < baseStart_4075930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075963 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4]
def baseStart_4075963 : Nat := 118140960795 + 4075963 * 2 ^ 59
def prefixEnd_4075963 : Nat := 4983230072969 + 3 ^ 40 * 4075963 * 2
def baseEnd_4075963 : Nat := 2092928148941941509717493

theorem tailTrace_4075963 : CollatzResearch.WordTrace tailWord_4075963 prefixEnd_4075963 2092928148941941509717493 := by
  unfold tailWord_4075963
  simp only [CollatzResearch.WordTrace]
  refine ⟨148662583732489644904640543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99108389154993096603093695 148662583732489644904640543)
  ·
    refine ⟨222993875598734467356960815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148662583732489644904640543 222993875598734467356960815)
    ·
      refine ⟨334490813398101701035441223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222993875598734467356960815 334490813398101701035441223)
      ·
        refine ⟨501736220097152551553161835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334490813398101701035441223 501736220097152551553161835)
        ·
          refine ⟨752604330145728827329742753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501736220097152551553161835 752604330145728827329742753)
          ·
            refine ⟨564453247609296620497307065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752604330145728827329742753 564453247609296620497307065)
            ·
              refine ⟨423339935706972465372980299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 564453247609296620497307065 423339935706972465372980299)
              ·
                refine ⟨635009903560458698059470449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 423339935706972465372980299 635009903560458698059470449)
                ·
                  refine ⟨476257427670344023544602837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 635009903560458698059470449 476257427670344023544602837)
                  ·
                    refine ⟨11162283461023688051826629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 476257427670344023544602837 11162283461023688051826629)
                    ·
                      refine ⟨2092928148941941509717493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11162283461023688051826629 2092928148941941509717493)
                      ·
                        rfl

theorem cell23_4075963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_4075963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075963 prefixEnd_4075963 := by exact prefixLift 4075963
  have htrace : WordTrace (prefixWord ++ tailWord_4075963) baseStart_4075963 baseEnd_4075963 := by
    simpa [prefixWord, tailWord_4075963, baseEnd_4075963] using wordTrace_append hprefix tailTrace_4075963
  have hstable : (prefixWord ++ tailWord_4075963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075963).length < 2 ^ (prefixWord ++ tailWord_4075963).sum := by decide
  have hdescent : baseEnd_4075963 < baseStart_4075963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4075997 : List Nat := [1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4075997 : Nat := 118140960795 + 4075997 * 2 ^ 59
def prefixEnd_4075997 : Nat := 4983230072969 + 3 ^ 40 * 4075997 * 2
def baseEnd_4075997 : Nat := 2092945607284194376692337

theorem tailTrace_4075997 : CollatzResearch.WordTrace tailWord_4075997 prefixEnd_4075997 2092945607284194376692337 := by
  unfold tailWord_4075997
  simp only [CollatzResearch.WordTrace]
  refine ⟨148663823814366468711378245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99109215876244312474252163 148663823814366468711378245)
  ·
    refine ⟨27874466965193712883383421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148663823814366468711378245 27874466965193712883383421)
    ·
      refine ⟨10452925111947642331268783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27874466965193712883383421 10452925111947642331268783)
      ·
        refine ⟨15679387667921463496903175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10452925111947642331268783 15679387667921463496903175)
        ·
          refine ⟨23519081501882195245354763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679387667921463496903175 23519081501882195245354763)
          ·
            refine ⟨35278622252823292868032145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23519081501882195245354763 35278622252823292868032145)
            ·
              refine ⟨26458966689617469651024109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35278622252823292868032145 26458966689617469651024109)
              ·
                refine ⟨9922112508606551119134041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26458966689617469651024109 9922112508606551119134041)
                ·
                  refine ⟨7441584381454913339350531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9922112508606551119134041 7441584381454913339350531)
                  ·
                    refine ⟨11162376572182370009025797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7441584381454913339350531 11162376572182370009025797)
                    ·
                      refine ⟨2092945607284194376692337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11162376572182370009025797 2092945607284194376692337)
                      ·
                        rfl

theorem cell23_4075997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4075997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4075997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4075997 prefixEnd_4075997 := by exact prefixLift 4075997
  have htrace : WordTrace (prefixWord ++ tailWord_4075997) baseStart_4075997 baseEnd_4075997 := by
    simpa [prefixWord, tailWord_4075997, baseEnd_4075997] using wordTrace_append hprefix tailTrace_4075997
  have hstable : (prefixWord ++ tailWord_4075997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4075997).length < 2 ^ (prefixWord ++ tailWord_4075997).sum := by decide
  have hdescent : baseEnd_4075997 < baseStart_4075997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4075997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076000 : List Nat := [2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_4076000 : Nat := 118140960795 + 4076000 * 2 ^ 59
def prefixEnd_4076000 : Nat := 4983230072969 + 3 ^ 40 * 4076000 * 2
def baseEnd_4076000 : Nat := 2092947147726157864954823

theorem tailTrace_4076000 : CollatzResearch.WordTrace tailWord_4076000 prefixEnd_4076000 2092947147726157864954823 := by
  unfold tailWord_4076000
  simp only [CollatzResearch.WordTrace]
  refine ⟨74331966616677800111868727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99109288822237066815824969 74331966616677800111868727)
  ·
    refine ⟨111497949925016700167803091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74331966616677800111868727 111497949925016700167803091)
    ·
      refine ⟨167246924887525050251704637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111497949925016700167803091 167246924887525050251704637)
      ·
        refine ⟨62717596832821893844389239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167246924887525050251704637 62717596832821893844389239)
        ·
          refine ⟨94076395249232840766583859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62717596832821893844389239 94076395249232840766583859)
          ·
            refine ⟨141114592873849261149875789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94076395249232840766583859 141114592873849261149875789)
            ·
              refine ⟨52917972327693472931203421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141114592873849261149875789 52917972327693472931203421)
              ·
                refine ⟨19844239622885052349201283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52917972327693472931203421 19844239622885052349201283)
                ·
                  refine ⟨29766359434327578523801925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19844239622885052349201283 29766359434327578523801925)
                  ·
                    refine ⟨5581192393936420973212861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29766359434327578523801925 5581192393936420973212861)
                    ·
                      refine ⟨2092947147726157864954823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581192393936420973212861 2092947147726157864954823)
                      ·
                        rfl

theorem cell23_4076000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_4076000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076000 prefixEnd_4076000 := by exact prefixLift 4076000
  have htrace : WordTrace (prefixWord ++ tailWord_4076000) baseStart_4076000 baseEnd_4076000 := by
    simpa [prefixWord, tailWord_4076000, baseEnd_4076000] using wordTrace_append hprefix tailTrace_4076000
  have hstable : (prefixWord ++ tailWord_4076000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076000).length < 2 ^ (prefixWord ++ tailWord_4076000).sum := by decide
  have hdescent : baseEnd_4076000 < baseStart_4076000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076017 : List Nat := [1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 3]
def baseStart_4076017 : Nat := 118140960795 + 4076017 * 2 ^ 59
def prefixEnd_4076017 : Nat := 4983230072969 + 3 ^ 40 * 4076017 * 2
def baseEnd_4076017 : Nat := 2092955876897284298442245

theorem tailTrace_4076017 : CollatzResearch.WordTrace tailWord_4076017 prefixEnd_4076017 2092955876897284298442245 := by
  unfold tailWord_4076017
  simp only [CollatzResearch.WordTrace]
  refine ⟨148664553274294012127106305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99109702182862674751404203 148664553274294012127106305)
  ·
    refine ⟨111498414955720509095329729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148664553274294012127106305 111498414955720509095329729)
    ·
      refine ⟨83623811216790381821497297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111498414955720509095329729 83623811216790381821497297)
      ·
        refine ⟨62717858412592786366122973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83623811216790381821497297 62717858412592786366122973)
        ·
          refine ⟨23519196904722294887296115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62717858412592786366122973 23519196904722294887296115)
          ·
            refine ⟨35278795357083442330944173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23519196904722294887296115 35278795357083442330944173)
            ·
              refine ⟨13229548258906290874104065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35278795357083442330944173 13229548258906290874104065)
              ·
                refine ⟨9922161194179718155578049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13229548258906290874104065 9922161194179718155578049)
                ·
                  refine ⟨7441620895634788616683537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9922161194179718155578049 7441620895634788616683537)
                  ·
                    refine ⟨5581215671726091462512653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7441620895634788616683537 5581215671726091462512653)
                    ·
                      refine ⟨2092955876897284298442245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581215671726091462512653 2092955876897284298442245)
                      ·
                        rfl

theorem cell23_4076017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_4076017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076017 prefixEnd_4076017 := by exact prefixLift 4076017
  have htrace : WordTrace (prefixWord ++ tailWord_4076017) baseStart_4076017 baseEnd_4076017 := by
    simpa [prefixWord, tailWord_4076017, baseEnd_4076017] using wordTrace_append hprefix tailTrace_4076017
  have hstable : (prefixWord ++ tailWord_4076017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076017).length < 2 ^ (prefixWord ++ tailWord_4076017).sum := by decide
  have hdescent : baseEnd_4076017 < baseStart_4076017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076037 : List Nat := [1, 3, 1, 1, 2, 2, 6, 1, 6]
def baseStart_4076037 : Nat := 118140960795 + 4076037 * 2 ^ 59
def prefixEnd_4076037 : Nat := 4983230072969 + 3 ^ 40 * 4076037 * 2
def baseEnd_4076037 : Nat := 232551794056708246688017

theorem tailTrace_4076037 : CollatzResearch.WordTrace tailWord_4076037 prefixEnd_4076037 232551794056708246688017 := by
  unfold tailWord_4076037
  simp only [CollatzResearch.WordTrace]
  refine ⟨148665282734221555542834365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99110188489481037028556243 148665282734221555542834365)
  ·
    refine ⟨55749481025333083328562887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148665282734221555542834365 55749481025333083328562887)
    ·
      refine ⟨83624221537999624992844331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55749481025333083328562887 83624221537999624992844331)
      ·
        refine ⟨125436332306999437489266497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83624221537999624992844331 125436332306999437489266497)
        ·
          refine ⟨94077249230249578116949873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125436332306999437489266497 94077249230249578116949873)
          ·
            refine ⟨70557936922687183587712405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94077249230249578116949873 70557936922687183587712405)
            ·
              refine ⟨3307403293250961730674019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70557936922687183587712405 3307403293250961730674019)
              ·
                refine ⟨4961104939876442596011029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307403293250961730674019 4961104939876442596011029)
                ·
                  refine ⟨232551794056708246688017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4961104939876442596011029 232551794056708246688017)
                  ·
                    rfl

theorem cell23_4076037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 6, 1, 6].length) (baseStart_4076037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076037 prefixEnd_4076037 := by exact prefixLift 4076037
  have htrace : WordTrace (prefixWord ++ tailWord_4076037) baseStart_4076037 baseEnd_4076037 := by
    simpa [prefixWord, tailWord_4076037, baseEnd_4076037] using wordTrace_append hprefix tailTrace_4076037
  have hstable : (prefixWord ++ tailWord_4076037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076037).length < 2 ^ (prefixWord ++ tailWord_4076037).sum := by decide
  have hdescent : baseEnd_4076037 < baseStart_4076037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076057 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 6, 3, 2]
def baseStart_4076057 : Nat := 118140960795 + 4076057 * 2 ^ 59
def prefixEnd_4076057 : Nat := 4983230072969 + 3 ^ 40 * 4076057 * 2
def baseEnd_4076057 : Nat := 2092976416123464141942061

theorem tailTrace_4076057 : CollatzResearch.WordTrace tailWord_4076057 prefixEnd_4076057 2092976416123464141942061 := by
  unfold tailWord_4076057
  simp only [CollatzResearch.WordTrace]
  refine ⟨148666012194149098958562425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99110674796099399305708283 148666012194149098958562425)
  ·
    refine ⟨111499509145611824218921819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148666012194149098958562425 111499509145611824218921819)
    ·
      refine ⟨167249263718417736328382729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111499509145611824218921819 167249263718417736328382729)
      ·
        refine ⟨125436947788813302246287047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167249263718417736328382729 125436947788813302246287047)
        ·
          refine ⟨188155421683219953369430571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125436947788813302246287047 188155421683219953369430571)
          ·
            refine ⟨282233132524829930054145857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188155421683219953369430571 282233132524829930054145857)
            ·
              refine ⟨211674849393622447540609393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282233132524829930054145857 211674849393622447540609393)
              ·
                refine ⟨158756137045216835655457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 211674849393622447540609393 158756137045216835655457045)
                ·
                  refine ⟨7441693923994539171349549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158756137045216835655457045 7441693923994539171349549)
                  ·
                    refine ⟨2790635221497952189256081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7441693923994539171349549 2790635221497952189256081)
                    ·
                      refine ⟨2092976416123464141942061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790635221497952189256081 2092976416123464141942061)
                      ·
                        rfl

theorem cell23_4076057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 6, 3, 2].length) (baseStart_4076057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076057 prefixEnd_4076057 := by exact prefixLift 4076057
  have htrace : WordTrace (prefixWord ++ tailWord_4076057) baseStart_4076057 baseEnd_4076057 := by
    simpa [prefixWord, tailWord_4076057, baseEnd_4076057] using wordTrace_append hprefix tailTrace_4076057
  have hstable : (prefixWord ++ tailWord_4076057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076057).length < 2 ^ (prefixWord ++ tailWord_4076057).sum := by decide
  have hdescent : baseEnd_4076057 < baseStart_4076057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076071 : List Nat := [1, 1, 7, 2, 1, 1, 2, 2, 6]
def baseStart_4076071 : Nat := 118140960795 + 4076071 * 2 ^ 59
def prefixEnd_4076071 : Nat := 4983230072969 + 3 ^ 40 * 4076071 * 2
def baseEnd_4076071 : Nat := 232553733872514120796333

theorem tailTrace_4076071 : CollatzResearch.WordTrace tailWord_4076071 prefixEnd_4076071 232553733872514120796333 := by
  unfold tailWord_4076071
  simp only [CollatzResearch.WordTrace]
  refine ⟨148666522816098379349572067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99111015210732252899714711 148666522816098379349572067)
  ·
    refine ⟨222999784224147569024358101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148666522816098379349572067 222999784224147569024358101)
    ·
      refine ⟨5226557442753458649008393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 222999784224147569024358101 5226557442753458649008393)
      ·
        refine ⟨3919918082065093986756295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5226557442753458649008393 3919918082065093986756295)
        ·
          refine ⟨5879877123097640980134443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3919918082065093986756295 5879877123097640980134443)
          ·
            refine ⟨8819815684646461470201665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5879877123097640980134443 8819815684646461470201665)
            ·
              refine ⟨6614861763484846102651249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8819815684646461470201665 6614861763484846102651249)
              ·
                refine ⟨4961146322613634576988437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6614861763484846102651249 4961146322613634576988437)
                ·
                  refine ⟨232553733872514120796333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4961146322613634576988437 232553733872514120796333)
                  ·
                    rfl

theorem cell23_4076071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 2, 6].length) (baseStart_4076071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076071 prefixEnd_4076071 := by exact prefixLift 4076071
  have htrace : WordTrace (prefixWord ++ tailWord_4076071) baseStart_4076071 baseEnd_4076071 := by
    simpa [prefixWord, tailWord_4076071, baseEnd_4076071] using wordTrace_append hprefix tailTrace_4076071
  have hstable : (prefixWord ++ tailWord_4076071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076071).length < 2 ^ (prefixWord ++ tailWord_4076071).sum := by decide
  have hdescent : baseEnd_4076071 < baseStart_4076071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076097 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 1, 6]
def baseStart_4076097 : Nat := 118140960795 + 4076097 * 2 ^ 59
def prefixEnd_4076097 : Nat := 4983230072969 + 3 ^ 40 * 4076097 * 2
def baseEnd_4076097 : Nat := 697665651783214661813959

theorem tailTrace_4076097 : CollatzResearch.WordTrace tailWord_4076097 prefixEnd_4076097 697665651783214661813959 := by
  unfold tailWord_4076097
  simp only [CollatzResearch.WordTrace]
  refine ⟨148667471114004185790018545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99111647409336123860012363 148667471114004185790018545)
  ·
    refine ⟨111500603335503139342513909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148667471114004185790018545 111500603335503139342513909)
    ·
      refine ⟨10453181562703419313360679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111500603335503139342513909 10453181562703419313360679)
      ·
        refine ⟨15679772344055128970041019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453181562703419313360679 15679772344055128970041019)
        ·
          refine ⟨23519658516082693455061529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679772344055128970041019 23519658516082693455061529)
          ·
            refine ⟨17639743887062020091296147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23519658516082693455061529 17639743887062020091296147)
            ·
              refine ⟨26459615830593030136944221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17639743887062020091296147 26459615830593030136944221)
              ·
                refine ⟨9922355936472386301354083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26459615830593030136944221 9922355936472386301354083)
                ·
                  refine ⟨14883533904708579452031125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9922355936472386301354083 14883533904708579452031125)
                  ·
                    refine ⟨697665651783214661813959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14883533904708579452031125 697665651783214661813959)
                    ·
                      rfl

theorem cell23_4076097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_4076097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076097 prefixEnd_4076097 := by exact prefixLift 4076097
  have htrace : WordTrace (prefixWord ++ tailWord_4076097) baseStart_4076097 baseEnd_4076097 := by
    simpa [prefixWord, tailWord_4076097, baseEnd_4076097] using wordTrace_append hprefix tailTrace_4076097
  have hstable : (prefixWord ++ tailWord_4076097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076097).length < 2 ^ (prefixWord ++ tailWord_4076097).sum := by decide
  have hdescent : baseEnd_4076097 < baseStart_4076097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076107 : List Nat := [1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 3]
def baseStart_4076107 : Nat := 118140960795 + 4076107 * 2 ^ 59
def prefixEnd_4076107 : Nat := 4983230072969 + 3 ^ 40 * 4076107 * 2
def baseEnd_4076107 : Nat := 2093002090156188946316831

theorem tailTrace_4076107 : CollatzResearch.WordTrace tailWord_4076107 prefixEnd_4076107 2093002090156188946316831 := by
  unfold tailWord_4076107
  simp only [CollatzResearch.WordTrace]
  refine ⟨148667835843967957497882575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99111890562645304998588383 148667835843967957497882575)
  ·
    refine ⟨223001753765951936246823863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148667835843967957497882575 223001753765951936246823863)
    ·
      refine ⟨334502630648927904370235795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223001753765951936246823863 334502630648927904370235795)
      ·
        refine ⟨501753945973391856555353693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334502630648927904370235795 501753945973391856555353693)
        ·
          refine ⟨188157729740021946208257635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 501753945973391856555353693 188157729740021946208257635)
          ·
            refine ⟨282236594610032919312386453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188157729740021946208257635 282236594610032919312386453)
            ·
              refine ⟨13229840372345293092768115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 282236594610032919312386453 13229840372345293092768115)
              ·
                refine ⟨19844760558517939639152173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13229840372345293092768115 19844760558517939639152173)
                ·
                  refine ⟨7441785209444227364682065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19844760558517939639152173 7441785209444227364682065)
                  ·
                    refine ⟨5581338907083170523511549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7441785209444227364682065 5581338907083170523511549)
                    ·
                      refine ⟨2093002090156188946316831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581338907083170523511549 2093002090156188946316831)
                      ·
                        rfl

theorem cell23_4076107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 1, 3, 2, 3].length) (baseStart_4076107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076107 prefixEnd_4076107 := by exact prefixLift 4076107
  have htrace : WordTrace (prefixWord ++ tailWord_4076107) baseStart_4076107 baseEnd_4076107 := by
    simpa [prefixWord, tailWord_4076107, baseEnd_4076107] using wordTrace_append hprefix tailTrace_4076107
  have hstable : (prefixWord ++ tailWord_4076107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076107).length < 2 ^ (prefixWord ++ tailWord_4076107).sum := by decide
  have hdescent : baseEnd_4076107 < baseStart_4076107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076110 : List Nat := [4, 1, 1, 1, 1, 2, 2, 11]
def baseStart_4076110 : Nat := 118140960795 + 4076110 * 2 ^ 59
def prefixEnd_4076110 : Nat := 4983230072969 + 3 ^ 40 * 4076110 * 2
def baseEnd_4076110 : Nat := 77518652985116756836271

theorem tailTrace_4076110 : CollatzResearch.WordTrace tailWord_4076110 prefixEnd_4076110 77518652985116756836271 := by
  unfold tailWord_4076110
  simp only [CollatzResearch.WordTrace]
  refine ⟨18583493157869636126280223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99111963508638059340161189 18583493157869636126280223)
  ·
    refine ⟨27875239736804454189420335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18583493157869636126280223 27875239736804454189420335)
    ·
      refine ⟨41812859605206681284130503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27875239736804454189420335 41812859605206681284130503)
      ·
        refine ⟨62719289407810021926195755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41812859605206681284130503 62719289407810021926195755)
        ·
          refine ⟨94078934111715032889293633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62719289407810021926195755 94078934111715032889293633)
          ·
            refine ⟨70559200583786274666970225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94078934111715032889293633 70559200583786274666970225)
            ·
              refine ⟨52919400437839706000227669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70559200583786274666970225 52919400437839706000227669)
              ·
                refine ⟨77518652985116756836271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 52919400437839706000227669 77518652985116756836271)
                ·
                  rfl

theorem cell23_4076110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 11].length) (baseStart_4076110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076110 prefixEnd_4076110 := by exact prefixLift 4076110
  have htrace : WordTrace (prefixWord ++ tailWord_4076110) baseStart_4076110 baseEnd_4076110 := by
    simpa [prefixWord, tailWord_4076110, baseEnd_4076110] using wordTrace_append hprefix tailTrace_4076110
  have hstable : (prefixWord ++ tailWord_4076110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076110).length < 2 ^ (prefixWord ++ tailWord_4076110).sum := by decide
  have hdescent : baseEnd_4076110 < baseStart_4076110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076117 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4076117 : Nat := 118140960795 + 4076117 * 2 ^ 59
def prefixEnd_4076117 : Nat := 4983230072969 + 3 ^ 40 * 4076117 * 2
def baseEnd_4076117 : Nat := 2093007224962733907191785

theorem tailTrace_4076117 : CollatzResearch.WordTrace tailWord_4076117 prefixEnd_4076117 2093007224962733907191785 := by
  unfold tailWord_4076117
  simp only [CollatzResearch.WordTrace]
  refine ⟨148668200573931729205746605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99112133715954486137164403 148668200573931729205746605)
  ·
    refine ⟨55750575215224398452154977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148668200573931729205746605 55750575215224398452154977)
    ·
      refine ⟨41812931411418298839116233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55750575215224398452154977 41812931411418298839116233)
      ·
        refine ⟨31359698558563724129337175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41812931411418298839116233 31359698558563724129337175)
        ·
          refine ⟨47039547837845586194005763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31359698558563724129337175 47039547837845586194005763)
          ·
            refine ⟨70559321756768379291008645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47039547837845586194005763 70559321756768379291008645)
            ·
              refine ⟨13229872829394071117064121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70559321756768379291008645 13229872829394071117064121)
              ·
                refine ⟨9922404622045553337798091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13229872829394071117064121 9922404622045553337798091)
                ·
                  refine ⟨14883606933068330006697137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9922404622045553337798091 14883606933068330006697137)
                  ·
                    refine ⟨11162705199801247505022853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14883606933068330006697137 11162705199801247505022853)
                    ·
                      refine ⟨2093007224962733907191785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11162705199801247505022853 2093007224962733907191785)
                      ·
                        rfl

theorem cell23_4076117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4076117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076117 prefixEnd_4076117 := by exact prefixLift 4076117
  have htrace : WordTrace (prefixWord ++ tailWord_4076117) baseStart_4076117 baseEnd_4076117 := by
    simpa [prefixWord, tailWord_4076117, baseEnd_4076117] using wordTrace_append hprefix tailTrace_4076117
  have hstable : (prefixWord ++ tailWord_4076117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076117).length < 2 ^ (prefixWord ++ tailWord_4076117).sum := by decide
  have hdescent : baseEnd_4076117 < baseStart_4076117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076138 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_4076138 : Nat := 118140960795 + 4076138 * 2 ^ 59
def prefixEnd_4076138 : Nat := 4983230072969 + 3 ^ 40 * 4076138 * 2
def baseEnd_4076138 : Nat := 2093018008056478325029189

theorem tailTrace_4076138 : CollatzResearch.WordTrace tailWord_4076138 prefixEnd_4076138 2093018008056478325029189 := by
  unfold tailWord_4076138
  simp only [CollatzResearch.WordTrace]
  refine ⟨37167241626713912448065267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99112644337903766528174045 37167241626713912448065267)
  ·
    refine ⟨55750862440070868672097901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37167241626713912448065267 55750862440070868672097901)
    ·
      refine ⟨20906573415026575752036713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55750862440070868672097901 20906573415026575752036713)
      ·
        refine ⟨15679930061269931814027535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20906573415026575752036713 15679930061269931814027535)
        ·
          refine ⟨23519895091904897721041303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15679930061269931814027535 23519895091904897721041303)
          ·
            refine ⟨35279842637857346581561955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23519895091904897721041303 35279842637857346581561955)
            ·
              refine ⟨52919763956786019872342933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35279842637857346581561955 52919763956786019872342933)
              ·
                refine ⟨2480613935474344681516075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52919763956786019872342933 2480613935474344681516075)
                ·
                  refine ⟨3720920903211517022274113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480613935474344681516075 3720920903211517022274113)
                  ·
                    refine ⟨2790690677408637766705585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3720920903211517022274113 2790690677408637766705585)
                    ·
                      refine ⟨2093018008056478325029189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790690677408637766705585 2093018008056478325029189)
                      ·
                        rfl

theorem cell23_4076138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_4076138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076138 prefixEnd_4076138 := by exact prefixLift 4076138
  have htrace : WordTrace (prefixWord ++ tailWord_4076138) baseStart_4076138 baseEnd_4076138 := by
    simpa [prefixWord, tailWord_4076138, baseEnd_4076138] using wordTrace_append hprefix tailTrace_4076138
  have hstable : (prefixWord ++ tailWord_4076138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076138).length < 2 ^ (prefixWord ++ tailWord_4076138).sum := by decide
  have hdescent : baseEnd_4076138 < baseStart_4076138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076140 : List Nat := [2, 2, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_4076140 : Nat := 118140960795 + 4076140 * 2 ^ 59
def prefixEnd_4076140 : Nat := 4983230072969 + 3 ^ 40 * 4076140 * 2
def baseEnd_4076140 : Nat := 697673011672595772401393

theorem tailTrace_4076140 : CollatzResearch.WordTrace tailWord_4076140 prefixEnd_4076140 697673011672595772401393 := by
  unfold tailWord_4076140
  simp only [CollatzResearch.WordTrace]
  refine ⟨74334519726424202066916937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99112692968565602755889249 74334519726424202066916937)
  ·
    refine ⟨55750889794818151550187703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74334519726424202066916937 55750889794818151550187703)
    ·
      refine ⟨83626334692227227325281555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55750889794818151550187703 83626334692227227325281555)
      ·
        refine ⟨125439502038340840987922333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83626334692227227325281555 125439502038340840987922333)
        ·
          refine ⟨47039813264377815370470875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125439502038340840987922333 47039813264377815370470875)
          ·
            refine ⟨70559719896566723055706313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47039813264377815370470875 70559719896566723055706313)
            ·
              refine ⟨52919789922425042291779735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70559719896566723055706313 52919789922425042291779735)
              ·
                refine ⟨79379684883637563437669603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52919789922425042291779735 79379684883637563437669603)
                ·
                  refine ⟨119069527325456345156504405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79379684883637563437669603 119069527325456345156504405)
                  ·
                    refine ⟨697673011672595772401393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 119069527325456345156504405 697673011672595772401393)
                    ·
                      rfl

theorem cell23_4076140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_4076140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076140 prefixEnd_4076140 := by exact prefixLift 4076140
  have htrace : WordTrace (prefixWord ++ tailWord_4076140) baseStart_4076140 baseEnd_4076140 := by
    simpa [prefixWord, tailWord_4076140, baseEnd_4076140] using wordTrace_append hprefix tailTrace_4076140
  have hstable : (prefixWord ++ tailWord_4076140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076140).length < 2 ^ (prefixWord ++ tailWord_4076140).sum := by decide
  have hdescent : baseEnd_4076140 < baseStart_4076140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076147 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 2, 7, 2]
def baseStart_4076147 : Nat := 118140960795 + 4076147 * 2 ^ 59
def prefixEnd_4076147 : Nat := 4983230072969 + 3 ^ 40 * 4076147 * 2
def baseEnd_4076147 : Nat := 2093022629382368789816647

theorem tailTrace_4076147 : CollatzResearch.WordTrace tailWord_4076147 prefixEnd_4076147 2093022629382368789816647 := by
  unfold tailWord_4076147
  simp only [CollatzResearch.WordTrace]
  refine ⟨148669294763823044329338695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99112863175882029552892463 148669294763823044329338695)
  ·
    refine ⟨223003942145734566494008043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148669294763823044329338695 223003942145734566494008043)
    ·
      refine ⟨334505913218601849741012065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223003942145734566494008043 334505913218601849741012065)
      ·
        refine ⟨250879434913951387305759049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334505913218601849741012065 250879434913951387305759049)
        ·
          refine ⟨188159576185463540479319287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250879434913951387305759049 188159576185463540479319287)
          ·
            refine ⟨282239364278195310718978931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188159576185463540479319287 282239364278195310718978931)
            ·
              refine ⟨423359046417292966078468397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282239364278195310718978931 423359046417292966078468397)
              ·
                refine ⟨158759642406484862279425649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423359046417292966078468397 158759642406484862279425649)
                ·
                  refine ⟨119069731804863646709569237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158759642406484862279425649 119069731804863646709569237)
                  ·
                    refine ⟨2790696839176491719755529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 119069731804863646709569237 2790696839176491719755529)
                    ·
                      refine ⟨2093022629382368789816647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790696839176491719755529 2093022629382368789816647)
                      ·
                        rfl

theorem cell23_4076147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 7, 2].length) (baseStart_4076147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076147 prefixEnd_4076147 := by exact prefixLift 4076147
  have htrace : WordTrace (prefixWord ++ tailWord_4076147) baseStart_4076147 baseEnd_4076147 := by
    simpa [prefixWord, tailWord_4076147, baseEnd_4076147] using wordTrace_append hprefix tailTrace_4076147
  have hstable : (prefixWord ++ tailWord_4076147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076147).length < 2 ^ (prefixWord ++ tailWord_4076147).sum := by decide
  have hdescent : baseEnd_4076147 < baseStart_4076147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076197 : List Nat := [1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 3]
def baseStart_4076197 : Nat := 118140960795 + 4076197 * 2 ^ 59
def prefixEnd_4076197 : Nat := 4983230072969 + 3 ^ 40 * 4076197 * 2
def baseEnd_4076197 : Nat := 2093048303415093594191417

theorem tailTrace_4076197 : CollatzResearch.WordTrace tailWord_4076197 prefixEnd_4076197 2093048303415093594191417 := by
  unfold tailWord_4076197
  simp only [CollatzResearch.WordTrace]
  refine ⟨148671118413641902868658845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99114078942427935245772563 148671118413641902868658845)
  ·
    refine ⟨55751669405115713575747067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148671118413641902868658845 55751669405115713575747067)
    ·
      refine ⟨83627504107673570363620601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55751669405115713575747067 83627504107673570363620601)
      ·
        refine ⟨62720628080755177772715451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83627504107673570363620601 62720628080755177772715451)
        ·
          refine ⟨94080942121132766659073177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62720628080755177772715451 94080942121132766659073177)
          ·
            refine ⟨70560706590849574994304883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94080942121132766659073177 70560706590849574994304883)
            ·
              refine ⟨105841059886274362491457325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70560706590849574994304883 105841059886274362491457325)
              ·
                refine ⟨39690397457352885934296497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105841059886274362491457325 39690397457352885934296497)
                ·
                  refine ⟨29767798093014664450722373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39690397457352885934296497 29767798093014664450722373)
                  ·
                    refine ⟨5581462142440249584510445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29767798093014664450722373 5581462142440249584510445)
                    ·
                      refine ⟨2093048303415093594191417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581462142440249584510445 2093048303415093594191417)
                      ·
                        rfl

theorem cell23_4076197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_4076197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076197 prefixEnd_4076197 := by exact prefixLift 4076197
  have htrace : WordTrace (prefixWord ++ tailWord_4076197) baseStart_4076197 baseEnd_4076197 := by
    simpa [prefixWord, tailWord_4076197, baseEnd_4076197] using wordTrace_append hprefix tailTrace_4076197
  have hstable : (prefixWord ++ tailWord_4076197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076197).length < 2 ^ (prefixWord ++ tailWord_4076197).sum := by decide
  have hdescent : baseEnd_4076197 < baseStart_4076197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076205 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_4076205 : Nat := 118140960795 + 4076205 * 2 ^ 59
def prefixEnd_4076205 : Nat := 4983230072969 + 3 ^ 40 * 4076205 * 2
def baseEnd_4076205 : Nat := 2093052411260329562891381

theorem tailTrace_4076205 : CollatzResearch.WordTrace tailWord_4076205 prefixEnd_4076205 2093052411260329562891381 := by
  unfold tailWord_4076205
  simp only [CollatzResearch.WordTrace]
  refine ⟨148671410197612920234950069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99114273465075280156633379 148671410197612920234950069)
  ·
    refine ⟨13937944706026211272026569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148671410197612920234950069 13937944706026211272026569)
    ·
      refine ⟨10453458529519658454019927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13937944706026211272026569 10453458529519658454019927)
      ·
        refine ⟨15680187794279487681029891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10453458529519658454019927 15680187794279487681029891)
        ·
          refine ⟨23520281691419231521544837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15680187794279487681029891 23520281691419231521544837)
          ·
            refine ⟨4410052817141105910289657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23520281691419231521544837 4410052817141105910289657)
            ·
              refine ⟨3307539612855829432717243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410052817141105910289657 3307539612855829432717243)
              ·
                refine ⟨4961309419283744149075865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307539612855829432717243 4961309419283744149075865)
                ·
                  refine ⟨3720982064462808111806899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4961309419283744149075865 3720982064462808111806899)
                  ·
                    refine ⟨5581473096694212167710349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3720982064462808111806899 5581473096694212167710349)
                    ·
                      refine ⟨2093052411260329562891381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581473096694212167710349 2093052411260329562891381)
                      ·
                        rfl

theorem cell23_4076205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_4076205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076205 prefixEnd_4076205 := by exact prefixLift 4076205
  have htrace : WordTrace (prefixWord ++ tailWord_4076205) baseStart_4076205 baseEnd_4076205 := by
    simpa [prefixWord, tailWord_4076205, baseEnd_4076205] using wordTrace_append hprefix tailTrace_4076205
  have hstable : (prefixWord ++ tailWord_4076205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076205).length < 2 ^ (prefixWord ++ tailWord_4076205).sum := by decide
  have hdescent : baseEnd_4076205 < baseStart_4076205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076215 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 1, 3, 2]
def baseStart_4076215 : Nat := 118140960795 + 4076215 * 2 ^ 59
def prefixEnd_4076215 : Nat := 4983230072969 + 3 ^ 40 * 4076215 * 2
def baseEnd_4076215 : Nat := 2093057546066874523766335

theorem tailTrace_4076215 : CollatzResearch.WordTrace tailWord_4076215 prefixEnd_4076215 2093057546066874523766335 := by
  unfold tailWord_4076215
  simp only [CollatzResearch.WordTrace]
  refine ⟨148671774927576691942814099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99114516618384461295209399 148671774927576691942814099)
  ·
    refine ⟨223007662391365037914221149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148671774927576691942814099 223007662391365037914221149)
    ·
      refine ⟨83627873396761889217832931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223007662391365037914221149 83627873396761889217832931)
      ·
        refine ⟨125441810095142833826749397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83627873396761889217832931 125441810095142833826749397)
        ·
          refine ⟨2940042424104910167814439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 125441810095142833826749397 2940042424104910167814439)
          ·
            refine ⟨4410063636157365251721659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940042424104910167814439 4410063636157365251721659)
            ·
              refine ⟨6615095454236047877582489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410063636157365251721659 6615095454236047877582489)
              ·
                refine ⟨4961321590677035908186867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6615095454236047877582489 4961321590677035908186867)
                ·
                  refine ⟨7441982386015553862280301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961321590677035908186867 7441982386015553862280301)
                  ·
                    refine ⟨2790743394755832698355113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7441982386015553862280301 2790743394755832698355113)
                    ·
                      refine ⟨2093057546066874523766335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790743394755832698355113 2093057546066874523766335)
                      ·
                        rfl

theorem cell23_4076215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 1, 3, 2].length) (baseStart_4076215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076215 prefixEnd_4076215 := by exact prefixLift 4076215
  have htrace : WordTrace (prefixWord ++ tailWord_4076215) baseStart_4076215 baseEnd_4076215 := by
    simpa [prefixWord, tailWord_4076215, baseEnd_4076215] using wordTrace_append hprefix tailTrace_4076215
  have hstable : (prefixWord ++ tailWord_4076215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076215).length < 2 ^ (prefixWord ++ tailWord_4076215).sum := by decide
  have hdescent : baseEnd_4076215 < baseStart_4076215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076267 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4]
def baseStart_4076267 : Nat := 118140960795 + 4076267 * 2 ^ 59
def prefixEnd_4076267 : Nat := 4983230072969 + 3 ^ 40 * 4076267 * 2
def baseEnd_4076267 : Nat := 2093084247060908320316095

theorem tailTrace_4076267 : CollatzResearch.WordTrace tailWord_4076267 prefixEnd_4076267 2093084247060908320316095 := by
  unfold tailWord_4076267
  simp only [CollatzResearch.WordTrace]
  refine ⟨148673671523388304823707055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99115781015592203215804703 148673671523388304823707055)
  ·
    refine ⟨223010507285082457235560583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148673671523388304823707055 223010507285082457235560583)
    ·
      refine ⟨334515760927623685853340875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223010507285082457235560583 334515760927623685853340875)
      ·
        refine ⟨501773641391435528780011313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334515760927623685853340875 501773641391435528780011313)
        ·
          refine ⟨376330231043576646585008485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 501773641391435528780011313 376330231043576646585008485)
          ·
            refine ⟨70561918320670621234689091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376330231043576646585008485 70561918320670621234689091)
            ·
              refine ⟨105842877481005931852033637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70561918320670621234689091 105842877481005931852033637)
              ·
                refine ⟨19845539527688612222256307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105842877481005931852033637 19845539527688612222256307)
                ·
                  refine ⟨29768309291532918333384461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19845539527688612222256307 29768309291532918333384461)
                  ·
                    refine ⟨11163115984324844375019173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29768309291532918333384461 11163115984324844375019173)
                    ·
                      refine ⟨2093084247060908320316095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11163115984324844375019173 2093084247060908320316095)
                      ·
                        rfl

theorem cell23_4076267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_4076267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076267 prefixEnd_4076267 := by exact prefixLift 4076267
  have htrace : WordTrace (prefixWord ++ tailWord_4076267) baseStart_4076267 baseEnd_4076267 := by
    simpa [prefixWord, tailWord_4076267, baseEnd_4076267] using wordTrace_append hprefix tailTrace_4076267
  have hstable : (prefixWord ++ tailWord_4076267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076267).length < 2 ^ (prefixWord ++ tailWord_4076267).sum := by decide
  have hdescent : baseEnd_4076267 < baseStart_4076267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076284 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_4076284 : Nat := 118140960795 + 4076284 * 2 ^ 59
def prefixEnd_4076284 : Nat := 4983230072969 + 3 ^ 40 * 4076284 * 2
def baseEnd_4076284 : Nat := 2093092976232034753803517

theorem tailTrace_4076284 : CollatzResearch.WordTrace tailWord_4076284 prefixEnd_4076284 2093092976232034753803517 := by
  unfold tailWord_4076284
  simp only [CollatzResearch.WordTrace]
  refine ⟨74337145782163358363537953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99116194376217811151383937 74337145782163358363537953)
  ·
    refine ⟨55752859336622518772653465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74337145782163358363537953 55752859336622518772653465)
    ·
      refine ⟨41814644502466889079490099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55752859336622518772653465 41814644502466889079490099)
      ·
        refine ⟨62721966753700333619235149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41814644502466889079490099 62721966753700333619235149)
        ·
          refine ⟨23520737532637625107213181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62721966753700333619235149 23520737532637625107213181)
          ·
            refine ⟨8820276574739109415204943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23520737532637625107213181 8820276574739109415204943)
            ·
              refine ⟨13230414862108664122807415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820276574739109415204943 13230414862108664122807415)
              ·
                refine ⟨19845622293162996184211123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230414862108664122807415 19845622293162996184211123)
                ·
                  refine ⟨29768433439744494276316685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19845622293162996184211123 29768433439744494276316685)
                  ·
                    refine ⟨11163162539904185353618757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29768433439744494276316685 11163162539904185353618757)
                    ·
                      refine ⟨2093092976232034753803517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11163162539904185353618757 2093092976232034753803517)
                      ·
                        rfl

theorem cell23_4076284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_4076284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076284 prefixEnd_4076284 := by exact prefixLift 4076284
  have htrace : WordTrace (prefixWord ++ tailWord_4076284) baseStart_4076284 baseEnd_4076284 := by
    simpa [prefixWord, tailWord_4076284, baseEnd_4076284] using wordTrace_append hprefix tailTrace_4076284
  have hstable : (prefixWord ++ tailWord_4076284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076284).length < 2 ^ (prefixWord ++ tailWord_4076284).sum := by decide
  have hdescent : baseEnd_4076284 < baseStart_4076284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076297 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_4076297 : Nat := 118140960795 + 4076297 * 2 ^ 59
def prefixEnd_4076297 : Nat := 4983230072969 + 3 ^ 40 * 4076297 * 2
def baseEnd_4076297 : Nat := 2093099651480543202940957

theorem tailTrace_4076297 : CollatzResearch.WordTrace tailWord_4076297 prefixEnd_4076297 2093099651480543202940957 := by
  unfold tailWord_4076297
  simp only [CollatzResearch.WordTrace]
  refine ⟨148674765713279619947299145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99116510475519746631532763 148674765713279619947299145)
  ·
    refine ⟨111506074284959714960474359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148674765713279619947299145 111506074284959714960474359)
    ·
      refine ⟨167259111427439572440711539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111506074284959714960474359 167259111427439572440711539)
      ·
        refine ⟨250888667141159358661067309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167259111427439572440711539 250888667141159358661067309)
        ·
          refine ⟨94083250177934759497900241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250888667141159358661067309 94083250177934759497900241)
          ·
            refine ⟨70562437633451069623425181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94083250177934759497900241 70562437633451069623425181)
            ·
              refine ⟨26460914112544151108784443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70562437633451069623425181 26460914112544151108784443)
              ·
                refine ⟨39691371168816226663176665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26460914112544151108784443 39691371168816226663176665)
                ·
                  refine ⟨29768528376612169997382499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39691371168816226663176665 29768528376612169997382499)
                  ·
                    refine ⟨44652792564918254996073749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29768528376612169997382499 44652792564918254996073749)
                    ·
                      refine ⟨2093099651480543202940957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44652792564918254996073749 2093099651480543202940957)
                      ·
                        rfl

theorem cell23_4076297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_4076297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076297 prefixEnd_4076297 := by exact prefixLift 4076297
  have htrace : WordTrace (prefixWord ++ tailWord_4076297) baseStart_4076297 baseEnd_4076297 := by
    simpa [prefixWord, tailWord_4076297, baseEnd_4076297] using wordTrace_append hprefix tailTrace_4076297
  have hstable : (prefixWord ++ tailWord_4076297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076297).length < 2 ^ (prefixWord ++ tailWord_4076297).sum := by decide
  have hdescent : baseEnd_4076297 < baseStart_4076297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076307 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 8]
def baseStart_4076307 : Nat := 118140960795 + 4076307 * 2 ^ 59
def prefixEnd_4076307 : Nat := 4983230072969 + 3 ^ 40 * 4076307 * 2
def baseEnd_4076307 : Nat := 232567198476343129312879

theorem tailTrace_4076307 : CollatzResearch.WordTrace tailWord_4076307 prefixEnd_4076307 232567198476343129312879 := by
  unfold tailWord_4076307
  simp only [CollatzResearch.WordTrace]
  refine ⟨148675130443243391655163175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99116753628828927770108783 148675130443243391655163175)
  ·
    refine ⟨223012695664865087482744763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148675130443243391655163175 223012695664865087482744763)
    ·
      refine ⟨334519043497297631224117145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223012695664865087482744763 334519043497297631224117145)
      ·
        refine ⟨250889282622973223418087859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334519043497297631224117145 250889282622973223418087859)
        ·
          refine ⟨376333923934459835127131789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250889282622973223418087859 376333923934459835127131789)
          ·
            refine ⟨141125221475422438172674421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376333923934459835127131789 141125221475422438172674421)
            ·
              refine ⟨13230489513320853578688227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 141125221475422438172674421 13230489513320853578688227)
              ·
                refine ⟨19845734269981280368032341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230489513320853578688227 19845734269981280368032341)
                ·
                  refine ⟨232567198476343129312879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19845734269981280368032341 232567198476343129312879)
                  ·
                    rfl

theorem cell23_4076307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 8].length) (baseStart_4076307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076307 prefixEnd_4076307 := by exact prefixLift 4076307
  have htrace : WordTrace (prefixWord ++ tailWord_4076307) baseStart_4076307 baseEnd_4076307 := by
    simpa [prefixWord, tailWord_4076307, baseEnd_4076307] using wordTrace_append hprefix tailTrace_4076307
  have hstable : (prefixWord ++ tailWord_4076307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076307).length < 2 ^ (prefixWord ++ tailWord_4076307).sum := by decide
  have hdescent : baseEnd_4076307 < baseStart_4076307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076361 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 4, 3, 2]
def baseStart_4076361 : Nat := 118140960795 + 4076361 * 2 ^ 59
def prefixEnd_4076361 : Nat := 4983230072969 + 3 ^ 40 * 4076361 * 2
def baseEnd_4076361 : Nat := 2093132514242430952540663

theorem tailTrace_4076361 : CollatzResearch.WordTrace tailWord_4076361 prefixEnd_4076361 2093132514242430952540663 := by
  unfold tailWord_4076361
  simp only [CollatzResearch.WordTrace]
  refine ⟨148677099985047758877628937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99118066656698505918419291 148677099985047758877628937)
  ·
    refine ⟨111507824988785819158221703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148677099985047758877628937 111507824988785819158221703)
    ·
      refine ⟨167261737483178728737332555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111507824988785819158221703 167261737483178728737332555)
      ·
        refine ⟨250892606224768093105998833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167261737483178728737332555 250892606224768093105998833)
        ·
          refine ⟨188169454668576069829499125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250892606224768093105998833 188169454668576069829499125)
          ·
            refine ⟨17640886375179006546515543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188169454668576069829499125 17640886375179006546515543)
            ·
              refine ⟨26461329562768509819773315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17640886375179006546515543 26461329562768509819773315)
              ·
                refine ⟨39691994344152764729659973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26461329562768509819773315 39691994344152764729659973)
                ·
                  refine ⟨7442248939528643386811245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39691994344152764729659973 7442248939528643386811245)
                  ·
                    refine ⟨2790843352323241270054217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7442248939528643386811245 2790843352323241270054217)
                    ·
                      refine ⟨2093132514242430952540663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790843352323241270054217 2093132514242430952540663)
                      ·
                        rfl

theorem cell23_4076361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 4, 3, 2].length) (baseStart_4076361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076361 prefixEnd_4076361 := by exact prefixLift 4076361
  have htrace : WordTrace (prefixWord ++ tailWord_4076361) baseStart_4076361 baseEnd_4076361 := by
    simpa [prefixWord, tailWord_4076361, baseEnd_4076361] using wordTrace_append hprefix tailTrace_4076361
  have hstable : (prefixWord ++ tailWord_4076361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076361).length < 2 ^ (prefixWord ++ tailWord_4076361).sum := by decide
  have hdescent : baseEnd_4076361 < baseStart_4076361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076368 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 1, 1, 3]
def baseStart_4076368 : Nat := 118140960795 + 4076368 * 2 ^ 59
def prefixEnd_4076368 : Nat := 4983230072969 + 3 ^ 40 * 4076368 * 2
def baseEnd_4076368 : Nat := 2093136108607012425153131

theorem tailTrace_4076368 : CollatzResearch.WordTrace tailWord_4076368 prefixEnd_4076368 2093136108607012425153131 := by
  unfold tailWord_4076368
  simp only [CollatzResearch.WordTrace]
  refine ⟨74338677648011199536566879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99118236864014932715422505 74338677648011199536566879)
  ·
    refine ⟨111508016472016799304850319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74338677648011199536566879 111508016472016799304850319)
    ·
      refine ⟨167262024708025198957275479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111508016472016799304850319 167262024708025198957275479)
      ·
        refine ⟨250893037062037798435913219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167262024708025198957275479 250893037062037798435913219)
        ·
          refine ⟨376339555593056697653869829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250893037062037798435913219 376339555593056697653869829)
          ·
            refine ⟨70563666673698130810100593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 376339555593056697653869829 70563666673698130810100593)
            ·
              refine ⟨52922750005273598107575445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70563666673698130810100593 52922750005273598107575445)
              ·
                refine ⟨2480753906497199911292599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52922750005273598107575445 2480753906497199911292599)
                ·
                  refine ⟨3721130859745799866938899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2480753906497199911292599 3721130859745799866938899)
                  ·
                    refine ⟨5581696289618699800408349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721130859745799866938899 5581696289618699800408349)
                    ·
                      refine ⟨2093136108607012425153131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581696289618699800408349 2093136108607012425153131)
                      ·
                        rfl

theorem cell23_4076368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 1, 1, 3].length) (baseStart_4076368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076368 prefixEnd_4076368 := by exact prefixLift 4076368
  have htrace : WordTrace (prefixWord ++ tailWord_4076368) baseStart_4076368 baseEnd_4076368 := by
    simpa [prefixWord, tailWord_4076368, baseEnd_4076368] using wordTrace_append hprefix tailTrace_4076368
  have hstable : (prefixWord ++ tailWord_4076368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076368).length < 2 ^ (prefixWord ++ tailWord_4076368).sum := by decide
  have hdescent : baseEnd_4076368 < baseStart_4076368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076384 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_4076384 : Nat := 118140960795 + 4076384 * 2 ^ 59
def prefixEnd_4076384 : Nat := 4983230072969 + 3 ^ 40 * 4076384 * 2
def baseEnd_4076384 : Nat := 697714774765828120851019

theorem tailTrace_4076384 : CollatzResearch.WordTrace tailWord_4076384 prefixEnd_4076384 697714774765828120851019 := by
  unfold tailWord_4076384
  simp only [CollatzResearch.WordTrace]
  refine ⟨74338969431982216902858103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99118625909309622537144137 74338969431982216902858103)
  ·
    refine ⟨111508454147973325354287155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74338969431982216902858103 111508454147973325354287155)
    ·
      refine ⟨167262681221959988031430733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111508454147973325354287155 167262681221959988031430733)
      ·
        refine ⟨62723505458234995511786525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167262681221959988031430733 62723505458234995511786525)
        ·
          refine ⟨23521314546838123316919947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62723505458234995511786525 23521314546838123316919947)
          ·
            refine ⟨35281971820257184975379921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23521314546838123316919947 35281971820257184975379921)
            ·
              refine ⟨26461478865192888731534941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35281971820257184975379921 26461478865192888731534941)
              ·
                refine ⟨9923054574447333274325603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26461478865192888731534941 9923054574447333274325603)
                ·
                  refine ⟨14884581861670999911488405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9923054574447333274325603 14884581861670999911488405)
                  ·
                    refine ⟨697714774765828120851019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14884581861670999911488405 697714774765828120851019)
                    ·
                      rfl

theorem cell23_4076384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_4076384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076384 prefixEnd_4076384 := by exact prefixLift 4076384
  have htrace : WordTrace (prefixWord ++ tailWord_4076384) baseStart_4076384 baseEnd_4076384 := by
    simpa [prefixWord, tailWord_4076384, baseEnd_4076384] using wordTrace_append hprefix tailTrace_4076384
  have hstable : (prefixWord ++ tailWord_4076384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076384).length < 2 ^ (prefixWord ++ tailWord_4076384).sum := by decide
  have hdescent : baseEnd_4076384 < baseStart_4076384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076388 : List Nat := [2, 3, 1, 1, 4, 3, 1, 2, 1, 5]
def baseStart_4076388 : Nat := 118140960795 + 4076388 * 2 ^ 59
def prefixEnd_4076388 : Nat := 4983230072969 + 3 ^ 40 * 4076388 * 2
def baseEnd_4076388 : Nat := 697715459406700782301013

theorem tailTrace_4076388 : CollatzResearch.WordTrace tailWord_4076388 prefixEnd_4076388 697715459406700782301013 := by
  unfold tailWord_4076388
  simp only [CollatzResearch.WordTrace]
  refine ⟨74339042377974971244430909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99118723170633294992574545 74339042377974971244430909)
  ·
    refine ⟨27877140891740614216661591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74339042377974971244430909 27877140891740614216661591)
    ·
      refine ⟨41815711337610921324992387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27877140891740614216661591 41815711337610921324992387)
      ·
        refine ⟨62723567006416381987488581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41815711337610921324992387 62723567006416381987488581)
        ·
          refine ⟨11760668813703071622654109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62723567006416381987488581 11760668813703071622654109)
          ·
            refine ⟨4410250805138651858495291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11760668813703071622654109 4410250805138651858495291)
            ·
              refine ⟨6615376207707977787742937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410250805138651858495291 6615376207707977787742937)
              ·
                refine ⟨4961532155780983340807203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6615376207707977787742937 4961532155780983340807203)
                ·
                  refine ⟨7442298233671475011210805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961532155780983340807203 7442298233671475011210805)
                  ·
                    refine ⟨697715459406700782301013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442298233671475011210805 697715459406700782301013)
                    ·
                      rfl

theorem cell23_4076388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 2, 1, 5].length) (baseStart_4076388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076388 prefixEnd_4076388 := by exact prefixLift 4076388
  have htrace : WordTrace (prefixWord ++ tailWord_4076388) baseStart_4076388 baseEnd_4076388 := by
    simpa [prefixWord, tailWord_4076388, baseEnd_4076388] using wordTrace_append hprefix tailTrace_4076388
  have hstable : (prefixWord ++ tailWord_4076388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076388).length < 2 ^ (prefixWord ++ tailWord_4076388).sum := by decide
  have hdescent : baseEnd_4076388 < baseStart_4076388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076391 : List Nat := [1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_4076391 : Nat := 118140960795 + 4076391 * 2 ^ 59
def prefixEnd_4076391 : Nat := 4983230072969 + 3 ^ 40 * 4076391 * 2
def baseEnd_4076391 : Nat := 2093147918662065835165525

theorem tailTrace_4076391 : CollatzResearch.WordTrace tailWord_4076391 prefixEnd_4076391 2093147918662065835165525 := by
  unfold tailWord_4076391
  simp only [CollatzResearch.WordTrace]
  refine ⟨148678194174939074001221027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99118796116626049334147351 148678194174939074001221027)
  ·
    refine ⟨223017291262408611001831541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148678194174939074001221027 223017291262408611001831541)
    ·
      refine ⟨20907871055850807281421707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 223017291262408611001831541 20907871055850807281421707)
      ·
        refine ⟨31361806583776210922132561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20907871055850807281421707 31361806583776210922132561)
        ·
          refine ⟨23521354937832158191599421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31361806583776210922132561 23521354937832158191599421)
          ·
            refine ⟨8820508101687059321849783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23521354937832158191599421 8820508101687059321849783)
            ·
              refine ⟨13230762152530588982774675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820508101687059321849783 13230762152530588982774675)
              ·
                refine ⟨19846143228795883474162013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13230762152530588982774675 19846143228795883474162013)
                ·
                  refine ⟨7442303710798456302810755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19846143228795883474162013 7442303710798456302810755)
                  ·
                    refine ⟨11163455566197684454216133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442303710798456302810755 11163455566197684454216133)
                    ·
                      refine ⟨2093147918662065835165525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11163455566197684454216133 2093147918662065835165525)
                      ·
                        rfl

theorem cell23_4076391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_4076391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076391 prefixEnd_4076391 := by exact prefixLift 4076391
  have htrace : WordTrace (prefixWord ++ tailWord_4076391) baseStart_4076391 baseEnd_4076391 := by
    simpa [prefixWord, tailWord_4076391, baseEnd_4076391] using wordTrace_append hprefix tailTrace_4076391
  have hstable : (prefixWord ++ tailWord_4076391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076391).length < 2 ^ (prefixWord ++ tailWord_4076391).sum := by decide
  have hdescent : baseEnd_4076391 < baseStart_4076391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076411 : List Nat := [1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 3]
def baseStart_4076411 : Nat := 118140960795 + 4076411 * 2 ^ 59
def prefixEnd_4076411 : Nat := 4983230072969 + 3 ^ 40 * 4076411 * 2
def baseEnd_4076411 : Nat := 2093158188275155756915433

theorem tailTrace_4076411 : CollatzResearch.WordTrace tailWord_4076411 prefixEnd_4076411 2093158188275155756915433 := by
  unfold tailWord_4076411
  simp only [CollatzResearch.WordTrace]
  refine ⟨148678923634866617416949087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99119282423244411611299391 148678923634866617416949087)
  ·
    refine ⟨223018385452299926125423631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148678923634866617416949087 223018385452299926125423631)
    ·
      refine ⟨334527578178449889188135447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223018385452299926125423631 334527578178449889188135447)
      ·
        refine ⟨501791367267674833782203171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334527578178449889188135447 501791367267674833782203171)
        ·
          refine ⟨752687050901512250673304757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501791367267674833782203171 752687050901512250673304757)
          ·
            refine ⟨70564411022016773500622321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 752687050901512250673304757 70564411022016773500622321)
            ·
              refine ⟨52923308266512580125466741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70564411022016773500622321 52923308266512580125466741)
              ·
                refine ⟨4961560149985554386762507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52923308266512580125466741 4961560149985554386762507)
                ·
                  refine ⟨7442340224978331580143761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961560149985554386762507 7442340224978331580143761)
                  ·
                    refine ⟨5581755168733748685107821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7442340224978331580143761 5581755168733748685107821)
                    ·
                      refine ⟨2093158188275155756915433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581755168733748685107821 2093158188275155756915433)
                      ·
                        rfl

theorem cell23_4076411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 3].length) (baseStart_4076411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076411 prefixEnd_4076411 := by exact prefixLift 4076411
  have htrace : WordTrace (prefixWord ++ tailWord_4076411) baseStart_4076411 baseEnd_4076411 := by
    simpa [prefixWord, tailWord_4076411, baseEnd_4076411] using wordTrace_append hprefix tailTrace_4076411
  have hstable : (prefixWord ++ tailWord_4076411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076411).length < 2 ^ (prefixWord ++ tailWord_4076411).sum := by decide
  have hdescent : baseEnd_4076411 < baseStart_4076411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076441 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 3]
def baseStart_4076441 : Nat := 118140960795 + 4076441 * 2 ^ 59
def prefixEnd_4076441 : Nat := 4983230072969 + 3 ^ 40 * 4076441 * 2
def baseEnd_4076441 : Nat := 2093173592694790639540295

theorem tailTrace_4076441 : CollatzResearch.WordTrace tailWord_4076441 prefixEnd_4076441 2093173592694790639540295 := by
  unfold tailWord_4076441
  simp only [CollatzResearch.WordTrace]
  refine ⟨148680017824757932540541177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99120011883171955027027451 148680017824757932540541177)
  ·
    refine ⟨111510013368568449405405883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148680017824757932540541177 111510013368568449405405883)
    ·
      refine ⟨167265020052852674108108825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111510013368568449405405883 167265020052852674108108825)
      ·
        refine ⟨125448765039639505581081619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167265020052852674108108825 125448765039639505581081619)
        ·
          refine ⟨188173147559459258371622429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125448765039639505581081619 188173147559459258371622429)
          ·
            refine ⟨70564930334797221889358411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188173147559459258371622429 70564930334797221889358411)
            ·
              refine ⟨105847395502195832834037617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70564930334797221889358411 105847395502195832834037617)
              ·
                refine ⟨79385546626646874625528213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105847395502195832834037617 79385546626646874625528213)
                ·
                  refine ⟨3721197498124072248071635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79385546626646874625528213 3721197498124072248071635)
                  ·
                    refine ⟨5581796247186108372107453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721197498124072248071635 5581796247186108372107453)
                    ·
                      refine ⟨2093173592694790639540295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5581796247186108372107453 2093173592694790639540295)
                      ·
                        rfl

theorem cell23_4076441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 6, 1, 3].length) (baseStart_4076441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076441 prefixEnd_4076441 := by exact prefixLift 4076441
  have htrace : WordTrace (prefixWord ++ tailWord_4076441) baseStart_4076441 baseEnd_4076441 := by
    simpa [prefixWord, tailWord_4076441, baseEnd_4076441] using wordTrace_append hprefix tailTrace_4076441
  have hstable : (prefixWord ++ tailWord_4076441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076441).length < 2 ^ (prefixWord ++ tailWord_4076441).sum := by decide
  have hdescent : baseEnd_4076441 < baseStart_4076441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076474 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 4, 6]
def baseStart_4076474 : Nat := 118140960795 + 4076474 * 2 ^ 59
def prefixEnd_4076474 : Nat := 4983230072969 + 3 ^ 40 * 4076474 * 2
def baseEnd_4076474 : Nat := 697730179185463003475881

theorem tailTrace_4076474 : CollatzResearch.WordTrace tailWord_4076474 prefixEnd_4076474 697730179185463003475881 := by
  unfold tailWord_4076474
  simp only [CollatzResearch.WordTrace]
  refine ⟨37170305358409594794123119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99120814289092252784328317 37170305358409594794123119)
  ·
    refine ⟨55755458037614392191184679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37170305358409594794123119 55755458037614392191184679)
    ·
      refine ⟨83633187056421588286777019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55755458037614392191184679 83633187056421588286777019)
      ·
        refine ⟨125449780584632382430165529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83633187056421588286777019 125449780584632382430165529)
        ·
          refine ⟨94087335438474286822624147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125449780584632382430165529 94087335438474286822624147)
          ·
            refine ⟨141131003157711430233936221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94087335438474286822624147 141131003157711430233936221)
            ·
              refine ⟨52924126184141786337726083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141131003157711430233936221 52924126184141786337726083)
              ·
                refine ⟨79386189276212679506589125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52924126184141786337726083 79386189276212679506589125)
                ·
                  refine ⟨14884910489289877407485461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79386189276212679506589125 14884910489289877407485461)
                  ·
                    refine ⟨697730179185463003475881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14884910489289877407485461 697730179185463003475881)
                    ·
                      rfl

theorem cell23_4076474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_4076474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076474 prefixEnd_4076474 := by exact prefixLift 4076474
  have htrace : WordTrace (prefixWord ++ tailWord_4076474) baseStart_4076474 baseEnd_4076474 := by
    simpa [prefixWord, tailWord_4076474, baseEnd_4076474] using wordTrace_append hprefix tailTrace_4076474
  have hstable : (prefixWord ++ tailWord_4076474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076474).length < 2 ^ (prefixWord ++ tailWord_4076474).sum := by decide
  have hdescent : baseEnd_4076474 < baseStart_4076474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076486 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_4076486 : Nat := 118140960795 + 4076486 * 2 ^ 59
def prefixEnd_4076486 : Nat := 4983230072969 + 3 ^ 40 * 4076486 * 2
def baseEnd_4076486 : Nat := 697732233108080987825863

theorem tailTrace_4076486 : CollatzResearch.WordTrace tailWord_4076486 prefixEnd_4076486 697732233108080987825863 := by
  unfold tailWord_4076486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4646301847174840788310291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99121106073063270150619541 4646301847174840788310291)
  ·
    refine ⟨6969452770762261182465437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4646301847174840788310291 6969452770762261182465437)
    ·
      refine ⟨2613544789035847943424539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6969452770762261182465437 2613544789035847943424539)
      ·
        refine ⟨3920317183553771915136809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2613544789035847943424539 3920317183553771915136809)
        ·
          refine ⟨2940237887665328936352607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3920317183553771915136809 2940237887665328936352607)
          ·
            refine ⟨4410356831497993404528911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940237887665328936352607 4410356831497993404528911)
            ·
              refine ⟨6615535247246990106793367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410356831497993404528911 6615535247246990106793367)
              ·
                refine ⟨9923302870870485160190051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615535247246990106793367 9923302870870485160190051)
                ·
                  refine ⟨14884954306305727740285077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9923302870870485160190051 14884954306305727740285077)
                  ·
                    refine ⟨697732233108080987825863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14884954306305727740285077 697732233108080987825863)
                    ·
                      rfl

theorem cell23_4076486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_4076486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076486 prefixEnd_4076486 := by exact prefixLift 4076486
  have htrace : WordTrace (prefixWord ++ tailWord_4076486) baseStart_4076486 baseEnd_4076486 := by
    simpa [prefixWord, tailWord_4076486, baseEnd_4076486] using wordTrace_append hprefix tailTrace_4076486
  have hstable : (prefixWord ++ tailWord_4076486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076486).length < 2 ^ (prefixWord ++ tailWord_4076486).sum := by decide
  have hdescent : baseEnd_4076486 < baseStart_4076486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076502 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_4076502 : Nat := 118140960795 + 4076502 * 2 ^ 59
def prefixEnd_4076502 : Nat := 4983230072969 + 3 ^ 40 * 4076502 * 2
def baseEnd_4076502 : Nat := 2093204915014714900877515

theorem tailTrace_4076502 : CollatzResearch.WordTrace tailWord_4076502 prefixEnd_4076502 2093204915014714900877515 := by
  unfold tailWord_4076502
  simp only [CollatzResearch.WordTrace]
  refine ⟨9292640167346058747406985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99121495118357959972341173 9292640167346058747406985)
  ·
    refine ⟨6969480125509544060555239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9292640167346058747406985 6969480125509544060555239)
    ·
      refine ⟨10454220188264316090832859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6969480125509544060555239 10454220188264316090832859)
      ·
        refine ⟨15681330282396474136249289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10454220188264316090832859 15681330282396474136249289)
        ·
          refine ⟨11760997711797355602186967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15681330282396474136249289 11760997711797355602186967)
          ·
            refine ⟨17641496567696033403280451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11760997711797355602186967 17641496567696033403280451)
            ·
              refine ⟨26462244851544050104920677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17641496567696033403280451 26462244851544050104920677)
              ·
                refine ⟨4961670909664509394672627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26462244851544050104920677 4961670909664509394672627)
                ·
                  refine ⟨7442506364496764092008941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961670909664509394672627 7442506364496764092008941)
                  ·
                    refine ⟨2790939886686286534503353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7442506364496764092008941 2790939886686286534503353)
                    ·
                      refine ⟨2093204915014714900877515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790939886686286534503353 2093204915014714900877515)
                      ·
                        rfl

theorem cell23_4076502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_4076502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076502 prefixEnd_4076502 := by exact prefixLift 4076502
  have htrace : WordTrace (prefixWord ++ tailWord_4076502) baseStart_4076502 baseEnd_4076502 := by
    simpa [prefixWord, tailWord_4076502, baseEnd_4076502] using wordTrace_append hprefix tailTrace_4076502
  have hstable : (prefixWord ++ tailWord_4076502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076502).length < 2 ^ (prefixWord ++ tailWord_4076502).sum := by decide
  have hdescent : baseEnd_4076502 < baseStart_4076502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076524 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_4076524 : Nat := 118140960795 + 4076524 * 2 ^ 59
def prefixEnd_4076524 : Nat := 4983230072969 + 3 ^ 40 * 4076524 * 2
def baseEnd_4076524 : Nat := 2093216211589113814802413

theorem tailTrace_4076524 : CollatzResearch.WordTrace tailWord_4076524 prefixEnd_4076524 2093216211589113814802413 := by
  unfold tailWord_4076524
  simp only [CollatzResearch.WordTrace]
  refine ⟨74341522541728618857906313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99122030055638158477208417 74341522541728618857906313)
  ·
    refine ⟨55756141906296464143429735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74341522541728618857906313 55756141906296464143429735)
    ·
      refine ⟨83634212859444696215144603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55756141906296464143429735 83634212859444696215144603)
      ·
        refine ⟨125451319289167044322716905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83634212859444696215144603 125451319289167044322716905)
        ·
          refine ⟨94088489466875283242037679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125451319289167044322716905 94088489466875283242037679)
          ·
            refine ⟨141132734200312924863056519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94088489466875283242037679 141132734200312924863056519)
            ·
              refine ⟨211699101300469387294584779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141132734200312924863056519 211699101300469387294584779)
              ·
                refine ⟨317548651950704080941877169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211699101300469387294584779 317548651950704080941877169)
                ·
                  refine ⟨238161488963028060706407877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 317548651950704080941877169 238161488963028060706407877)
                  ·
                    refine ⟨44655279180567761382451477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238161488963028060706407877 44655279180567761382451477)
                    ·
                      refine ⟨2093216211589113814802413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44655279180567761382451477 2093216211589113814802413)
                      ·
                        rfl

theorem cell23_4076524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_4076524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076524 prefixEnd_4076524 := by exact prefixLift 4076524
  have htrace : WordTrace (prefixWord ++ tailWord_4076524) baseStart_4076524 baseEnd_4076524 := by
    simpa [prefixWord, tailWord_4076524, baseEnd_4076524] using wordTrace_append hprefix tailTrace_4076524
  have hstable : (prefixWord ++ tailWord_4076524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076524).length < 2 ^ (prefixWord ++ tailWord_4076524).sum := by decide
  have hdescent : baseEnd_4076524 < baseStart_4076524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076551 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 4, 5]
def baseStart_4076551 : Nat := 118140960795 + 4076551 * 2 ^ 59
def prefixEnd_4076551 : Nat := 4983230072969 + 3 ^ 40 * 4076551 * 2
def baseEnd_4076551 : Nat := 697743358522261736388263

theorem tailTrace_4076551 : CollatzResearch.WordTrace tailWord_4076551 prefixEnd_4076551 697743358522261736388263 := by
  unfold tailWord_4076551
  simp only [CollatzResearch.WordTrace]
  refine ⟨148684029854359421327045507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99122686569572947551363671 148684029854359421327045507)
  ·
    refine ⟨223026044781539131990568261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148684029854359421327045507 223026044781539131990568261)
    ·
      refine ⟨41817383396538587248231549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223026044781539131990568261 41817383396538587248231549)
      ·
        refine ⟨15681518773701970218086831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41817383396538587248231549 15681518773701970218086831)
        ·
          refine ⟨23522278160552955327130247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15681518773701970218086831 23522278160552955327130247)
          ·
            refine ⟨35283417240829432990695371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23522278160552955327130247 35283417240829432990695371)
            ·
              refine ⟨52925125861244149486043057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35283417240829432990695371 52925125861244149486043057)
              ·
                refine ⟨39693844395933112114532293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52925125861244149486043057 39693844395933112114532293)
                ·
                  refine ⟨7442595824237458521474805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39693844395933112114532293 7442595824237458521474805)
                  ·
                    refine ⟨697743358522261736388263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442595824237458521474805 697743358522261736388263)
                    ·
                      rfl

theorem cell23_4076551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_4076551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076551 prefixEnd_4076551 := by exact prefixLift 4076551
  have htrace : WordTrace (prefixWord ++ tailWord_4076551) baseStart_4076551 baseEnd_4076551 := by
    simpa [prefixWord, tailWord_4076551, baseEnd_4076551] using wordTrace_append hprefix tailTrace_4076551
  have hstable : (prefixWord ++ tailWord_4076551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076551).length < 2 ^ (prefixWord ++ tailWord_4076551).sum := by decide
  have hdescent : baseEnd_4076551 < baseStart_4076551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076568 : List Nat := [2, 1, 2, 3, 2, 3, 2, 1, 2, 5]
def baseStart_4076568 : Nat := 118140960795 + 4076568 * 2 ^ 59
def prefixEnd_4076568 : Nat := 4983230072969 + 3 ^ 40 * 4076568 * 2
def baseEnd_4076568 : Nat := 697746268245970547550737

theorem tailTrace_4076568 : CollatzResearch.WordTrace tailWord_4076568 prefixEnd_4076568 697746268245970547550737 := by
  unfold tailWord_4076568
  simp only [CollatzResearch.WordTrace]
  refine ⟨74342324947648916615207179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99123099930198555486942905 74342324947648916615207179)
  ·
    refine ⟨111513487421473374922810769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74342324947648916615207179 111513487421473374922810769)
    ·
      refine ⟨83635115566105031192108077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111513487421473374922810769 83635115566105031192108077)
      ·
        refine ⟨31363168337289386697040529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83635115566105031192108077 31363168337289386697040529)
        ·
          refine ⟨23522376252967040022780397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31363168337289386697040529 23522376252967040022780397)
          ·
            refine ⟨8820891094862640008542649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23522376252967040022780397 8820891094862640008542649)
            ·
              refine ⟨6615668321146980006406987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8820891094862640008542649 6615668321146980006406987)
              ·
                refine ⟨9923502481720470009610481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615668321146980006406987 9923502481720470009610481)
                ·
                  refine ⟨7442626861290352507207861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9923502481720470009610481 7442626861290352507207861)
                  ·
                    refine ⟨697746268245970547550737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442626861290352507207861 697746268245970547550737)
                    ·
                      rfl

theorem cell23_4076568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_4076568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076568 prefixEnd_4076568 := by exact prefixLift 4076568
  have htrace : WordTrace (prefixWord ++ tailWord_4076568) baseStart_4076568 baseEnd_4076568 := by
    simpa [prefixWord, tailWord_4076568, baseEnd_4076568] using wordTrace_append hprefix tailTrace_4076568
  have hstable : (prefixWord ++ tailWord_4076568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076568).length < 2 ^ (prefixWord ++ tailWord_4076568).sum := by decide
  have hdescent : baseEnd_4076568 < baseStart_4076568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076588 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 2, 4, 2]
def baseStart_4076588 : Nat := 118140960795 + 4076588 * 2 ^ 59
def prefixEnd_4076588 : Nat := 4983230072969 + 3 ^ 40 * 4076588 * 2
def baseEnd_4076588 : Nat := 2093249074351001564402119

theorem tailTrace_4076588 : CollatzResearch.WordTrace tailWord_4076588 prefixEnd_4076588 2093249074351001564402119 := by
  unfold tailWord_4076588
  simp only [CollatzResearch.WordTrace]
  refine ⟨74342689677612688323071209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99123586236816917764094945 74342689677612688323071209)
  ·
    refine ⟨55757017258209516242303407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74342689677612688323071209 55757017258209516242303407)
    ·
      refine ⟨83635525887314274363455111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55757017258209516242303407 83635525887314274363455111)
      ·
        refine ⟨125453288830971411545182667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83635525887314274363455111 125453288830971411545182667)
        ·
          refine ⟨188179933246457117317774001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125453288830971411545182667 188179933246457117317774001)
          ·
            refine ⟨141134949934842837988330501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188179933246457117317774001 141134949934842837988330501)
            ·
              refine ⟨26462803112783032122811969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141134949934842837988330501 26462803112783032122811969)
              ·
                refine ⟨19847102334587274092108977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26462803112783032122811969 19847102334587274092108977)
                ·
                  refine ⟨14885326750940455569081733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19847102334587274092108977 14885326750940455569081733)
                  ·
                    refine ⟨2790998765801335419202825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14885326750940455569081733 2790998765801335419202825)
                    ·
                      refine ⟨2093249074351001564402119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2790998765801335419202825 2093249074351001564402119)
                      ·
                        rfl

theorem cell23_4076588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 4, 2].length) (baseStart_4076588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076588 prefixEnd_4076588 := by exact prefixLift 4076588
  have htrace : WordTrace (prefixWord ++ tailWord_4076588) baseStart_4076588 baseEnd_4076588 := by
    simpa [prefixWord, tailWord_4076588, baseEnd_4076588] using wordTrace_append hprefix tailTrace_4076588
  have hstable : (prefixWord ++ tailWord_4076588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076588).length < 2 ^ (prefixWord ++ tailWord_4076588).sum := by decide
  have hdescent : baseEnd_4076588 < baseStart_4076588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076605 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 2, 4, 2]
def baseStart_4076605 : Nat := 118140960795 + 4076605 * 2 ^ 59
def prefixEnd_4076605 : Nat := 4983230072969 + 3 ^ 40 * 4076605 * 2
def baseEnd_4076605 : Nat := 2093257803522127997889541

theorem tailTrace_4076605 : CollatzResearch.WordTrace tailWord_4076605 prefixEnd_4076605 2093257803522127997889541 := by
  unfold tailWord_4076605
  simp only [CollatzResearch.WordTrace]
  refine ⟨148685999396163788549511269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99123999597442525699674179 148685999396163788549511269)
  ·
    refine ⟨27878624886780710353033363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148685999396163788549511269 27878624886780710353033363)
    ·
      refine ⟨41817937330171065529550045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27878624886780710353033363 41817937330171065529550045)
      ·
        refine ⟨15681726498814149573581267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41817937330171065529550045 15681726498814149573581267)
        ·
          refine ⟨23522589748221224360371901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15681726498814149573581267 23522589748221224360371901)
          ·
            refine ⟨8820971155582959135139463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23522589748221224360371901 8820971155582959135139463)
            ·
              refine ⟨13231456733374438702709195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8820971155582959135139463 13231456733374438702709195)
              ·
                refine ⟨19847185100061658054063793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13231456733374438702709195 19847185100061658054063793)
                ·
                  refine ⟨14885388825046243540547845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19847185100061658054063793 14885388825046243540547845)
                  ·
                    refine ⟨2791010404696170663852721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14885388825046243540547845 2791010404696170663852721)
                    ·
                      refine ⟨2093257803522127997889541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791010404696170663852721 2093257803522127997889541)
                      ·
                        rfl

theorem cell23_4076605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_4076605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076605 prefixEnd_4076605 := by exact prefixLift 4076605
  have htrace : WordTrace (prefixWord ++ tailWord_4076605) baseStart_4076605 baseEnd_4076605 := by
    simpa [prefixWord, tailWord_4076605, baseEnd_4076605] using wordTrace_append hprefix tailTrace_4076605
  have hstable : (prefixWord ++ tailWord_4076605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076605).length < 2 ^ (prefixWord ++ tailWord_4076605).sum := by decide
  have hdescent : baseEnd_4076605 < baseStart_4076605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076611 : List Nat := [1, 1, 1, 3, 1, 2, 3, 5, 6]
def baseStart_4076611 : Nat := 118140960795 + 4076611 * 2 ^ 59
def prefixEnd_4076611 : Nat := 4983230072969 + 3 ^ 40 * 4076611 * 2
def baseEnd_4076611 : Nat := 232584542711783886046057

theorem tailTrace_4076611 : CollatzResearch.WordTrace tailWord_4076611 prefixEnd_4076611 232584542711783886046057 := by
  unfold tailWord_4076611
  simp only [CollatzResearch.WordTrace]
  refine ⟨148686218234142051574229687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99124145489428034382819791 148686218234142051574229687)
  ·
    refine ⟨223029327351213077361344531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148686218234142051574229687 223029327351213077361344531)
    ·
      refine ⟨334543991026819616042016797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223029327351213077361344531 334543991026819616042016797)
      ·
        refine ⟨125453996635057356015756299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334543991026819616042016797 125453996635057356015756299)
        ·
          refine ⟨188180994952586034023634449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125453996635057356015756299 188180994952586034023634449)
          ·
            refine ⟨141135746214439525517725837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188180994952586034023634449 141135746214439525517725837)
            ·
              refine ⟨52925904830414822069147189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141135746214439525517725837 52925904830414822069147189)
              ·
                refine ⟨4961803577851389568982549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52925904830414822069147189 4961803577851389568982549)
                ·
                  refine ⟨232584542711783886046057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4961803577851389568982549 232584542711783886046057)
                  ·
                    rfl

theorem cell23_4076611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 5, 6].length) (baseStart_4076611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076611 prefixEnd_4076611 := by exact prefixLift 4076611
  have htrace : WordTrace (prefixWord ++ tailWord_4076611) baseStart_4076611 baseEnd_4076611 := by
    simpa [prefixWord, tailWord_4076611, baseEnd_4076611] using wordTrace_append hprefix tailTrace_4076611
  have hstable : (prefixWord ++ tailWord_4076611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076611).length < 2 ^ (prefixWord ++ tailWord_4076611).sum := by decide
  have hdescent : baseEnd_4076611 < baseStart_4076611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076655 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 3]
def baseStart_4076655 : Nat := 118140960795 + 4076655 * 2 ^ 59
def prefixEnd_4076655 : Nat := 4983230072969 + 3 ^ 40 * 4076655 * 2
def baseEnd_4076655 : Nat := 2093283477554852802264311

theorem tailTrace_4076655 : CollatzResearch.WordTrace tailWord_4076655 prefixEnd_4076655 2093283477554852802264311 := by
  unfold tailWord_4076655
  simp only [CollatzResearch.WordTrace]
  refine ⟨148687823045982647088831419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99125215363988431392554279 148687823045982647088831419)
  ·
    refine ⟨223031734568973970633247129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148687823045982647088831419 223031734568973970633247129)
    ·
      refine ⟨167273800926730477974935347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223031734568973970633247129 167273800926730477974935347)
      ·
        refine ⟨250910701390095716962403021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167273800926730477974935347 250910701390095716962403021)
        ·
          refine ⟨94091513021285893860901133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250910701390095716962403021 94091513021285893860901133)
          ·
            refine ⟨35284317382982210197837925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94091513021285893860901133 35284317382982210197837925)
            ·
              refine ⟨6615809509309164412094611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35284317382982210197837925 6615809509309164412094611)
              ·
                refine ⟨9923714263963746618141917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615809509309164412094611 9923714263963746618141917)
                ·
                  refine ⟨3721392848986404981803219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9923714263963746618141917 3721392848986404981803219)
                  ·
                    refine ⟨5582089273479607472704829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721392848986404981803219 5582089273479607472704829)
                    ·
                      refine ⟨2093283477554852802264311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582089273479607472704829 2093283477554852802264311)
                      ·
                        rfl

theorem cell23_4076655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 3, 1, 3].length) (baseStart_4076655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076655 prefixEnd_4076655 := by exact prefixLift 4076655
  have htrace : WordTrace (prefixWord ++ tailWord_4076655) baseStart_4076655 baseEnd_4076655 := by
    simpa [prefixWord, tailWord_4076655, baseEnd_4076655] using wordTrace_append hprefix tailTrace_4076655
  have hstable : (prefixWord ++ tailWord_4076655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076655).length < 2 ^ (prefixWord ++ tailWord_4076655).sum := by decide
  have hdescent : baseEnd_4076655 < baseStart_4076655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076695 : List Nat := [1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 4]
def baseStart_4076695 : Nat := 118140960795 + 4076695 * 2 ^ 59
def prefixEnd_4076695 : Nat := 4983230072969 + 3 ^ 40 * 4076695 * 2
def baseEnd_4076695 : Nat := 2093304016781032645764127

theorem tailTrace_4076695 : CollatzResearch.WordTrace tailWord_4076695 prefixEnd_4076695 2093304016781032645764127 := by
  unfold tailWord_4076695
  simp only [CollatzResearch.WordTrace]
  refine ⟨148689281965837733920287539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99126187977225155946858359 148689281965837733920287539)
  ·
    refine ⟨223033922948756600880431309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148689281965837733920287539 223033922948756600880431309)
    ·
      refine ⟨83637721105783725330161741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223033922948756600880431309 83637721105783725330161741)
      ·
        refine ⟨31364145414668896998810653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83637721105783725330161741 31364145414668896998810653)
        ·
          refine ⟨11761554530500836374553995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31364145414668896998810653 11761554530500836374553995)
          ·
            refine ⟨17642331795751254561830993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761554530500836374553995 17642331795751254561830993)
            ·
              refine ⟨13231748846813440921373245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17642331795751254561830993 13231748846813440921373245)
              ·
                refine ⟨4961905817555040345514967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13231748846813440921373245 4961905817555040345514967)
                ·
                  refine ⟨7442858726332560518272451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961905817555040345514967 7442858726332560518272451)
                  ·
                    refine ⟨11164288089498840777408677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7442858726332560518272451 11164288089498840777408677)
                    ·
                      refine ⟨2093304016781032645764127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11164288089498840777408677 2093304016781032645764127)
                      ·
                        rfl

theorem cell23_4076695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_4076695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076695 prefixEnd_4076695 := by exact prefixLift 4076695
  have htrace : WordTrace (prefixWord ++ tailWord_4076695) baseStart_4076695 baseEnd_4076695 := by
    simpa [prefixWord, tailWord_4076695, baseEnd_4076695] using wordTrace_append hprefix tailTrace_4076695
  have hstable : (prefixWord ++ tailWord_4076695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076695).length < 2 ^ (prefixWord ++ tailWord_4076695).sum := by decide
  have hdescent : baseEnd_4076695 < baseStart_4076695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076705 : List Nat := [1, 2, 3, 3, 1, 1, 2, 4, 2, 4]
def baseStart_4076705 : Nat := 118140960795 + 4076705 * 2 ^ 59
def prefixEnd_4076705 : Nat := 4983230072969 + 3 ^ 40 * 4076705 * 2
def baseEnd_4076705 : Nat := 697769717195859202213027

theorem tailTrace_4076705 : CollatzResearch.WordTrace tailWord_4076705 prefixEnd_4076705 697769717195859202213027 := by
  unfold tailWord_4076705
  simp only [CollatzResearch.WordTrace]
  refine ⟨148689646695801505628151569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99126431130534337085434379 148689646695801505628151569)
  ·
    refine ⟨111517235021851129221113677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148689646695801505628151569 111517235021851129221113677)
    ·
      refine ⟨41818963133194173457917629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111517235021851129221113677 41818963133194173457917629)
      ·
        refine ⟨15682111174947815046719111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41818963133194173457917629 15682111174947815046719111)
        ·
          refine ⟨23523166762421722570078667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15682111174947815046719111 23523166762421722570078667)
          ·
            refine ⟨35284750143632583855118001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23523166762421722570078667 35284750143632583855118001)
            ·
              refine ⟨26463562607724437891338501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35284750143632583855118001 26463562607724437891338501)
              ·
                refine ⟨4961917988948332104625969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26463562607724437891338501 4961917988948332104625969)
                ·
                  refine ⟨3721438491711249078469477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4961917988948332104625969 3721438491711249078469477)
                  ·
                    refine ⟨697769717195859202213027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721438491711249078469477 697769717195859202213027)
                    ·
                      rfl

theorem cell23_4076705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 4].length) (baseStart_4076705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076705 prefixEnd_4076705 := by exact prefixLift 4076705
  have htrace : WordTrace (prefixWord ++ tailWord_4076705) baseStart_4076705 baseEnd_4076705 := by
    simpa [prefixWord, tailWord_4076705, baseEnd_4076705] using wordTrace_append hprefix tailTrace_4076705
  have hstable : (prefixWord ++ tailWord_4076705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076705).length < 2 ^ (prefixWord ++ tailWord_4076705).sum := by decide
  have hdescent : baseEnd_4076705 < baseStart_4076705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076706 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4076706 : Nat := 118140960795 + 4076706 * 2 ^ 59
def prefixEnd_4076706 : Nat := 4983230072969 + 3 ^ 40 * 4076706 * 2
def baseEnd_4076706 : Nat := 2093309665068232102726577

theorem tailTrace_4076706 : CollatzResearch.WordTrace tailWord_4076706 prefixEnd_4076706 2093309665068232102726577 := by
  unfold tailWord_4076706
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172420792199470699734493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99126455445865255199291981 37172420792199470699734493)
  ·
    refine ⟨13939657797074801512400435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37172420792199470699734493 13939657797074801512400435)
    ·
      refine ⟨20909486695612202268600653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13939657797074801512400435 20909486695612202268600653)
      ·
        refine ⟨7841057510854575850725245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20909486695612202268600653 7841057510854575850725245)
        ·
          refine ⟨2940396566570465944021967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7841057510854575850725245 2940396566570465944021967)
          ·
            refine ⟨4410594849855698916032951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940396566570465944021967 4410594849855698916032951)
            ·
              refine ⟨6615892274783548374049427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410594849855698916032951 6615892274783548374049427)
              ·
                refine ⟨9923838412175322561074141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6615892274783548374049427 9923838412175322561074141)
                ·
                  refine ⟨3721439404565745960402803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9923838412175322561074141 3721439404565745960402803)
                  ·
                    refine ⟨5582159106848618940604205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721439404565745960402803 5582159106848618940604205)
                    ·
                      refine ⟨2093309665068232102726577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582159106848618940604205 2093309665068232102726577)
                      ·
                        rfl

theorem cell23_4076706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4076706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076706 prefixEnd_4076706 := by exact prefixLift 4076706
  have htrace : WordTrace (prefixWord ++ tailWord_4076706) baseStart_4076706 baseEnd_4076706 := by
    simpa [prefixWord, tailWord_4076706, baseEnd_4076706] using wordTrace_append hprefix tailTrace_4076706
  have hstable : (prefixWord ++ tailWord_4076706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076706).length < 2 ^ (prefixWord ++ tailWord_4076706).sum := by decide
  have hdescent : baseEnd_4076706 < baseStart_4076706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076708 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_4076708 : Nat := 118140960795 + 4076708 * 2 ^ 59
def prefixEnd_4076708 : Nat := 4983230072969 + 3 ^ 40 * 4076708 * 2
def baseEnd_4076708 : Nat := 2093310692029541094901567

theorem tailTrace_4076708 : CollatzResearch.WordTrace tailWord_4076708 prefixEnd_4076708 2093310692029541094901567 := by
  unfold tailWord_4076708
  simp only [CollatzResearch.WordTrace]
  refine ⟨74344878057395318570255389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99126504076527091427007185 74344878057395318570255389)
  ·
    refine ⟨27879329271523244463845771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74344878057395318570255389 27879329271523244463845771)
    ·
      refine ⟨41818993907284866695768657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27879329271523244463845771 41818993907284866695768657)
      ·
        refine ⟨31364245430463650021826493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41818993907284866695768657 31364245430463650021826493)
        ·
          refine ⟨11761592036423868758184935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31364245430463650021826493 11761592036423868758184935)
          ·
            refine ⟨17642388054635803137277403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761592036423868758184935 17642388054635803137277403)
            ·
              refine ⟨26463582081953704705916105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642388054635803137277403 26463582081953704705916105)
              ·
                refine ⟨19847686561465278529437079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26463582081953704705916105 19847686561465278529437079)
                ·
                  refine ⟨29771529842197917794155619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19847686561465278529437079 29771529842197917794155619)
                  ·
                    refine ⟨44657294763296876691233429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29771529842197917794155619 44657294763296876691233429)
                    ·
                      refine ⟨2093310692029541094901567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44657294763296876691233429 2093310692029541094901567)
                      ·
                        rfl

theorem cell23_4076708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_4076708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076708 prefixEnd_4076708 := by exact prefixLift 4076708
  have htrace : WordTrace (prefixWord ++ tailWord_4076708) baseStart_4076708 baseEnd_4076708 := by
    simpa [prefixWord, tailWord_4076708, baseEnd_4076708] using wordTrace_append hprefix tailTrace_4076708
  have hstable : (prefixWord ++ tailWord_4076708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076708).length < 2 ^ (prefixWord ++ tailWord_4076708).sum := by decide
  have hdescent : baseEnd_4076708 < baseStart_4076708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076722 : List Nat := [3, 2, 1, 1, 1, 4, 4, 1, 2, 4]
def baseStart_4076722 : Nat := 118140960795 + 4076722 * 2 ^ 59
def prefixEnd_4076722 : Nat := 4983230072969 + 3 ^ 40 * 4076722 * 2
def baseEnd_4076722 : Nat := 697772626919568013375501

theorem tailTrace_4076722 : CollatzResearch.WordTrace tailWord_4076722 prefixEnd_4076722 697772626919568013375501 := by
  unfold tailWord_4076722
  simp only [CollatzResearch.WordTrace]
  refine ⟨37172566684184979382880105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99126844491159945021013613 37172566684184979382880105)
  ·
    refine ⟨27879425013138734537160079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37172566684184979382880105 27879425013138734537160079)
    ·
      refine ⟨41819137519708101805740119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27879425013138734537160079 41819137519708101805740119)
      ·
        refine ⟨62728706279562152708610179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41819137519708101805740119 62728706279562152708610179)
        ·
          refine ⟨94093059419343229062915269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62728706279562152708610179 94093059419343229062915269)
          ·
            refine ⟨17642448641126855449296613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94093059419343229062915269 17642448641126855449296613)
            ·
              refine ⟨3307959120211285396743115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17642448641126855449296613 3307959120211285396743115)
              ·
                refine ⟨4961938680316928095114673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3307959120211285396743115 4961938680316928095114673)
                ·
                  refine ⟨3721454010237696071336005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4961938680316928095114673 3721454010237696071336005)
                  ·
                    refine ⟨697772626919568013375501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721454010237696071336005 697772626919568013375501)
                    ·
                      rfl

theorem cell23_4076722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 4, 1, 2, 4].length) (baseStart_4076722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076722 prefixEnd_4076722 := by exact prefixLift 4076722
  have htrace : WordTrace (prefixWord ++ tailWord_4076722) baseStart_4076722 baseEnd_4076722 := by
    simpa [prefixWord, tailWord_4076722, baseEnd_4076722] using wordTrace_append hprefix tailTrace_4076722
  have hstable : (prefixWord ++ tailWord_4076722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076722).length < 2 ^ (prefixWord ++ tailWord_4076722).sum := by decide
  have hdescent : baseEnd_4076722 < baseStart_4076722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076726 : List Nat := [5, 1, 3, 2, 1, 2, 1, 2, 1, 5]
def baseStart_4076726 : Nat := 118140960795 + 4076726 * 2 ^ 59
def prefixEnd_4076726 : Nat := 4983230072969 + 3 ^ 40 * 4076726 * 2
def baseEnd_4076726 : Nat := 697773311560440674825495

theorem tailTrace_4076726 : CollatzResearch.WordTrace tailWord_4076726 prefixEnd_4076726 697773311560440674825495 := by
  unfold tailWord_4076726
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293150789295339138416627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99126941752483617476444021 9293150789295339138416627)
  ·
    refine ⟨13939726183943008707624941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9293150789295339138416627 13939726183943008707624941)
    ·
      refine ⟨5227397318978628265359353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13939726183943008707624941 5227397318978628265359353)
      ·
        refine ⟨3920547989233971199019515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5227397318978628265359353 3920547989233971199019515)
        ·
          refine ⟨5880821983850956798529273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3920547989233971199019515 5880821983850956798529273)
          ·
            refine ⟨4410616487888217598896955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5880821983850956798529273 4410616487888217598896955)
            ·
              refine ⟨6615924731832326398345433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4410616487888217598896955 6615924731832326398345433)
              ·
                refine ⟨4961943548874244798759075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6615924731832326398345433 4961943548874244798759075)
                ·
                  refine ⟨7442915323311367198138613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961943548874244798759075 7442915323311367198138613)
                  ·
                    refine ⟨697773311560440674825495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7442915323311367198138613 697773311560440674825495)
                    ·
                      rfl

theorem cell23_4076726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_4076726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076726 prefixEnd_4076726 := by exact prefixLift 4076726
  have htrace : WordTrace (prefixWord ++ tailWord_4076726) baseStart_4076726 baseEnd_4076726 := by
    simpa [prefixWord, tailWord_4076726, baseEnd_4076726] using wordTrace_append hprefix tailTrace_4076726
  have hstable : (prefixWord ++ tailWord_4076726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076726).length < 2 ^ (prefixWord ++ tailWord_4076726).sum := by decide
  have hdescent : baseEnd_4076726 < baseStart_4076726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076731 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 4, 7]
def baseStart_4076731 : Nat := 118140960795 + 4076731 * 2 ^ 59
def prefixEnd_4076731 : Nat := 4983230072969 + 3 ^ 40 * 4076731 * 2
def baseEnd_4076731 : Nat := 697774167361531501637987

theorem tailTrace_4076731 : CollatzResearch.WordTrace tailWord_4076731 prefixEnd_4076731 697774167361531501637987 := by
  unfold tailWord_4076731
  simp only [CollatzResearch.WordTrace]
  refine ⟨148690594993707312068598047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99127063329138208045732031 148690594993707312068598047)
  ·
    refine ⟨223035892490560968102897071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148690594993707312068598047 223035892490560968102897071)
    ·
      refine ⟨334553838735841452154345607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223035892490560968102897071 334553838735841452154345607)
      ·
        refine ⟨501830758103762178231518411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334553838735841452154345607 501830758103762178231518411)
        ·
          refine ⟨752746137155643267347277617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501830758103762178231518411 752746137155643267347277617)
          ·
            refine ⟨564559602866732450510458213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752746137155643267347277617 564559602866732450510458213)
            ·
              refine ⟨105854925537512334470710915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 564559602866732450510458213 105854925537512334470710915)
              ·
                refine ⟨158782388306268501706066373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105854925537512334470710915 158782388306268501706066373)
                ·
                  refine ⟨29771697807425344069887445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158782388306268501706066373 29771697807425344069887445)
                  ·
                    refine ⟨697774167361531501637987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29771697807425344069887445 697774167361531501637987)
                    ·
                      rfl

theorem cell23_4076731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 7].length) (baseStart_4076731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076731 prefixEnd_4076731 := by exact prefixLift 4076731
  have htrace : WordTrace (prefixWord ++ tailWord_4076731) baseStart_4076731 baseEnd_4076731 := by
    simpa [prefixWord, tailWord_4076731, baseEnd_4076731] using wordTrace_append hprefix tailTrace_4076731
  have hstable : (prefixWord ++ tailWord_4076731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076731).length < 2 ^ (prefixWord ++ tailWord_4076731).sum := by decide
  have hdescent : baseEnd_4076731 < baseStart_4076731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076732 : List Nat := [2, 2, 2, 3, 2, 1, 3, 2, 1, 2, 3]
def baseStart_4076732 : Nat := 118140960795 + 4076732 * 2 ^ 59
def prefixEnd_4076732 : Nat := 4983230072969 + 3 ^ 40 * 4076732 * 2
def baseEnd_4076732 : Nat := 2093323015565249001001457

theorem tailTrace_4076732 : CollatzResearch.WordTrace tailWord_4076732 prefixEnd_4076732 2093323015565249001001457 := by
  unfold tailWord_4076732
  simp only [CollatzResearch.WordTrace]
  refine ⟨74345315733351844619692225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99127087644469126159589633 74345315733351844619692225)
  ·
    refine ⟨55758986800013883464769169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74345315733351844619692225 55758986800013883464769169)
    ·
      refine ⟨41819240100010412598576877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55758986800013883464769169 41819240100010412598576877)
      ·
        refine ⟨15682215037503904724466329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41819240100010412598576877 15682215037503904724466329)
        ·
          refine ⟨11761661278127928543349747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15682215037503904724466329 11761661278127928543349747)
          ·
            refine ⟨17642491917191892815024621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11761661278127928543349747 17642491917191892815024621)
            ·
              refine ⟨6615934468946959805634233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17642491917191892815024621 6615934468946959805634233)
              ·
                refine ⟨4961950851710219854225675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6615934468946959805634233 4961950851710219854225675)
                ·
                  refine ⟨7442926277565329781338513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4961950851710219854225675 7442926277565329781338513)
                  ·
                    refine ⟨5582194708173997336003885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7442926277565329781338513 5582194708173997336003885)
                    ·
                      refine ⟨2093323015565249001001457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582194708173997336003885 2093323015565249001001457)
                      ·
                        rfl

theorem cell23_4076732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_4076732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076732 prefixEnd_4076732 := by exact prefixLift 4076732
  have htrace : WordTrace (prefixWord ++ tailWord_4076732) baseStart_4076732 baseEnd_4076732 := by
    simpa [prefixWord, tailWord_4076732, baseEnd_4076732] using wordTrace_append hprefix tailTrace_4076732
  have hstable : (prefixWord ++ tailWord_4076732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076732).length < 2 ^ (prefixWord ++ tailWord_4076732).sum := by decide
  have hdescent : baseEnd_4076732 < baseStart_4076732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076768 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_4076768 : Nat := 118140960795 + 4076768 * 2 ^ 59
def prefixEnd_4076768 : Nat := 4983230072969 + 3 ^ 40 * 4076768 * 2
def baseEnd_4076768 : Nat := 2093341500868810860151291

theorem tailTrace_4076768 : CollatzResearch.WordTrace tailWord_4076768 prefixEnd_4076768 2093341500868810860151291 := by
  unfold tailWord_4076768
  simp only [CollatzResearch.WordTrace]
  refine ⟨74345972247286633693847479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99127962996382178258463305 74345972247286633693847479)
  ·
    refine ⟨111518958370929950540771219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74345972247286633693847479 111518958370929950540771219)
    ·
      refine ⟨167278437556394925811156829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111518958370929950540771219 167278437556394925811156829)
      ·
        refine ⟨62729414083648097179183811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167278437556394925811156829 62729414083648097179183811)
        ·
          refine ⟨94094121125472145768775717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62729414083648097179183811 94094121125472145768775717)
          ·
            refine ⟨17642647711026027331645447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 94094121125472145768775717 17642647711026027331645447)
            ·
              refine ⟨26463971566539040997468171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642647711026027331645447 26463971566539040997468171)
              ·
                refine ⟨39695957349808561496202257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26463971566539040997468171 39695957349808561496202257)
                ·
                  refine ⟨29771968012356421122151693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39695957349808561496202257 29771968012356421122151693)
                  ·
                    refine ⟨11164488004633657920806885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29771968012356421122151693 11164488004633657920806885)
                    ·
                      refine ⟨2093341500868810860151291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11164488004633657920806885 2093341500868810860151291)
                      ·
                        rfl

theorem cell23_4076768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_4076768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076768 prefixEnd_4076768 := by exact prefixLift 4076768
  have htrace : WordTrace (prefixWord ++ tailWord_4076768) baseStart_4076768 baseEnd_4076768 := by
    simpa [prefixWord, tailWord_4076768, baseEnd_4076768] using wordTrace_append hprefix tailTrace_4076768
  have hstable : (prefixWord ++ tailWord_4076768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076768).length < 2 ^ (prefixWord ++ tailWord_4076768).sum := by decide
  have hdescent : baseEnd_4076768 < baseStart_4076768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076778 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 1, 8]
def baseStart_4076778 : Nat := 118140960795 + 4076778 * 2 ^ 59
def prefixEnd_4076778 : Nat := 4983230072969 + 3 ^ 40 * 4076778 * 2
def baseEnd_4076778 : Nat := 697782211891785273675415

theorem tailTrace_4076778 : CollatzResearch.WordTrace tailWord_4076778 prefixEnd_4076778 697782211891785273675415 := by
  unfold tailWord_4076778
  simp only [CollatzResearch.WordTrace]
  refine ⟨37173077306134259773889747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99128206149691359397039325 37173077306134259773889747)
  ·
    refine ⟨55759615959201389660834621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37173077306134259773889747 55759615959201389660834621)
    ·
      refine ⟨20909855984700521122812983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55759615959201389660834621 20909855984700521122812983)
      ·
        refine ⟨31364783977050781684219475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20909855984700521122812983 31364783977050781684219475)
        ·
          refine ⟨47047175965576172526329213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31364783977050781684219475 47047175965576172526329213)
          ·
            refine ⟨17642690987091064697373455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47047175965576172526329213 17642690987091064697373455)
            ·
              refine ⟨26464036480636597046060183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17642690987091064697373455 26464036480636597046060183)
              ·
                refine ⟨39696054720954895569090275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26464036480636597046060183 39696054720954895569090275)
                ·
                  refine ⟨59544082081432343353635413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39696054720954895569090275 59544082081432343353635413)
                  ·
                    refine ⟨697782211891785273675415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59544082081432343353635413 697782211891785273675415)
                    ·
                      rfl

theorem cell23_4076778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_4076778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076778 prefixEnd_4076778 := by exact prefixLift 4076778
  have htrace : WordTrace (prefixWord ++ tailWord_4076778) baseStart_4076778 baseEnd_4076778 := by
    simpa [prefixWord, tailWord_4076778, baseEnd_4076778] using wordTrace_append hprefix tailTrace_4076778
  have hstable : (prefixWord ++ tailWord_4076778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076778).length < 2 ^ (prefixWord ++ tailWord_4076778).sum := by decide
  have hdescent : baseEnd_4076778 < baseStart_4076778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076835 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 3]
def baseStart_4076835 : Nat := 118140960795 + 4076835 * 2 ^ 59
def prefixEnd_4076835 : Nat := 4983230072969 + 3 ^ 40 * 4076835 * 2
def baseEnd_4076835 : Nat := 2093375904072662098013483

theorem tailTrace_4076835 : CollatzResearch.WordTrace tailWord_4076835 prefixEnd_4076835 2093375904072662098013483 := by
  unfold tailWord_4076835
  simp only [CollatzResearch.WordTrace]
  refine ⟨148694388185330537830383959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99129592123553691886922639 148694388185330537830383959)
  ·
    refine ⟨223041582277995806745575939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148694388185330537830383959 223041582277995806745575939)
    ·
      refine ⟨334562373416993710118363909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223041582277995806745575939 334562373416993710118363909)
      ·
        refine ⟨62730445015686320647193233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334562373416993710118363909 62730445015686320647193233)
        ·
          refine ⟨47047833761764740485394925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62730445015686320647193233 47047833761764740485394925)
          ·
            refine ⟨17642937660661777682023097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47047833761764740485394925 17642937660661777682023097)
            ·
              refine ⟨13232203245496333261517323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17642937660661777682023097 13232203245496333261517323)
              ·
                refine ⟨19848304868244499892275985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13232203245496333261517323 19848304868244499892275985)
                ·
                  refine ⟨14886228651183374919206989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19848304868244499892275985 14886228651183374919206989)
                  ·
                    refine ⟨5582335744193765594702621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14886228651183374919206989 5582335744193765594702621)
                    ·
                      refine ⟨2093375904072662098013483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582335744193765594702621 2093375904072662098013483)
                      ·
                        rfl

theorem cell23_4076835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_4076835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076835 prefixEnd_4076835 := by exact prefixLift 4076835
  have htrace : WordTrace (prefixWord ++ tailWord_4076835) baseStart_4076835 baseEnd_4076835 := by
    simpa [prefixWord, tailWord_4076835, baseEnd_4076835] using wordTrace_append hprefix tailTrace_4076835
  have hstable : (prefixWord ++ tailWord_4076835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076835).length < 2 ^ (prefixWord ++ tailWord_4076835).sum := by decide
  have hdescent : baseEnd_4076835 < baseStart_4076835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076836 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 2, 2, 2]
def baseStart_4076836 : Nat := 118140960795 + 4076836 * 2 ^ 59
def prefixEnd_4076836 : Nat := 4983230072969 + 3 ^ 40 * 4076836 * 2
def baseEnd_4076836 : Nat := 2093376417553316594100979

theorem tailTrace_4076836 : CollatzResearch.WordTrace tailWord_4076836 prefixEnd_4076836 2093376417553316594100979 := by
  unfold tailWord_4076836
  simp only [CollatzResearch.WordTrace]
  refine ⟨74347212329163457500585181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99129616438884610000780241 74347212329163457500585181)
  ·
    refine ⟨27880204623436296562719443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74347212329163457500585181 27880204623436296562719443)
    ·
      refine ⟨41820306935154444844079165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27880204623436296562719443 41820306935154444844079165)
      ·
        refine ⟨15682615100682916816529687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41820306935154444844079165 15682615100682916816529687)
        ·
          refine ⟨23523922651024375224794531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15682615100682916816529687 23523922651024375224794531)
          ·
            refine ⟨35285883976536562837191797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23523922651024375224794531 35285883976536562837191797)
            ·
              refine ⟨3308051622800302765986731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35285883976536562837191797 3308051622800302765986731)
              ·
                refine ⟨4962077434200454148980097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308051622800302765986731 4962077434200454148980097)
                ·
                  refine ⟨3721558075650340611735073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962077434200454148980097 3721558075650340611735073)
                  ·
                    refine ⟨2791168556737755458801305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3721558075650340611735073 2791168556737755458801305)
                    ·
                      refine ⟨2093376417553316594100979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791168556737755458801305 2093376417553316594100979)
                      ·
                        rfl

theorem cell23_4076836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_4076836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076836 prefixEnd_4076836 := by exact prefixLift 4076836
  have htrace : WordTrace (prefixWord ++ tailWord_4076836) baseStart_4076836 baseEnd_4076836 := by
    simpa [prefixWord, tailWord_4076836, baseEnd_4076836] using wordTrace_append hprefix tailTrace_4076836
  have hstable : (prefixWord ++ tailWord_4076836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076836).length < 2 ^ (prefixWord ++ tailWord_4076836).sum := by decide
  have hdescent : baseEnd_4076836 < baseStart_4076836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076895 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 3]
def baseStart_4076895 : Nat := 118140960795 + 4076895 * 2 ^ 59
def prefixEnd_4076895 : Nat := 4983230072969 + 3 ^ 40 * 4076895 * 2
def baseEnd_4076895 : Nat := 2093406712911931863263207

theorem tailTrace_4076895 : CollatzResearch.WordTrace tailWord_4076895 prefixEnd_4076895 2093406712911931863263207 := by
  unfold tailWord_4076895
  simp only [CollatzResearch.WordTrace]
  refine ⟨148696576565113168077568139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99131051043408778718378759 148696576565113168077568139)
  ·
    refine ⟨223044864847669752116352209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148696576565113168077568139 223044864847669752116352209)
    ·
      refine ⟨167283648635752314087264157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223044864847669752116352209 167283648635752314087264157)
      ·
        refine ⟨62731368238407117782724059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167283648635752314087264157 62731368238407117782724059)
        ·
          refine ⟨94097052357610676674086089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62731368238407117782724059 94097052357610676674086089)
          ·
            refine ⟨70572789268208007505564567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94097052357610676674086089 70572789268208007505564567)
            ·
              refine ⟨105859183902312011258346851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70572789268208007505564567 105859183902312011258346851)
              ·
                refine ⟨158788775853468016887520277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105859183902312011258346851 158788775853468016887520277)
                ·
                  refine ⟨7443223868131313291602513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 158788775853468016887520277 7443223868131313291602513)
                  ·
                    refine ⟨5582417901098484968701885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7443223868131313291602513 5582417901098484968701885)
                    ·
                      refine ⟨2093406712911931863263207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582417901098484968701885 2093406712911931863263207)
                      ·
                        rfl

theorem cell23_4076895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_4076895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076895 prefixEnd_4076895 := by exact prefixLift 4076895
  have htrace : WordTrace (prefixWord ++ tailWord_4076895) baseStart_4076895 baseEnd_4076895 := by
    simpa [prefixWord, tailWord_4076895, baseEnd_4076895] using wordTrace_append hprefix tailTrace_4076895
  have hstable : (prefixWord ++ tailWord_4076895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076895).length < 2 ^ (prefixWord ++ tailWord_4076895).sum := by decide
  have hdescent : baseEnd_4076895 < baseStart_4076895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076912 : List Nat := [2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_4076912 : Nat := 118140960795 + 4076912 * 2 ^ 59
def prefixEnd_4076912 : Nat := 4983230072969 + 3 ^ 40 * 4076912 * 2
def baseEnd_4076912 : Nat := 2093415442083058296750629

theorem tailTrace_4076912 : CollatzResearch.WordTrace tailWord_4076912 prefixEnd_4076912 2093415442083058296750629 := by
  unfold tailWord_4076912
  simp only [CollatzResearch.WordTrace]
  refine ⟨74348598303025789990468495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99131464404034386653957993 74348598303025789990468495)
  ·
    refine ⟨111522897454538684985702743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74348598303025789990468495 111522897454538684985702743)
    ·
      refine ⟨167284346181808027478554115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111522897454538684985702743 167284346181808027478554115)
      ·
        refine ⟨250926519272712041217831173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167284346181808027478554115 250926519272712041217831173)
        ·
          refine ⟨47048722363633507728343345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250926519272712041217831173 47048722363633507728343345)
          ·
            refine ⟨35286541772725130796257509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47048722363633507728343345 35286541772725130796257509)
            ·
              refine ⟨6616226582385962024298283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35286541772725130796257509 6616226582385962024298283)
              ·
                refine ⟨9924339873578943036447425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6616226582385962024298283 9924339873578943036447425)
                ·
                  refine ⟨7443254905184207277335569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9924339873578943036447425 7443254905184207277335569)
                  ·
                    refine ⟨5582441178888155458001677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7443254905184207277335569 5582441178888155458001677)
                    ·
                      refine ⟨2093415442083058296750629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582441178888155458001677 2093415442083058296750629)
                      ·
                        rfl

theorem cell23_4076912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_4076912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076912 prefixEnd_4076912 := by exact prefixLift 4076912
  have htrace : WordTrace (prefixWord ++ tailWord_4076912) baseStart_4076912 baseEnd_4076912 := by
    simpa [prefixWord, tailWord_4076912, baseEnd_4076912] using wordTrace_append hprefix tailTrace_4076912
  have hstable : (prefixWord ++ tailWord_4076912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076912).length < 2 ^ (prefixWord ++ tailWord_4076912).sum := by decide
  have hdescent : baseEnd_4076912 < baseStart_4076912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076932 : List Nat := [2, 3, 2, 1, 1, 4, 2, 2, 6]
def baseStart_4076932 : Nat := 118140960795 + 4076932 * 2 ^ 59
def prefixEnd_4076932 : Nat := 4983230072969 + 3 ^ 40 * 4076932 * 2
def baseEnd_4076932 : Nat := 232602856855127579833393

theorem tailTrace_4076932 : CollatzResearch.WordTrace tailWord_4076932 prefixEnd_4076932 232602856855127579833393 := by
  unfold tailWord_4076932
  simp only [CollatzResearch.WordTrace]
  refine ⟨74348963032989561698332525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99131950710652748931110033 74348963032989561698332525)
  ·
    refine ⟨27880861137371085636874697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74348963032989561698332525 27880861137371085636874697)
    ·
      refine ⟨20910645853028314227656023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27880861137371085636874697 20910645853028314227656023)
      ·
        refine ⟨31365968779542471341484035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20910645853028314227656023 31365968779542471341484035)
        ·
          refine ⟨47048953169313707012226053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31365968779542471341484035 47048953169313707012226053)
          ·
            refine ⟨8821678719246320064792385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47048953169313707012226053 8821678719246320064792385)
            ·
              refine ⟨6616259039434740048594289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8821678719246320064792385 6616259039434740048594289)
              ·
                refine ⟨4962194279576055036445717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616259039434740048594289 4962194279576055036445717)
                ·
                  refine ⟨232602856855127579833393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4962194279576055036445717 232602856855127579833393)
                  ·
                    rfl

theorem cell23_4076932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_4076932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076932 prefixEnd_4076932 := by exact prefixLift 4076932
  have htrace : WordTrace (prefixWord ++ tailWord_4076932) baseStart_4076932 baseEnd_4076932 := by
    simpa [prefixWord, tailWord_4076932, baseEnd_4076932] using wordTrace_append hprefix tailTrace_4076932
  have hstable : (prefixWord ++ tailWord_4076932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076932).length < 2 ^ (prefixWord ++ tailWord_4076932).sum := by decide
  have hdescent : baseEnd_4076932 < baseStart_4076932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076936 : List Nat := [2, 1, 3, 3, 1, 2, 4, 2, 1, 4]
def baseStart_4076936 : Nat := 118140960795 + 4076936 * 2 ^ 59
def prefixEnd_4076936 : Nat := 4983230072969 + 3 ^ 40 * 4076936 * 2
def baseEnd_4076936 : Nat := 697809255206255400950173

theorem tailTrace_4076936 : CollatzResearch.WordTrace tailWord_4076936 prefixEnd_4076936 697809255206255400950173 := by
  unfold tailWord_4076936
  simp only [CollatzResearch.WordTrace]
  refine ⟨74349035978982316039905331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99132047971976421386540441 74349035978982316039905331)
  ·
    refine ⟨111523553968473474059857997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74349035978982316039905331 111523553968473474059857997)
    ·
      refine ⟨41821332738177552772446749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111523553968473474059857997 41821332738177552772446749)
      ·
        refine ⟨15682999776816582289667531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41821332738177552772446749 15682999776816582289667531)
        ·
          refine ⟨23524499665224873434501297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15682999776816582289667531 23524499665224873434501297)
          ·
            refine ⟨17643374748918655075875973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23524499665224873434501297 17643374748918655075875973)
            ·
              refine ⟨3308132765422247826726745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17643374748918655075875973 3308132765422247826726745)
              ·
                refine ⟨2481099574066685870045059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308132765422247826726745 2481099574066685870045059)
                ·
                  refine ⟨3721649361100028805067589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481099574066685870045059 3721649361100028805067589)
                  ·
                    refine ⟨697809255206255400950173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721649361100028805067589 697809255206255400950173)
                    ·
                      rfl

theorem cell23_4076936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 4, 2, 1, 4].length) (baseStart_4076936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076936 prefixEnd_4076936 := by exact prefixLift 4076936
  have htrace : WordTrace (prefixWord ++ tailWord_4076936) baseStart_4076936 baseEnd_4076936 := by
    simpa [prefixWord, tailWord_4076936, baseEnd_4076936] using wordTrace_append hprefix tailTrace_4076936
  have hstable : (prefixWord ++ tailWord_4076936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076936).length < 2 ^ (prefixWord ++ tailWord_4076936).sum := by decide
  have hdescent : baseEnd_4076936 < baseStart_4076936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076959 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4076959 : Nat := 118140960795 + 4076959 * 2 ^ 59
def prefixEnd_4076959 : Nat := 4983230072969 + 3 ^ 40 * 4076959 * 2
def baseEnd_4076959 : Nat := 2093439575673819612862913

theorem tailTrace_4076959 : CollatzResearch.WordTrace tailWord_4076959 prefixEnd_4076959 2093439575673819612862913 := by
  unfold tailWord_4076959
  simp only [CollatzResearch.WordTrace]
  refine ⟨148698910836881307007897931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99132607224587538005265287 148698910836881307007897931)
  ·
    refine ⟨223048366255321960511846897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148698910836881307007897931 223048366255321960511846897)
    ·
      refine ⟨167286274691491470383885173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223048366255321960511846897 167286274691491470383885173)
      ·
        refine ⟨15683088252327325348489235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167286274691491470383885173 15683088252327325348489235)
        ·
          refine ⟨23524632378490988022733853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15683088252327325348489235 23524632378490988022733853)
          ·
            refine ⟨8821737141934120508525195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23524632378490988022733853 8821737141934120508525195)
            ·
              refine ⟨13232605712901180762787793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8821737141934120508525195 13232605712901180762787793)
              ·
                refine ⟨9924454284675885572090845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13232605712901180762787793 9924454284675885572090845)
                ·
                  refine ⟨3721670356753457089534067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9924454284675885572090845 3721670356753457089534067)
                  ·
                    refine ⟨5582505535130185634301101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721670356753457089534067 5582505535130185634301101)
                    ·
                      refine ⟨2093439575673819612862913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582505535130185634301101 2093439575673819612862913)
                      ·
                        rfl

theorem cell23_4076959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4076959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076959 prefixEnd_4076959 := by exact prefixLift 4076959
  have htrace : WordTrace (prefixWord ++ tailWord_4076959) baseStart_4076959 baseEnd_4076959 := by
    simpa [prefixWord, tailWord_4076959, baseEnd_4076959] using wordTrace_append hprefix tailTrace_4076959
  have hstable : (prefixWord ++ tailWord_4076959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076959).length < 2 ^ (prefixWord ++ tailWord_4076959).sum := by decide
  have hdescent : baseEnd_4076959 < baseStart_4076959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076962 : List Nat := [3, 3, 1, 2, 1, 2, 2, 1, 3, 5]
def baseStart_4076962 : Nat := 118140960795 + 4076962 * 2 ^ 59
def prefixEnd_4076962 : Nat := 4983230072969 + 3 ^ 40 * 4076962 * 2
def baseEnd_4076962 : Nat := 697813705371927700375133

theorem tailTrace_4076962 : CollatzResearch.WordTrace tailWord_4076962 prefixEnd_4076962 697813705371927700375133 := by
  unfold tailWord_4076962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37174755063967609630064285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99132680170580292346838093 37174755063967609630064285)
  ·
    refine ⟨13940533148987853611274107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37174755063967609630064285 13940533148987853611274107)
    ·
      refine ⟨20910799723481780416911161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13940533148987853611274107 20910799723481780416911161)
      ·
        refine ⟨15683099792611335312683371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20910799723481780416911161 15683099792611335312683371)
        ·
          refine ⟨23524649688917002969025057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15683099792611335312683371 23524649688917002969025057)
          ·
            refine ⟨17643487266687752226768793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23524649688917002969025057 17643487266687752226768793)
            ·
              refine ⟨13232615450015814170076595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17643487266687752226768793 13232615450015814170076595)
              ·
                refine ⟨19848923175023721255114893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13232615450015814170076595 19848923175023721255114893)
                ·
                  refine ⟨7443346190633895470668085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19848923175023721255114893 7443346190633895470668085)
                  ·
                    refine ⟨697813705371927700375133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7443346190633895470668085 697813705371927700375133)
                    ·
                      rfl

theorem cell23_4076962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_4076962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076962 prefixEnd_4076962 := by exact prefixLift 4076962
  have htrace : WordTrace (prefixWord ++ tailWord_4076962) baseStart_4076962 baseEnd_4076962 := by
    simpa [prefixWord, tailWord_4076962, baseEnd_4076962] using wordTrace_append hprefix tailTrace_4076962
  have hstable : (prefixWord ++ tailWord_4076962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076962).length < 2 ^ (prefixWord ++ tailWord_4076962).sum := by decide
  have hdescent : baseEnd_4076962 < baseStart_4076962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4076995 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4]
def baseStart_4076995 : Nat := 118140960795 + 4076995 * 2 ^ 59
def prefixEnd_4076995 : Nat := 4983230072969 + 3 ^ 40 * 4076995 * 2
def baseEnd_4076995 : Nat := 2093458060977381472012747

theorem tailTrace_4076995 : CollatzResearch.WordTrace tailWord_4076995 prefixEnd_4076995 2093458060977381472012747 := by
  unfold tailWord_4076995
  simp only [CollatzResearch.WordTrace]
  refine ⟨148700223864750885156208439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99133482576500590104138959 148700223864750885156208439)
  ·
    refine ⟨223050335797126327734312659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148700223864750885156208439 223050335797126327734312659)
    ·
      refine ⟨334575503695689491601468989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223050335797126327734312659 334575503695689491601468989)
      ·
        refine ⟨125465813885883559350550871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334575503695689491601468989 125465813885883559350550871)
        ·
          refine ⟨188198720828825339025826307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125465813885883559350550871 188198720828825339025826307)
          ·
            refine ⟨282298081243238008538739461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188198720828825339025826307 282298081243238008538739461)
            ·
              refine ⟨52930890233107126601013649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 282298081243238008538739461 52930890233107126601013649)
              ·
                refine ⟨39698167674830344950760237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52930890233107126601013649 39698167674830344950760237)
                ·
                  refine ⟨14886812878061379356535089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39698167674830344950760237 14886812878061379356535089)
                  ·
                    refine ⟨11165109658546034517401317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14886812878061379356535089 11165109658546034517401317)
                    ·
                      refine ⟨2093458060977381472012747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11165109658546034517401317 2093458060977381472012747)
                      ·
                        rfl

theorem cell23_4076995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_4076995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4076995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4076995 prefixEnd_4076995 := by exact prefixLift 4076995
  have htrace : WordTrace (prefixWord ++ tailWord_4076995) baseStart_4076995 baseEnd_4076995 := by
    simpa [prefixWord, tailWord_4076995, baseEnd_4076995] using wordTrace_append hprefix tailTrace_4076995
  have hstable : (prefixWord ++ tailWord_4076995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4076995).length < 2 ^ (prefixWord ++ tailWord_4076995).sum := by decide
  have hdescent : baseEnd_4076995 < baseStart_4076995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4076995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077002 : List Nat := [3, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5]
def baseStart_4077002 : Nat := 118140960795 + 4077002 * 2 ^ 59
def prefixEnd_4077002 : Nat := 4983230072969 + 3 ^ 40 * 4077002 * 2
def baseEnd_4077002 : Nat := 2093461655341962944625215

theorem tailTrace_4077002 : CollatzResearch.WordTrace tailWord_4077002 prefixEnd_4077002 2093461655341962944625215 := by
  unfold tailWord_4077002
  simp only [CollatzResearch.WordTrace]
  refine ⟨37175119793931381337928315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99133652783817016901142173 37175119793931381337928315)
  ·
    refine ⟨55762679690897072006892473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37175119793931381337928315 55762679690897072006892473)
    ·
      refine ⟨41822009768172804005169355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55762679690897072006892473 41822009768172804005169355)
      ·
        refine ⟨62733014652259206007754033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41822009768172804005169355 62733014652259206007754033)
        ·
          refine ⟨47049760989194404505815525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62733014652259206007754033 47049760989194404505815525)
          ·
            refine ⟨8821830185473950844840411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47049760989194404505815525 8821830185473950844840411)
            ·
              refine ⟨13232745278210926267260617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8821830185473950844840411 13232745278210926267260617)
              ·
                refine ⟨9924558958658194700445463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13232745278210926267260617 9924558958658194700445463)
                ·
                  refine ⟨14886838437987292050668195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9924558958658194700445463 14886838437987292050668195)
                  ·
                    refine ⟨22330257656980938076002293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14886838437987292050668195 22330257656980938076002293)
                    ·
                      refine ⟨2093461655341962944625215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22330257656980938076002293 2093461655341962944625215)
                      ·
                        rfl

theorem cell23_4077002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5].length) (baseStart_4077002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077002 prefixEnd_4077002 := by exact prefixLift 4077002
  have htrace : WordTrace (prefixWord ++ tailWord_4077002) baseStart_4077002 baseEnd_4077002 := by
    simpa [prefixWord, tailWord_4077002, baseEnd_4077002] using wordTrace_append hprefix tailTrace_4077002
  have hstable : (prefixWord ++ tailWord_4077002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077002).length < 2 ^ (prefixWord ++ tailWord_4077002).sum := by decide
  have hdescent : baseEnd_4077002 < baseStart_4077002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077032 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_4077032 : Nat := 118140960795 + 4077032 * 2 ^ 59
def prefixEnd_4077032 : Nat := 4983230072969 + 3 ^ 40 * 4077032 * 2
def baseEnd_4077032 : Nat := 2093477059761597827250077

theorem tailTrace_4077032 : CollatzResearch.WordTrace tailWord_4077032 prefixEnd_4077032 2093477059761597827250077 := by
  unfold tailWord_4077032
  simp only [CollatzResearch.WordTrace]
  refine ⟨74350786682808420237652675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99134382243744560316870233 74350786682808420237652675)
  ·
    refine ⟨111526180024212630356479013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74350786682808420237652675 111526180024212630356479013)
    ·
      refine ⟨20911158754539868191839815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111526180024212630356479013 20911158754539868191839815)
      ·
        refine ⟨31366738131809802287759723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20911158754539868191839815 31366738131809802287759723)
        ·
          refine ⟨47050107197714703431639585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31366738131809802287759723 47050107197714703431639585)
          ·
            refine ⟨35287580398286027573729689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47050107197714703431639585 35287580398286027573729689)
            ·
              refine ⟨26465685298714520680297267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35287580398286027573729689 26465685298714520680297267)
              ·
                refine ⟨39698527948071781020445901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26465685298714520680297267 39698527948071781020445901)
                ·
                  refine ⟨14886947980526917882667213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39698527948071781020445901 14886947980526917882667213)
                  ·
                    refine ⟨5582605492697594206000205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14886947980526917882667213 5582605492697594206000205)
                    ·
                      refine ⟨2093477059761597827250077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582605492697594206000205 2093477059761597827250077)
                      ·
                        rfl

theorem cell23_4077032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_4077032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077032 prefixEnd_4077032 := by exact prefixLift 4077032
  have htrace : WordTrace (prefixWord ++ tailWord_4077032) baseStart_4077032 baseEnd_4077032 := by
    simpa [prefixWord, tailWord_4077032, baseEnd_4077032] using wordTrace_append hprefix tailTrace_4077032
  have hstable : (prefixWord ++ tailWord_4077032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077032).length < 2 ^ (prefixWord ++ tailWord_4077032).sum := by decide
  have hdescent : baseEnd_4077032 < baseStart_4077032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077049 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 3]
def baseStart_4077049 : Nat := 118140960795 + 4077049 * 2 ^ 59
def prefixEnd_4077049 : Nat := 4983230072969 + 3 ^ 40 * 4077049 * 2
def baseEnd_4077049 : Nat := 2093485788932724260737499

theorem tailTrace_4077049 : CollatzResearch.WordTrace tailWord_4077049 prefixEnd_4077049 2093485788932724260737499 := by
  unfold tailWord_4077049
  simp only [CollatzResearch.WordTrace]
  refine ⟨148702193406555252378674201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99134795604370168252449467 148702193406555252378674201)
  ·
    refine ⟨111526645054916439284005651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148702193406555252378674201 111526645054916439284005651)
    ·
      refine ⟨167289967582374658926008477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111526645054916439284005651 167289967582374658926008477)
      ·
        refine ⟨62733737843390497097253179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167289967582374658926008477 62733737843390497097253179)
        ·
          refine ⟨94100606765085745645879769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62733737843390497097253179 94100606765085745645879769)
          ·
            refine ⟨70575455073814309234409827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94100606765085745645879769 70575455073814309234409827)
            ·
              refine ⟨105863182610721463851614741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70575455073814309234409827 105863182610721463851614741)
              ·
                refine ⟨4962336684877568618044441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105863182610721463851614741 4962336684877568618044441)
                ·
                  refine ⟨3721752513658176463533331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962336684877568618044441 3721752513658176463533331)
                  ·
                    refine ⟨5582628770487264695299997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721752513658176463533331 5582628770487264695299997)
                    ·
                      refine ⟨2093485788932724260737499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582628770487264695299997 2093485788932724260737499)
                      ·
                        rfl

theorem cell23_4077049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 2, 1, 3].length) (baseStart_4077049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077049 prefixEnd_4077049 := by exact prefixLift 4077049
  have htrace : WordTrace (prefixWord ++ tailWord_4077049) baseStart_4077049 baseEnd_4077049 := by
    simpa [prefixWord, tailWord_4077049, baseEnd_4077049] using wordTrace_append hprefix tailTrace_4077049
  have hstable : (prefixWord ++ tailWord_4077049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077049).length < 2 ^ (prefixWord ++ tailWord_4077049).sum := by decide
  have hdescent : baseEnd_4077049 < baseStart_4077049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077060 : List Nat := [2, 3, 2, 3, 3, 1, 2, 1, 2, 4]
def baseStart_4077060 : Nat := 118140960795 + 4077060 * 2 ^ 59
def prefixEnd_4077060 : Nat := 4983230072969 + 3 ^ 40 * 4077060 * 2
def baseEnd_4077060 : Nat := 697830479073307905899983

theorem tailTrace_4077060 : CollatzResearch.WordTrace tailWord_4077060 prefixEnd_4077060 697830479073307905899983 := by
  unfold tailWord_4077060
  simp only [CollatzResearch.WordTrace]
  refine ⟨74351297304757700628662317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99135063073010267504883089 74351297304757700628662317)
  ·
    refine ⟨27881736489284137735748369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74351297304757700628662317 27881736489284137735748369)
    ·
      refine ⟨20911302366963103301811277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27881736489284137735748369 20911302366963103301811277)
      ·
        refine ⟨7841738387611163738179229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20911302366963103301811277 7841738387611163738179229)
        ·
          refine ⟨2940651895354186401817211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7841738387611163738179229 2940651895354186401817211)
          ·
            refine ⟨4410977843031279602725817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2940651895354186401817211 4410977843031279602725817)
            ·
              refine ⟨3308233382273459702044363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4410977843031279602725817 3308233382273459702044363)
              ·
                refine ⟨4962350073410189553066545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308233382273459702044363 4962350073410189553066545)
                ·
                  refine ⟨3721762555057642164799909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962350073410189553066545 3721762555057642164799909)
                  ·
                    refine ⟨697830479073307905899983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721762555057642164799909 697830479073307905899983)
                    ·
                      rfl

theorem cell23_4077060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_4077060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077060 prefixEnd_4077060 := by exact prefixLift 4077060
  have htrace : WordTrace (prefixWord ++ tailWord_4077060) baseStart_4077060 baseEnd_4077060 := by
    simpa [prefixWord, tailWord_4077060, baseEnd_4077060] using wordTrace_append hprefix tailTrace_4077060
  have hstable : (prefixWord ++ tailWord_4077060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077060).length < 2 ^ (prefixWord ++ tailWord_4077060).sum := by decide
  have hdescent : baseEnd_4077060 < baseStart_4077060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077065 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 1, 8]
def baseStart_4077065 : Nat := 118140960795 + 4077065 * 2 ^ 59
def prefixEnd_4077065 : Nat := 4983230072969 + 3 ^ 40 * 4077065 * 2
def baseEnd_4077065 : Nat := 697831334874398732712475

theorem tailTrace_4077065 : CollatzResearch.WordTrace tailWord_4077065 prefixEnd_4077065 697831334874398732712475 := by
  unfold tailWord_4077065
  simp only [CollatzResearch.WordTrace]
  refine ⟨148702776974497287111256649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99135184649664858074171099 148702776974497287111256649)
  ·
    refine ⟨111527082730872965333442487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148702776974497287111256649 111527082730872965333442487)
    ·
      refine ⟨167290624096309448000163731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111527082730872965333442487 167290624096309448000163731)
      ·
        refine ⟨250935936144464172000245597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167290624096309448000163731 250935936144464172000245597)
        ·
          refine ⟨94100976054174064500092099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 250935936144464172000245597 94100976054174064500092099)
          ·
            refine ⟨141151464081261096750138149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94100976054174064500092099 141151464081261096750138149)
            ·
              refine ⟨26465899515236455640650903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 141151464081261096750138149 26465899515236455640650903)
              ·
                refine ⟨39698849272854683460976355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26465899515236455640650903 39698849272854683460976355)
                ·
                  refine ⟨59548273909282025191464533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39698849272854683460976355 59548273909282025191464533)
                  ·
                    refine ⟨697831334874398732712475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59548273909282025191464533 697831334874398732712475)
                    ·
                      rfl

theorem cell23_4077065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_4077065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077065 prefixEnd_4077065 := by exact prefixLift 4077065
  have htrace : WordTrace (prefixWord ++ tailWord_4077065) baseStart_4077065 baseEnd_4077065 := by
    simpa [prefixWord, tailWord_4077065, baseEnd_4077065] using wordTrace_append hprefix tailTrace_4077065
  have hstable : (prefixWord ++ tailWord_4077065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077065).length < 2 ^ (prefixWord ++ tailWord_4077065).sum := by decide
  have hdescent : baseEnd_4077065 < baseStart_4077065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077066 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3]
def baseStart_4077066 : Nat := 118140960795 + 4077066 * 2 ^ 59
def prefixEnd_4077066 : Nat := 4983230072969 + 3 ^ 40 * 4077066 * 2
def baseEnd_4077066 : Nat := 2093494518103850694224921

theorem tailTrace_4077066 : CollatzResearch.WordTrace tailWord_4077066 prefixEnd_4077066 2093494518103850694224921 := by
  unfold tailWord_4077066
  simp only [CollatzResearch.WordTrace]
  refine ⟨37175703361873416070510763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99135208964995776188028701 37175703361873416070510763)
  ·
    refine ⟨55763555042810124105766145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37175703361873416070510763 55763555042810124105766145)
    ·
      refine ⟨41822666282107593079324609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55763555042810124105766145 41822666282107593079324609)
      ·
        refine ⟨31366999711580694809493457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41822666282107593079324609 31366999711580694809493457)
        ·
          refine ⟨23525249783685521107120093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31366999711580694809493457 23525249783685521107120093)
          ·
            refine ⟨8821968668882070415170035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23525249783685521107120093 8821968668882070415170035)
            ·
              refine ⟨13232953003323105622755053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8821968668882070415170035 13232953003323105622755053)
              ·
                refine ⟨4962357376246164608533145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13232953003323105622755053 4962357376246164608533145)
                ·
                  refine ⟨3721768032184623456399859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962357376246164608533145 3721768032184623456399859)
                  ·
                    refine ⟨5582652048276935184599789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721768032184623456399859 5582652048276935184599789)
                    ·
                      refine ⟨2093494518103850694224921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582652048276935184599789 2093494518103850694224921)
                      ·
                        rfl

theorem cell23_4077066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_4077066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077066 prefixEnd_4077066 := by exact prefixLift 4077066
  have htrace : WordTrace (prefixWord ++ tailWord_4077066) baseStart_4077066 baseEnd_4077066 := by
    simpa [prefixWord, tailWord_4077066, baseEnd_4077066] using wordTrace_append hprefix tailTrace_4077066
  have hstable : (prefixWord ++ tailWord_4077066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077066).length < 2 ^ (prefixWord ++ tailWord_4077066).sum := by decide
  have hdescent : baseEnd_4077066 < baseStart_4077066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077072 : List Nat := [2, 1, 1, 1, 1, 1, 1, 2, 1, 10, 2]
def baseStart_4077072 : Nat := 118140960795 + 4077072 * 2 ^ 59
def prefixEnd_4077072 : Nat := 4983230072969 + 3 ^ 40 * 4077072 * 2
def baseEnd_4077072 : Nat := 2093497598987777670749893

theorem tailTrace_4077072 : CollatzResearch.WordTrace tailWord_4077072 prefixEnd_4077072 2093497598987777670749893 := by
  unfold tailWord_4077072
  simp only [CollatzResearch.WordTrace]
  refine ⟨74351516142735963653380735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99135354856981284871174313 74351516142735963653380735)
  ·
    refine ⟨111527274214103945480071103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74351516142735963653380735 111527274214103945480071103)
    ·
      refine ⟨167290911321155918220106655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111527274214103945480071103 167290911321155918220106655)
      ·
        refine ⟨250936366981733877330159983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167290911321155918220106655 250936366981733877330159983)
        ·
          refine ⟨376404550472600815995239975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250936366981733877330159983 376404550472600815995239975)
          ·
            refine ⟨564606825708901223992859963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376404550472600815995239975 564606825708901223992859963)
            ·
              refine ⟨846910238563351835989289945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564606825708901223992859963 846910238563351835989289945)
              ·
                refine ⟨635182678922513876991967459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846910238563351835989289945 635182678922513876991967459)
                ·
                  refine ⟨952774018383770815487951189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635182678922513876991967459 952774018383770815487951189)
                  ·
                    refine ⟨2791330131983703560999857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 952774018383770815487951189 2791330131983703560999857)
                    ·
                      refine ⟨2093497598987777670749893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791330131983703560999857 2093497598987777670749893)
                      ·
                        rfl

theorem cell23_4077072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 10, 2].length) (baseStart_4077072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077072 prefixEnd_4077072 := by exact prefixLift 4077072
  have htrace : WordTrace (prefixWord ++ tailWord_4077072) baseStart_4077072 baseEnd_4077072 := by
    simpa [prefixWord, tailWord_4077072, baseEnd_4077072] using wordTrace_append hprefix tailTrace_4077072
  have hstable : (prefixWord ++ tailWord_4077072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077072).length < 2 ^ (prefixWord ++ tailWord_4077072).sum := by decide
  have hdescent : baseEnd_4077072 < baseStart_4077072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077089 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 3, 4, 2]
def baseStart_4077089 : Nat := 118140960795 + 4077089 * 2 ^ 59
def prefixEnd_4077089 : Nat := 4983230072969 + 3 ^ 40 * 4077089 * 2
def baseEnd_4077089 : Nat := 2093506328158904104237315

theorem tailTrace_4077089 : CollatzResearch.WordTrace tailWord_4077089 prefixEnd_4077089 2093506328158904104237315 := by
  unfold tailWord_4077089
  simp only [CollatzResearch.WordTrace]
  refine ⟨148703652326410339210130321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99135768217606892806753547 148703652326410339210130321)
  ·
    refine ⟨111527739244807754407597741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148703652326410339210130321 111527739244807754407597741)
    ·
      refine ⟨41822902216802907902849153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111527739244807754407597741 41822902216802907902849153)
      ·
        refine ⟨31367176662602180927136865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41822902216802907902849153 31367176662602180927136865)
        ·
          refine ⟨23525382496951635695352649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31367176662602180927136865 23525382496951635695352649)
          ·
            refine ⟨17644036872713726771514487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23525382496951635695352649 17644036872713726771514487)
            ·
              refine ⟨26466055309070590157271731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17644036872713726771514487 26466055309070590157271731)
              ·
                refine ⟨39699082963605885235907597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26466055309070590157271731 39699082963605885235907597)
                ·
                  refine ⟨14887156111352206963465349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39699082963605885235907597 14887156111352206963465349)
                  ·
                    refine ⟨2791341770878538805649753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14887156111352206963465349 2791341770878538805649753)
                    ·
                      refine ⟨2093506328158904104237315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791341770878538805649753 2093506328158904104237315)
                      ·
                        rfl

theorem cell23_4077089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 4, 2].length) (baseStart_4077089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077089 prefixEnd_4077089 := by exact prefixLift 4077089
  have htrace : WordTrace (prefixWord ++ tailWord_4077089) baseStart_4077089 baseEnd_4077089 := by
    simpa [prefixWord, tailWord_4077089, baseEnd_4077089] using wordTrace_append hprefix tailTrace_4077089
  have hstable : (prefixWord ++ tailWord_4077089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077089).length < 2 ^ (prefixWord ++ tailWord_4077089).sum := by decide
  have hdescent : baseEnd_4077089 < baseStart_4077089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077115 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6]
def baseStart_4077115 : Nat := 118140960795 + 4077115 * 2 ^ 59
def prefixEnd_4077115 : Nat := 4983230072969 + 3 ^ 40 * 4077115 * 2
def baseEnd_4077115 : Nat := 2093519678655921002512195

theorem tailTrace_4077115 : CollatzResearch.WordTrace tailWord_4077115 prefixEnd_4077115 2093519678655921002512195 := by
  unfold tailWord_4077115
  simp only [CollatzResearch.WordTrace]
  refine ⟨148704600624316145650576799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99136400416210763767051199 148704600624316145650576799)
  ·
    refine ⟨223056900936474218475865199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148704600624316145650576799 223056900936474218475865199)
    ·
      refine ⟨334585351404711327713797799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223056900936474218475865199 334585351404711327713797799)
      ·
        refine ⟨501878027107066991570696699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334585351404711327713797799 501878027107066991570696699)
        ·
          refine ⟨752817040660600487356045049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501878027107066991570696699 752817040660600487356045049)
          ·
            refine ⟨564612780495450365517033787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 752817040660600487356045049 564612780495450365517033787)
            ·
              refine ⟨846919170743175548275550681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 564612780495450365517033787 846919170743175548275550681)
              ·
                refine ⟨635189378057381661206663011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 846919170743175548275550681 635189378057381661206663011)
                ·
                  refine ⟨952784067086072491809994517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 635189378057381661206663011 952784067086072491809994517)
                  ·
                    refine ⟨44661753144659648053593493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 952784067086072491809994517 44661753144659648053593493)
                    ·
                      refine ⟨2093519678655921002512195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44661753144659648053593493 2093519678655921002512195)
                      ·
                        rfl

theorem cell23_4077115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 6].length) (baseStart_4077115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077115 prefixEnd_4077115 := by exact prefixLift 4077115
  have htrace : WordTrace (prefixWord ++ tailWord_4077115) baseStart_4077115 baseEnd_4077115 := by
    simpa [prefixWord, tailWord_4077115, baseEnd_4077115] using wordTrace_append hprefix tailTrace_4077115
  have hstable : (prefixWord ++ tailWord_4077115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077115).length < 2 ^ (prefixWord ++ tailWord_4077115).sum := by decide
  have hdescent : baseEnd_4077115 < baseStart_4077115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077179 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 2, 4, 2]
def baseStart_4077179 : Nat := 118140960795 + 4077179 * 2 ^ 59
def prefixEnd_4077179 : Nat := 4983230072969 + 3 ^ 40 * 4077179 * 2
def baseEnd_4077179 : Nat := 2093552541417808752111901

theorem tailTrace_4077179 : CollatzResearch.WordTrace tailWord_4077179 prefixEnd_4077179 2093552541417808752111901 := by
  unfold tailWord_4077179
  simp only [CollatzResearch.WordTrace]
  refine ⟨148706934896084284580906591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99137956597389523053937727 148706934896084284580906591)
  ·
    refine ⟨223060402344126426871359887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148706934896084284580906591 223060402344126426871359887)
    ·
      refine ⟨334590603516189640307039831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223060402344126426871359887 334590603516189640307039831)
      ·
        refine ⟨501885905274284460460559747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334590603516189640307039831 501885905274284460460559747)
        ·
          refine ⟨752828857911426690690839621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 501885905274284460460559747 752828857911426690690839621)
          ·
            refine ⟨141155410858392504504532429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 752828857911426690690839621 141155410858392504504532429)
            ·
              refine ⟨52933279071897189189199661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 141155410858392504504532429 52933279071897189189199661)
              ·
                refine ⟨19849979651961445945949873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52933279071897189189199661 19849979651961445945949873)
                ·
                  refine ⟨14887484738971084459462405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19849979651961445945949873 14887484738971084459462405)
                  ·
                    refine ⟨2791403388557078336149201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14887484738971084459462405 2791403388557078336149201)
                    ·
                      refine ⟨2093552541417808752111901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791403388557078336149201 2093552541417808752111901)
                      ·
                        rfl

theorem cell23_4077179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 2, 4, 2].length) (baseStart_4077179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077179 prefixEnd_4077179 := by exact prefixLift 4077179
  have htrace : WordTrace (prefixWord ++ tailWord_4077179) baseStart_4077179 baseEnd_4077179 := by
    simpa [prefixWord, tailWord_4077179, baseEnd_4077179] using wordTrace_append hprefix tailTrace_4077179
  have hstable : (prefixWord ++ tailWord_4077179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077179).length < 2 ^ (prefixWord ++ tailWord_4077179).sum := by decide
  have hdescent : baseEnd_4077179 < baseStart_4077179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077189 : List Nat := [1, 3, 1, 1, 4, 1, 1, 4, 3, 4]
def baseStart_4077189 : Nat := 118140960795 + 4077189 * 2 ^ 59
def prefixEnd_4077189 : Nat := 4983230072969 + 3 ^ 40 * 4077189 * 2
def baseEnd_4077189 : Nat := 697852558741451237662285

theorem tailTrace_4077189 : CollatzResearch.WordTrace tailWord_4077189 prefixEnd_4077189 697852558741451237662285 := by
  unfold tailWord_4077189
  simp only [CollatzResearch.WordTrace]
  refine ⟨148707299626048056288770621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99138199750698704192513747 148707299626048056288770621)
  ·
    refine ⟨55765237359768021108288983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148707299626048056288770621 55765237359768021108288983)
    ·
      refine ⟨83647856039652031662433475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55765237359768021108288983 83647856039652031662433475)
      ·
        refine ⟨125471784059478047493650213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83647856039652031662433475 125471784059478047493650213)
        ·
          refine ⟨23525959511152133905059415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125471784059478047493650213 23525959511152133905059415)
          ·
            refine ⟨35288939266728200857589123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23525959511152133905059415 35288939266728200857589123)
            ·
              refine ⟨52933408900092301286383685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35288939266728200857589123 52933408900092301286383685)
              ·
                refine ⟨9925014168767306491196941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52933408900092301286383685 9925014168767306491196941)
                ·
                  refine ⟨3721880313287739934198853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9925014168767306491196941 3721880313287739934198853)
                  ·
                    refine ⟨697852558741451237662285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3721880313287739934198853 697852558741451237662285)
                    ·
                      rfl

theorem cell23_4077189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 4, 3, 4].length) (baseStart_4077189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077189 prefixEnd_4077189 := by exact prefixLift 4077189
  have htrace : WordTrace (prefixWord ++ tailWord_4077189) baseStart_4077189 baseEnd_4077189 := by
    simpa [prefixWord, tailWord_4077189, baseEnd_4077189] using wordTrace_append hprefix tailTrace_4077189
  have hstable : (prefixWord ++ tailWord_4077189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077189).length < 2 ^ (prefixWord ++ tailWord_4077189).sum := by decide
  have hdescent : baseEnd_4077189 < baseStart_4077189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077216 : List Nat := [2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_4077216 : Nat := 118140960795 + 4077216 * 2 ^ 59
def prefixEnd_4077216 : Nat := 4983230072969 + 3 ^ 40 * 4077216 * 2
def baseEnd_4077216 : Nat := 2093571540202025107349231

theorem tailTrace_4077216 : CollatzResearch.WordTrace tailWord_4077216 prefixEnd_4077216 2093571540202025107349231 := by
  unfold tailWord_4077216
  simp only [CollatzResearch.WordTrace]
  refine ⟨74354142198475119950001751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99138856264633493266669001 74354142198475119950001751)
  ·
    refine ⟨111531213297712679925002627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74354142198475119950001751 111531213297712679925002627)
    ·
      refine ⟨167296819946569019887503941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111531213297712679925002627 167296819946569019887503941)
      ·
        refine ⟨31368153739981691228906989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167296819946569019887503941 31368153739981691228906989)
        ·
          refine ⟨11763057652493134210840121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31368153739981691228906989 11763057652493134210840121)
          ·
            refine ⟨8822293239369850658130091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11763057652493134210840121 8822293239369850658130091)
            ·
              refine ⟨13233439859054775987195137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822293239369850658130091 13233439859054775987195137)
              ·
                refine ⟨9925079894291081990396353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13233439859054775987195137 9925079894291081990396353)
                ·
                  refine ⟨7443809920718311492797265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9925079894291081990396353 7443809920718311492797265)
                  ·
                    refine ⟨5582857440538733619597949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7443809920718311492797265 5582857440538733619597949)
                    ·
                      refine ⟨2093571540202025107349231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582857440538733619597949 2093571540202025107349231)
                      ·
                        rfl

theorem cell23_4077216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_4077216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077216 prefixEnd_4077216 := by exact prefixLift 4077216
  have htrace : WordTrace (prefixWord ++ tailWord_4077216) baseStart_4077216 baseEnd_4077216 := by
    simpa [prefixWord, tailWord_4077216, baseEnd_4077216] using wordTrace_append hprefix tailTrace_4077216
  have hstable : (prefixWord ++ tailWord_4077216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077216).length < 2 ^ (prefixWord ++ tailWord_4077216).sum := by decide
  have hdescent : baseEnd_4077216 < baseStart_4077216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077270 : List Nat := [5, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_4077270 : Nat := 118140960795 + 4077270 * 2 ^ 59
def prefixEnd_4077270 : Nat := 4983230072969 + 3 ^ 40 * 4077270 * 2
def baseEnd_4077270 : Nat := 232622140906374210674887

theorem tailTrace_4077270 : CollatzResearch.WordTrace tailWord_4077270 prefixEnd_4077270 232622140906374210674887 := by
  unfold tailWord_4077270
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294390871172162945154329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99140169292503071414979509 9294390871172162945154329)
  ·
    refine ⟨6970793153379122208865747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9294390871172162945154329 6970793153379122208865747)
    ·
      refine ⟨10456189730068683313298621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6970793153379122208865747 10456189730068683313298621)
      ·
        refine ⟨3921071148775756242486983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10456189730068683313298621 3921071148775756242486983)
        ·
          refine ⟨5881606723163634363730475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921071148775756242486983 5881606723163634363730475)
          ·
            refine ⟨8822410084745451545595713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881606723163634363730475 8822410084745451545595713)
            ·
              refine ⟨6616807563559088659196785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8822410084745451545595713 6616807563559088659196785)
              ·
                refine ⟨4962605672669316494397589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616807563559088659196785 4962605672669316494397589)
                ·
                  refine ⟨232622140906374210674887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4962605672669316494397589 232622140906374210674887)
                  ·
                    rfl

theorem cell23_4077270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_4077270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077270 prefixEnd_4077270 := by exact prefixLift 4077270
  have htrace : WordTrace (prefixWord ++ tailWord_4077270) baseStart_4077270 baseEnd_4077270 := by
    simpa [prefixWord, tailWord_4077270, baseEnd_4077270] using wordTrace_append hprefix tailTrace_4077270
  have hstable : (prefixWord ++ tailWord_4077270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077270).length < 2 ^ (prefixWord ++ tailWord_4077270).sum := by decide
  have hdescent : baseEnd_4077270 < baseStart_4077270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077280 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 1, 1, 3]
def baseStart_4077280 : Nat := 118140960795 + 4077280 * 2 ^ 59
def prefixEnd_4077280 : Nat := 4983230072969 + 3 ^ 40 * 4077280 * 2
def baseEnd_4077280 : Nat := 2093604402963912856948937

theorem tailTrace_4077280 : CollatzResearch.WordTrace tailWord_4077280 prefixEnd_4077280 2093604402963912856948937 := by
  unfold tailWord_4077280
  simp only [CollatzResearch.WordTrace]
  refine ⟨74355309334359189415166647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99140412445812252553555529 74355309334359189415166647)
  ·
    refine ⟨111532964001538784122749971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74355309334359189415166647 111532964001538784122749971)
    ·
      refine ⟨167299446002308176184124957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111532964001538784122749971 167299446002308176184124957)
      ·
        refine ⟨62737292250865566069046859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167299446002308176184124957 62737292250865566069046859)
        ·
          refine ⟨94105938376298349103570289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62737292250865566069046859 94105938376298349103570289)
          ·
            refine ⟨70579453782223761827677717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94105938376298349103570289 70579453782223761827677717)
            ·
              refine ⟨3308411896041738835672393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70579453782223761827677717 3308411896041738835672393)
              ·
                refine ⟨2481308922031304126754295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308411896041738835672393 2481308922031304126754295)
                ·
                  refine ⟨3721963383046956190131443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2481308922031304126754295 3721963383046956190131443)
                  ·
                    refine ⟨5582945074570434285197165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3721963383046956190131443 5582945074570434285197165)
                    ·
                      refine ⟨2093604402963912856948937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582945074570434285197165 2093604402963912856948937)
                      ·
                        rfl

theorem cell23_4077280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 1, 1, 3].length) (baseStart_4077280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077280 prefixEnd_4077280 := by exact prefixLift 4077280
  have htrace : WordTrace (prefixWord ++ tailWord_4077280) baseStart_4077280 baseEnd_4077280 := by
    simpa [prefixWord, tailWord_4077280, baseEnd_4077280] using wordTrace_append hprefix tailTrace_4077280
  have hstable : (prefixWord ++ tailWord_4077280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077280).length < 2 ^ (prefixWord ++ tailWord_4077280).sum := by decide
  have hdescent : baseEnd_4077280 < baseStart_4077280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077299 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4]
def baseStart_4077299 : Nat := 118140960795 + 4077299 * 2 ^ 59
def prefixEnd_4077299 : Nat := 4983230072969 + 3 ^ 40 * 4077299 * 2
def baseEnd_4077299 : Nat := 2093614159096348282611349

theorem tailTrace_4077299 : CollatzResearch.WordTrace tailWord_4077299 prefixEnd_4077299 2093614159096348282611349 := by
  unfold tailWord_4077299
  simp only [CollatzResearch.WordTrace]
  refine ⟨148711311655649545075274951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99140874437099696716849967 148711311655649545075274951)
  ·
    refine ⟨223066967483474317612912427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148711311655649545075274951 223066967483474317612912427)
    ·
      refine ⟨334600451225211476419368641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223066967483474317612912427 334600451225211476419368641)
      ·
        refine ⟨250950338418908607314526481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334600451225211476419368641 250950338418908607314526481)
        ·
          refine ⟨188212753814181455485894861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250950338418908607314526481 188212753814181455485894861)
          ·
            refine ⟨70579782680318045807210573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188212753814181455485894861 70579782680318045807210573)
            ·
              refine ⟨26467418505119267177703965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70579782680318045807210573 26467418505119267177703965)
              ·
                refine ⟨9925281939419725191638987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26467418505119267177703965 9925281939419725191638987)
                ·
                  refine ⟨14887922909129587787458481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925281939419725191638987 14887922909129587787458481)
                  ·
                    refine ⟨11165942181847190840593861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14887922909129587787458481 11165942181847190840593861)
                    ·
                      refine ⟨2093614159096348282611349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11165942181847190840593861 2093614159096348282611349)
                      ·
                        rfl

theorem cell23_4077299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_4077299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077299 prefixEnd_4077299 := by exact prefixLift 4077299
  have htrace : WordTrace (prefixWord ++ tailWord_4077299) baseStart_4077299 baseEnd_4077299 := by
    simpa [prefixWord, tailWord_4077299, baseEnd_4077299] using wordTrace_append hprefix tailTrace_4077299
  have hstable : (prefixWord ++ tailWord_4077299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077299).length < 2 ^ (prefixWord ++ tailWord_4077299).sum := by decide
  have hdescent : baseEnd_4077299 < baseStart_4077299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077306 : List Nat := [3, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3]
def baseStart_4077306 : Nat := 118140960795 + 4077306 * 2 ^ 59
def prefixEnd_4077306 : Nat := 4983230072969 + 3 ^ 40 * 4077306 * 2
def baseEnd_4077306 : Nat := 2093617753460929755223817

theorem tailTrace_4077306 : CollatzResearch.WordTrace tailWord_4077306 prefixEnd_4077306 2093617753460929755223817 := by
  unfold tailWord_4077306
  simp only [CollatzResearch.WordTrace]
  refine ⟨37177891741656046317694943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99141044644416123513853181 37177891741656046317694943)
  ·
    refine ⟨55766837612484069476542415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37177891741656046317694943 55766837612484069476542415)
    ·
      refine ⟨83650256418726104214813623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55766837612484069476542415 83650256418726104214813623)
      ·
        refine ⟨125475384628089156322220435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83650256418726104214813623 125475384628089156322220435)
        ·
          refine ⟨188213076942133734483330653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125475384628089156322220435 188213076942133734483330653)
          ·
            refine ⟨70579903853300150431248995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188213076942133734483330653 70579903853300150431248995)
            ·
              refine ⟨105869855779950225646873493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70579903853300150431248995 105869855779950225646873493)
              ·
                refine ⟨4962649489685166827197195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105869855779950225646873493 4962649489685166827197195)
                ·
                  refine ⟨7443974234527750240795793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962649489685166827197195 7443974234527750240795793)
                  ·
                    refine ⟨5582980675895812680596845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7443974234527750240795793 5582980675895812680596845)
                    ·
                      refine ⟨2093617753460929755223817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5582980675895812680596845 2093617753460929755223817)
                      ·
                        rfl

theorem cell23_4077306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 6, 1, 2, 3].length) (baseStart_4077306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077306 prefixEnd_4077306 := by exact prefixLift 4077306
  have htrace : WordTrace (prefixWord ++ tailWord_4077306) baseStart_4077306 baseEnd_4077306 := by
    simpa [prefixWord, tailWord_4077306, baseEnd_4077306] using wordTrace_append hprefix tailTrace_4077306
  have hstable : (prefixWord ++ tailWord_4077306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077306).length < 2 ^ (prefixWord ++ tailWord_4077306).sum := by decide
  have hdescent : baseEnd_4077306 < baseStart_4077306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077316 : List Nat := [2, 3, 2, 2, 1, 2, 2, 2, 1, 2, 4]
def baseStart_4077316 : Nat := 118140960795 + 4077316 * 2 ^ 59
def prefixEnd_4077316 : Nat := 4983230072969 + 3 ^ 40 * 4077316 * 2
def baseEnd_4077316 : Nat := 2093622888267474716098771

theorem tailTrace_4077316 : CollatzResearch.WordTrace tailWord_4077316 prefixEnd_4077316 2093622888267474716098771 := by
  unfold tailWord_4077316
  simp only [CollatzResearch.WordTrace]
  refine ⟨74355965848293978489321901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99141287797725304652429201 74355965848293978489321901)
  ·
    refine ⟨27883487193110241933495713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74355965848293978489321901 27883487193110241933495713)
    ·
      refine ⟨20912615394832681450121785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27883487193110241933495713 20912615394832681450121785)
      ·
        refine ⟨15684461546124511087591339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20912615394832681450121785 15684461546124511087591339)
        ·
          refine ⟨23526692319186766631387009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15684461546124511087591339 23526692319186766631387009)
          ·
            refine ⟨17645019239390074973540257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23526692319186766631387009 17645019239390074973540257)
            ·
              refine ⟨13233764429542556230155193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17645019239390074973540257 13233764429542556230155193)
              ·
                refine ⟨9925323322156917172616395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13233764429542556230155193 9925323322156917172616395)
                ·
                  refine ⟨14887984983235375758924593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9925323322156917172616395 14887984983235375758924593)
                  ·
                    refine ⟨11165988737426531819193445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14887984983235375758924593 11165988737426531819193445)
                    ·
                      refine ⟨2093622888267474716098771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11165988737426531819193445 2093622888267474716098771)
                      ·
                        rfl

theorem cell23_4077316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_4077316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077316 prefixEnd_4077316 := by exact prefixLift 4077316
  have htrace : WordTrace (prefixWord ++ tailWord_4077316) baseStart_4077316 baseEnd_4077316 := by
    simpa [prefixWord, tailWord_4077316, baseEnd_4077316] using wordTrace_append hprefix tailTrace_4077316
  have hstable : (prefixWord ++ tailWord_4077316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077316).length < 2 ^ (prefixWord ++ tailWord_4077316).sum := by decide
  have hdescent : baseEnd_4077316 < baseStart_4077316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077323 : List Nat := [1, 1, 1, 1, 5, 1, 6, 1, 1, 2, 3]
def baseStart_4077323 : Nat := 118140960795 + 4077323 * 2 ^ 59
def prefixEnd_4077323 : Nat := 4983230072969 + 3 ^ 40 * 4077323 * 2
def baseEnd_4077323 : Nat := 2093626482632056188711239

theorem tailTrace_4077323 : CollatzResearch.WordTrace tailWord_4077323 prefixEnd_4077323 2093626482632056188711239 := by
  unfold tailWord_4077323
  simp only [CollatzResearch.WordTrace]
  refine ⟨148712187007562597174148623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99141458005041731449432415 148712187007562597174148623)
  ·
    refine ⟨223068280511343895761222935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148712187007562597174148623 223068280511343895761222935)
    ·
      refine ⟨334602420767015843641834403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223068280511343895761222935 334602420767015843641834403)
      ·
        refine ⟨501903631150523765462751605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 334602420767015843641834403 501903631150523765462751605)
        ·
          refine ⟨47053465420361603012132963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 501903631150523765462751605 47053465420361603012132963)
          ·
            refine ⟨70580198130542404518199445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47053465420361603012132963 70580198130542404518199445)
            ·
              refine ⟨3308446787369175211790599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70580198130542404518199445 3308446787369175211790599)
              ·
                refine ⟨4962670181053762817685899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308446787369175211790599 4962670181053762817685899)
                ·
                  refine ⟨7444005271580644226528849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4962670181053762817685899 7444005271580644226528849)
                  ·
                    refine ⟨5583003953685483169896637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444005271580644226528849 5583003953685483169896637)
                    ·
                      refine ⟨2093626482632056188711239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5583003953685483169896637 2093626482632056188711239)
                      ·
                        rfl

theorem cell23_4077323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 6, 1, 1, 2, 3].length) (baseStart_4077323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077323 prefixEnd_4077323 := by exact prefixLift 4077323
  have htrace : WordTrace (prefixWord ++ tailWord_4077323) baseStart_4077323 baseEnd_4077323 := by
    simpa [prefixWord, tailWord_4077323, baseEnd_4077323] using wordTrace_append hprefix tailTrace_4077323
  have hstable : (prefixWord ++ tailWord_4077323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077323).length < 2 ^ (prefixWord ++ tailWord_4077323).sum := by decide
  have hdescent : baseEnd_4077323 < baseStart_4077323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077330 : List Nat := [3, 2, 4, 1, 1, 1, 3, 2, 2, 4]
def baseStart_4077330 : Nat := 118140960795 + 4077330 * 2 ^ 59
def prefixEnd_4077330 : Nat := 4983230072969 + 3 ^ 40 * 4077330 * 2
def baseEnd_4077330 : Nat := 697876692332212553774569

theorem tailTrace_4077330 : CollatzResearch.WordTrace tailWord_4077330 prefixEnd_4077330 697876692332212553774569 := by
  unfold tailWord_4077330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178110579634309342413361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99141628212358158246435629 37178110579634309342413361)
  ·
    refine ⟨27883582934725732006810021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37178110579634309342413361 27883582934725732006810021)
    ·
      refine ⟨5228171800261074751276879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27883582934725732006810021 5228171800261074751276879)
      ·
        refine ⟨7842257700391612126915319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228171800261074751276879 7842257700391612126915319)
        ·
          refine ⟨11763386550587418190372979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842257700391612126915319 11763386550587418190372979)
          ·
            refine ⟨17645079825881127285559469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11763386550587418190372979 17645079825881127285559469)
            ·
              refine ⟨6616904934705422732084801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17645079825881127285559469 6616904934705422732084801)
              ·
                refine ⟨4962678701029067049063601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6616904934705422732084801 4962678701029067049063601)
                ·
                  refine ⟨3722009025771800286797701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962678701029067049063601 3722009025771800286797701)
                  ·
                    refine ⟨697876692332212553774569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3722009025771800286797701 697876692332212553774569)
                    ·
                      rfl

theorem cell23_4077330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_4077330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077330 prefixEnd_4077330 := by exact prefixLift 4077330
  have htrace : WordTrace (prefixWord ++ tailWord_4077330) baseStart_4077330 baseEnd_4077330 := by
    simpa [prefixWord, tailWord_4077330, baseEnd_4077330] using wordTrace_append hprefix tailTrace_4077330
  have hstable : (prefixWord ++ tailWord_4077330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077330).length < 2 ^ (prefixWord ++ tailWord_4077330).sum := by decide
  have hdescent : baseEnd_4077330 < baseStart_4077330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077379 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5]
def baseStart_4077379 : Nat := 118140960795 + 4077379 * 2 ^ 59
def prefixEnd_4077379 : Nat := 4983230072969 + 3 ^ 40 * 4077379 * 2
def baseEnd_4077379 : Nat := 2093655237548707969610981

theorem tailTrace_4077379 : CollatzResearch.WordTrace tailWord_4077379 prefixEnd_4077379 2093655237548707969610981 := by
  unfold tailWord_4077379
  simp only [CollatzResearch.WordTrace]
  refine ⟨148714229495359718738187191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99142819663573145825458127 148714229495359718738187191)
  ·
    refine ⟨223071344243039578107280787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148714229495359718738187191 223071344243039578107280787)
    ·
      refine ⟨334607016364559367160921181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223071344243039578107280787 334607016364559367160921181)
      ·
        refine ⟨125477631136709762685345443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334607016364559367160921181 125477631136709762685345443)
        ·
          refine ⟨188216446705064644028018165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125477631136709762685345443 188216446705064644028018165)
          ·
            refine ⟨17645291878599810377626703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188216446705064644028018165 17645291878599810377626703)
            ·
              refine ⟨26467937817899715566440055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17645291878599810377626703 26467937817899715566440055)
              ·
                refine ⟨39701906726849573349660083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26467937817899715566440055 39701906726849573349660083)
                ·
                  refine ⟨59552860090274360024490125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39701906726849573349660083 59552860090274360024490125)
                  ·
                    refine ⟨22332322533852885009183797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59552860090274360024490125 22332322533852885009183797)
                    ·
                      refine ⟨2093655237548707969610981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22332322533852885009183797 2093655237548707969610981)
                      ·
                        rfl

theorem cell23_4077379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_4077379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077379 prefixEnd_4077379 := by exact prefixLift 4077379
  have htrace : WordTrace (prefixWord ++ tailWord_4077379) baseStart_4077379 baseEnd_4077379 := by
    simpa [prefixWord, tailWord_4077379, baseEnd_4077379] using wordTrace_append hprefix tailTrace_4077379
  have hstable : (prefixWord ++ tailWord_4077379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077379).length < 2 ^ (prefixWord ++ tailWord_4077379).sum := by decide
  have hdescent : baseEnd_4077379 < baseStart_4077379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077404 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4077404 : Nat := 118140960795 + 4077404 * 2 ^ 59
def prefixEnd_4077404 : Nat := 4983230072969 + 3 ^ 40 * 4077404 * 2
def baseEnd_4077404 : Nat := 2093668074565070371798367

theorem tailTrace_4077404 : CollatzResearch.WordTrace tailWord_4077404 prefixEnd_4077404 2093668074565070371798367 := by
  unfold tailWord_4077404
  simp only [CollatzResearch.WordTrace]
  refine ⟨74357570660134574003923633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99143427546846098671898177 74357570660134574003923633)
  ·
    refine ⟨55768177995100930502942725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74357570660134574003923633 55768177995100930502942725)
    ·
      refine ⟨10456533374081424469301761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55768177995100930502942725 10456533374081424469301761)
      ·
        refine ⟨7842400030561068351976321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10456533374081424469301761 7842400030561068351976321)
        ·
          refine ⟨5881800022920801263982241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842400030561068351976321 5881800022920801263982241)
          ·
            refine ⟨4411350017190600947986681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5881800022920801263982241 4411350017190600947986681)
            ·
              refine ⟨3308512512892950710990011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411350017190600947986681 3308512512892950710990011)
              ·
                refine ⟨4962768769339426066485017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308512512892950710990011 4962768769339426066485017)
                ·
                  refine ⟨3722076577004569549863763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4962768769339426066485017 3722076577004569549863763)
                  ·
                    refine ⟨5583114865506854324795645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3722076577004569549863763 5583114865506854324795645)
                    ·
                      refine ⟨2093668074565070371798367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5583114865506854324795645 2093668074565070371798367)
                      ·
                        rfl

theorem cell23_4077404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4077404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077404 prefixEnd_4077404 := by exact prefixLift 4077404
  have htrace : WordTrace (prefixWord ++ tailWord_4077404) baseStart_4077404 baseEnd_4077404 := by
    simpa [prefixWord, tailWord_4077404, baseEnd_4077404] using wordTrace_append hprefix tailTrace_4077404
  have hstable : (prefixWord ++ tailWord_4077404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077404).length < 2 ^ (prefixWord ++ tailWord_4077404).sum := by decide
  have hdescent : baseEnd_4077404 < baseStart_4077404 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077426 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3]
def baseStart_4077426 : Nat := 118140960795 + 4077426 * 2 ^ 59
def prefixEnd_4077426 : Nat := 4983230072969 + 3 ^ 40 * 4077426 * 2
def baseEnd_4077426 : Nat := 2093679371139469285723265

theorem tailTrace_4077426 : CollatzResearch.WordTrace tailWord_4077426 prefixEnd_4077426 2093679371139469285723265 := by
  unfold tailWord_4077426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37178985931547361441287033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99143962484126297176765421 37178985931547361441287033)
  ·
    refine ⟨27884239448660521080965275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37178985931547361441287033 27884239448660521080965275)
    ·
      refine ⟨41826359172990781621447913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27884239448660521080965275 41826359172990781621447913)
      ·
        refine ⟨31369769379743086216085935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41826359172990781621447913 31369769379743086216085935)
        ·
          refine ⟨47054654069614629324128903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31369769379743086216085935 47054654069614629324128903)
          ·
            refine ⟨70581981104421943986193355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47054654069614629324128903 70581981104421943986193355)
            ·
              refine ⟨105872971656632915979290033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70581981104421943986193355 105872971656632915979290033)
              ·
                refine ⟨79404728742474686984467525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105872971656632915979290033 79404728742474686984467525)
                ·
                  refine ⟨14888386639214003809587661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79404728742474686984467525 14888386639214003809587661)
                  ·
                    refine ⟨5583144989705251428595373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14888386639214003809587661 5583144989705251428595373)
                    ·
                      refine ⟨2093679371139469285723265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5583144989705251428595373 2093679371139469285723265)
                      ·
                        rfl

theorem cell23_4077426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 4, 3, 3].length) (baseStart_4077426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077426 prefixEnd_4077426 := by exact prefixLift 4077426
  have htrace : WordTrace (prefixWord ++ tailWord_4077426) baseStart_4077426 baseEnd_4077426 := by
    simpa [prefixWord, tailWord_4077426, baseEnd_4077426] using wordTrace_append hprefix tailTrace_4077426
  have hstable : (prefixWord ++ tailWord_4077426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077426).length < 2 ^ (prefixWord ++ tailWord_4077426).sum := by decide
  have hdescent : baseEnd_4077426 < baseStart_4077426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077450 : List Nat := [3, 1, 2, 4, 2, 1, 1, 4, 5]
def baseStart_4077450 : Nat := 118140960795 + 4077450 * 2 ^ 59
def prefixEnd_4077450 : Nat := 4983230072969 + 3 ^ 40 * 4077450 * 2
def baseEnd_4077450 : Nat := 232632410519464132424795

theorem tailTrace_4077450 : CollatzResearch.WordTrace tailWord_4077450 prefixEnd_4077450 232632410519464132424795 := by
  unfold tailWord_4077450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37179204769525624466005451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99144546052068331909347869 37179204769525624466005451)
  ·
    refine ⟨55768807154288436699008177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37179204769525624466005451 55768807154288436699008177)
    ·
      refine ⟨41826605365716327524256133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55768807154288436699008177 41826605365716327524256133)
      ·
        refine ⟨7842488506071811410798025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41826605365716327524256133 7842488506071811410798025)
        ·
          refine ⟨5881866379553858558098519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7842488506071811410798025 5881866379553858558098519)
          ·
            refine ⟨8822799569330787837147779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881866379553858558098519 8822799569330787837147779)
            ·
              refine ⟨13234199353996181755721669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822799569330787837147779 13234199353996181755721669)
              ·
                refine ⟨2481412378874284079197813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13234199353996181755721669 2481412378874284079197813)
                ·
                  refine ⟨232632410519464132424795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2481412378874284079197813 232632410519464132424795)
                  ·
                    rfl

theorem cell23_4077450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 4, 5].length) (baseStart_4077450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077450 prefixEnd_4077450 := by exact prefixLift 4077450
  have htrace : WordTrace (prefixWord ++ tailWord_4077450) baseStart_4077450 baseEnd_4077450 := by
    simpa [prefixWord, tailWord_4077450, baseEnd_4077450] using wordTrace_append hprefix tailTrace_4077450
  have hstable : (prefixWord ++ tailWord_4077450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077450).length < 2 ^ (prefixWord ++ tailWord_4077450).sum := by decide
  have hdescent : baseEnd_4077450 < baseStart_4077450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077480 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 1, 7]
def baseStart_4077480 : Nat := 118140960795 + 4077480 * 2 ^ 59
def prefixEnd_4077480 : Nat := 4983230072969 + 3 ^ 40 * 4077480 * 2
def baseEnd_4077480 : Nat := 697902366364937358149339

theorem tailTrace_4077480 : CollatzResearch.WordTrace tailWord_4077480 prefixEnd_4077480 697902366364937358149339 := by
  unfold tailWord_4077480
  simp only [CollatzResearch.WordTrace]
  refine ⟨74358956633996906493806947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99145275511995875325075929 74358956633996906493806947)
  ·
    refine ⟨111538434950995359740710421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74358956633996906493806947 111538434950995359740710421)
    ·
      refine ⟨5228364138327907487845801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 111538434950995359740710421 5228364138327907487845801)
      ·
        refine ⟨3921273103745930615884351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5228364138327907487845801 3921273103745930615884351)
        ·
          refine ⟨5881909655618895923826527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921273103745930615884351 5881909655618895923826527)
          ·
            refine ⟨8822864483428343885739791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5881909655618895923826527 8822864483428343885739791)
            ·
              refine ⟨13234296725142515828609687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8822864483428343885739791 13234296725142515828609687)
              ·
                refine ⟨19851445087713773742914531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13234296725142515828609687 19851445087713773742914531)
                ·
                  refine ⟨29777167631570660614371797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19851445087713773742914531 29777167631570660614371797)
                  ·
                    refine ⟨697902366364937358149339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29777167631570660614371797 697902366364937358149339)
                    ·
                      rfl

theorem cell23_4077480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_4077480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077480 prefixEnd_4077480 := by exact prefixLift 4077480
  have htrace : WordTrace (prefixWord ++ tailWord_4077480) baseStart_4077480 baseEnd_4077480 := by
    simpa [prefixWord, tailWord_4077480, baseEnd_4077480] using wordTrace_append hprefix tailTrace_4077480
  have hstable : (prefixWord ++ tailWord_4077480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077480).length < 2 ^ (prefixWord ++ tailWord_4077480).sum := by decide
  have hdescent : baseEnd_4077480 < baseStart_4077480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077536 : List Nat := [2, 1, 1, 3, 1, 1, 1, 5, 3, 5]
def baseStart_4077536 : Nat := 118140960795 + 4077536 * 2 ^ 59
def prefixEnd_4077536 : Nat := 4983230072969 + 3 ^ 40 * 4077536 * 2
def baseEnd_4077536 : Nat := 697911951337154618449253

theorem tailTrace_4077536 : CollatzResearch.WordTrace tailWord_4077536 prefixEnd_4077536 697911951337154618449253 := by
  unfold tailWord_4077536
  simp only [CollatzResearch.WordTrace]
  refine ⟨74359977877895467275826231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99146637170527289701101641 74359977877895467275826231)
  ·
    refine ⟨111539966816843200913739347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74359977877895467275826231 111539966816843200913739347)
    ·
      refine ⟨167309950225264801370609021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111539966816843200913739347 167309950225264801370609021)
      ·
        refine ⟨62741231334474300513978383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167309950225264801370609021 62741231334474300513978383)
        ·
          refine ⟨94111847001711450770967575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62741231334474300513978383 94111847001711450770967575)
          ·
            refine ⟨141167770502567176156451363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94111847001711450770967575 141167770502567176156451363)
            ·
              refine ⟨211751655753850764234677045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141167770502567176156451363 211751655753850764234677045)
              ·
                refine ⟨19851717726923509147000973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 211751655753850764234677045 19851717726923509147000973)
                ·
                  refine ⟨7444394147596315930125365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19851717726923509147000973 7444394147596315930125365)
                  ·
                    refine ⟨697911951337154618449253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7444394147596315930125365 697911951337154618449253)
                    ·
                      rfl

theorem cell23_4077536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_4077536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077536 prefixEnd_4077536 := by exact prefixLift 4077536
  have htrace : WordTrace (prefixWord ++ tailWord_4077536) baseStart_4077536 baseEnd_4077536 := by
    simpa [prefixWord, tailWord_4077536, baseEnd_4077536] using wordTrace_append hprefix tailTrace_4077536
  have hstable : (prefixWord ++ tailWord_4077536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077536).length < 2 ^ (prefixWord ++ tailWord_4077536).sum := by decide
  have hdescent : baseEnd_4077536 < baseStart_4077536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077603 : List Nat := [1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4]
def baseStart_4077603 : Nat := 118140960795 + 4077603 * 2 ^ 59
def prefixEnd_4077603 : Nat := 4983230072969 + 3 ^ 40 * 4077603 * 2
def baseEnd_4077603 : Nat := 2093770257215315093209951

theorem tailTrace_4077603 : CollatzResearch.WordTrace tailWord_4077603 prefixEnd_4077603 2093770257215315093209951 := by
  unfold tailWord_4077603
  simp only [CollatzResearch.WordTrace]
  refine ⟨148722399446548204994341463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99148266297698803329560975 148722399446548204994341463)
  ·
    refine ⟨223083599169822307491512195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148722399446548204994341463 223083599169822307491512195)
    ·
      refine ⟨334625398754733461237268293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223083599169822307491512195 334625398754733461237268293)
      ·
        refine ⟨62742262266512523981987805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 334625398754733461237268293 62742262266512523981987805)
        ·
          refine ⟨23528348349942196493245427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62742262266512523981987805 23528348349942196493245427)
          ·
            refine ⟨35292522524913294739868141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23528348349942196493245427 35292522524913294739868141)
            ·
              refine ⟨13234695946842485527450553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35292522524913294739868141 13234695946842485527450553)
              ·
                refine ⟨9926021960131864145587915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13234695946842485527450553 9926021960131864145587915)
                ·
                  refine ⟨14889032940197796218381873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9926021960131864145587915 14889032940197796218381873)
                  ·
                    refine ⟨11166774705148347163786405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14889032940197796218381873 11166774705148347163786405)
                    ·
                      refine ⟨2093770257215315093209951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11166774705148347163786405 2093770257215315093209951)
                      ·
                        rfl

theorem cell23_4077603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_4077603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077603 prefixEnd_4077603 := by exact prefixLift 4077603
  have htrace : WordTrace (prefixWord ++ tailWord_4077603) baseStart_4077603 baseEnd_4077603 := by
    simpa [prefixWord, tailWord_4077603, baseEnd_4077603] using wordTrace_append hprefix tailTrace_4077603
  have hstable : (prefixWord ++ tailWord_4077603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077603).length < 2 ^ (prefixWord ++ tailWord_4077603).sum := by decide
  have hdescent : baseEnd_4077603 < baseStart_4077603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077610 : List Nat := [3, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_4077610 : Nat := 118140960795 + 4077610 * 2 ^ 59
def prefixEnd_4077610 : Nat := 4983230072969 + 3 ^ 40 * 4077610 * 2
def baseEnd_4077610 : Nat := 2093773851579896565822419

theorem tailTrace_4077610 : CollatzResearch.WordTrace tailWord_4077610 prefixEnd_4077610 2093773851579896565822419 := by
  unfold tailWord_4077610
  simp only [CollatzResearch.WordTrace]
  refine ⟨37180663689380711297461571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99148436505015230126564189 37180663689380711297461571)
  ·
    refine ⟨55770995534071066946192357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37180663689380711297461571 55770995534071066946192357)
    ·
      refine ⟨10457061662638325052411067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55770995534071066946192357 10457061662638325052411067)
      ·
        refine ⟨15685592493957487578616601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10457061662638325052411067 15685592493957487578616601)
        ·
          refine ⟨11764194370468115683962451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15685592493957487578616601 11764194370468115683962451)
          ·
            refine ⟨17646291555702173525943677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11764194370468115683962451 17646291555702173525943677)
            ·
              refine ⟨6617359333388315072228879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17646291555702173525943677 6617359333388315072228879)
              ·
                refine ⟨9926039000082472608343319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6617359333388315072228879 9926039000082472608343319)
                ·
                  refine ⟨14889058500123708912514979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9926039000082472608343319 14889058500123708912514979)
                  ·
                    refine ⟨22333587750185563368772469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14889058500123708912514979 22333587750185563368772469)
                    ·
                      refine ⟨2093773851579896565822419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22333587750185563368772469 2093773851579896565822419)
                      ·
                        rfl

theorem cell23_4077610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_4077610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077610 prefixEnd_4077610 := by exact prefixLift 4077610
  have htrace : WordTrace (prefixWord ++ tailWord_4077610) baseStart_4077610 baseEnd_4077610 := by
    simpa [prefixWord, tailWord_4077610, baseEnd_4077610] using wordTrace_append hprefix tailTrace_4077610
  have hstable : (prefixWord ++ tailWord_4077610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077610).length < 2 ^ (prefixWord ++ tailWord_4077610).sum := by decide
  have hdescent : baseEnd_4077610 < baseStart_4077610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077661 : List Nat := [1, 4, 4, 1, 1, 3, 2, 1, 1, 2, 3]
def baseStart_4077661 : Nat := 118140960795 + 4077661 * 2 ^ 59
def prefixEnd_4077661 : Nat := 4983230072969 + 3 ^ 40 * 4077661 * 2
def baseEnd_4077661 : Nat := 2093800039093275866284685

theorem tailTrace_4077661 : CollatzResearch.WordTrace tailWord_4077661 prefixEnd_4077661 2093800039093275866284685 := by
  unfold tailWord_4077661
  simp only [CollatzResearch.WordTrace]
  refine ⟨148724514880338080899952837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99149676586892053933301891 148724514880338080899952837)
  ·
    refine ⟨27885846540063390168741157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148724514880338080899952837 27885846540063390168741157)
    ·
      refine ⟨5228596226261885656638967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27885846540063390168741157 5228596226261885656638967)
      ·
        refine ⟨7842894339392828484958451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5228596226261885656638967 7842894339392828484958451)
        ·
          refine ⟨11764341509089242727437677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7842894339392828484958451 11764341509089242727437677)
          ·
            refine ⟨4411628065908466022789129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11764341509089242727437677 4411628065908466022789129)
            ·
              refine ⟨3308721049431349517091847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411628065908466022789129 3308721049431349517091847)
              ·
                refine ⟨4963081574147024275637771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3308721049431349517091847 4963081574147024275637771)
                ·
                  refine ⟨7444622361220536413456657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963081574147024275637771 7444622361220536413456657)
                  ·
                    refine ⟨5583466770915402310092493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7444622361220536413456657 5583466770915402310092493)
                    ·
                      refine ⟨2093800039093275866284685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5583466770915402310092493 2093800039093275866284685)
                      ·
                        rfl

theorem cell23_4077661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_4077661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077661 prefixEnd_4077661 := by exact prefixLift 4077661
  have htrace : WordTrace (prefixWord ++ tailWord_4077661) baseStart_4077661 baseEnd_4077661 := by
    simpa [prefixWord, tailWord_4077661, baseEnd_4077661] using wordTrace_append hprefix tailTrace_4077661
  have hstable : (prefixWord ++ tailWord_4077661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077661).length < 2 ^ (prefixWord ++ tailWord_4077661).sum := by decide
  have hdescent : baseEnd_4077661 < baseStart_4077661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077703 : List Nat := [1, 1, 4, 2, 1, 1, 4, 2, 7]
def baseStart_4077703 : Nat := 118140960795 + 4077703 * 2 ^ 59
def prefixEnd_4077703 : Nat := 4983230072969 + 3 ^ 40 * 4077703 * 2
def baseEnd_4077703 : Nat := 232646845031196077995499

theorem tailTrace_4077703 : CollatzResearch.WordTrace tailWord_4077703 prefixEnd_4077703 232646845031196077995499 := by
  unfold tailWord_4077703
  simp only [CollatzResearch.WordTrace]
  refine ⟨148726046746185922072981763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99150697830790614715321175 148726046746185922072981763)
  ·
    refine ⟨223089070119278883109472645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148726046746185922072981763 223089070119278883109472645)
    ·
      refine ⟨41829200647364790583026121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223089070119278883109472645 41829200647364790583026121)
      ·
        refine ⟨31371900485523592937269591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41829200647364790583026121 31371900485523592937269591)
        ·
          refine ⟨47057850728285389405904387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31371900485523592937269591 47057850728285389405904387)
          ·
            refine ⟨70586776092428084108856581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47057850728285389405904387 70586776092428084108856581)
            ·
              refine ⟨13235020517330265770410609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70586776092428084108856581 13235020517330265770410609)
              ·
                refine ⟨9926265387997699327807957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13235020517330265770410609 9926265387997699327807957)
                ·
                  refine ⟨232646845031196077995499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9926265387997699327807957 232646845031196077995499)
                  ·
                    rfl

theorem cell23_4077703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 2, 7].length) (baseStart_4077703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077703 prefixEnd_4077703 := by exact prefixLift 4077703
  have htrace : WordTrace (prefixWord ++ tailWord_4077703) baseStart_4077703 baseEnd_4077703 := by
    simpa [prefixWord, tailWord_4077703, baseEnd_4077703] using wordTrace_append hprefix tailTrace_4077703
  have hstable : (prefixWord ++ tailWord_4077703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077703).length < 2 ^ (prefixWord ++ tailWord_4077703).sum := by decide
  have hdescent : baseEnd_4077703 < baseStart_4077703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077783 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 6]
def baseStart_4077783 : Nat := 118140960795 + 4077783 * 2 ^ 59
def prefixEnd_4077783 : Nat := 4983230072969 + 3 ^ 40 * 4077783 * 2
def baseEnd_4077783 : Nat := 2093862683733124388959123

theorem tailTrace_4077783 : CollatzResearch.WordTrace tailWord_4077783 prefixEnd_4077783 2093862683733124388959123 := by
  unfold tailWord_4077783
  simp only [CollatzResearch.WordTrace]
  refine ⟨148728964585896095735894003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99152643057264063823929335 148728964585896095735894003)
  ·
    refine ⟨223093446878844143603841005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148728964585896095735894003 223093446878844143603841005)
    ·
      refine ⟨83660042579566553851440377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223093446878844143603841005 83660042579566553851440377)
      ·
        refine ⟨62745031934674915388580283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83660042579566553851440377 62745031934674915388580283)
        ·
          refine ⟨94117547902012373082870425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62745031934674915388580283 94117547902012373082870425)
          ·
            refine ⟨70588160926509279812152819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94117547902012373082870425 70588160926509279812152819)
            ·
              refine ⟨105882241389763919718229229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70588160926509279812152819 105882241389763919718229229)
              ·
                refine ⟨39705840521161469894335961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105882241389763919718229229 39705840521161469894335961)
                ·
                  refine ⟨29779380390871102420751971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39705840521161469894335961 29779380390871102420751971)
                  ·
                    refine ⟨44669070586306653631127957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29779380390871102420751971 44669070586306653631127957)
                    ·
                      refine ⟨2093862683733124388959123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44669070586306653631127957 2093862683733124388959123)
                      ·
                        rfl

theorem cell23_4077783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_4077783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077783 prefixEnd_4077783 := by exact prefixLift 4077783
  have htrace : WordTrace (prefixWord ++ tailWord_4077783) baseStart_4077783 baseEnd_4077783 := by
    simpa [prefixWord, tailWord_4077783, baseEnd_4077783] using wordTrace_append hprefix tailTrace_4077783
  have hstable : (prefixWord ++ tailWord_4077783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077783).length < 2 ^ (prefixWord ++ tailWord_4077783).sum := by decide
  have hdescent : baseEnd_4077783 < baseStart_4077783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077788 : List Nat := [2, 2, 5, 2, 1, 2, 2, 2, 5]
def baseStart_4077788 : Nat := 118140960795 + 4077788 * 2 ^ 59
def prefixEnd_4077788 : Nat := 4983230072969 + 3 ^ 40 * 4077788 * 2
def baseEnd_4077788 : Nat := 232651694570710763266289

theorem tailTrace_4077788 : CollatzResearch.WordTrace tailWord_4077788 prefixEnd_4077788 232651694570710763266289 := by
  unfold tailWord_4077788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74364573475438990794913009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99152764633918654393217345 74364573475438990794913009)
  ·
    refine ⟨55773430106579243096184757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74364573475438990794913009 55773430106579243096184757)
    ·
      refine ⟨5228759072491804040267321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55773430106579243096184757 5228759072491804040267321)
      ·
        refine ⟨3921569304368853030200491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5228759072491804040267321 3921569304368853030200491)
        ·
          refine ⟨5882353956553279545300737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3921569304368853030200491 5882353956553279545300737)
          ·
            refine ⟨4411765467414959658975553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882353956553279545300737 4411765467414959658975553)
            ·
              refine ⟨3308824100561219744231665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4411765467414959658975553 3308824100561219744231665)
              ·
                refine ⟨2481618075420914808173749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3308824100561219744231665 2481618075420914808173749)
                ·
                  refine ⟨232651694570710763266289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2481618075420914808173749 232651694570710763266289)
                  ·
                    rfl

theorem cell23_4077788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 2, 5].length) (baseStart_4077788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077788 prefixEnd_4077788 := by exact prefixLift 4077788
  have htrace : WordTrace (prefixWord ++ tailWord_4077788) baseStart_4077788 baseEnd_4077788 := by
    simpa [prefixWord, tailWord_4077788, baseEnd_4077788] using wordTrace_append hprefix tailTrace_4077788
  have hstable : (prefixWord ++ tailWord_4077788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077788).length < 2 ^ (prefixWord ++ tailWord_4077788).sum := by decide
  have hdescent : baseEnd_4077788 < baseStart_4077788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077874 : List Nat := [3, 2, 1, 1, 5, 1, 2, 2, 1, 5]
def baseStart_4077874 : Nat := 118140960795 + 4077874 * 2 ^ 59
def prefixEnd_4077874 : Nat := 4983230072969 + 3 ^ 40 * 4077874 * 2
def baseEnd_4077874 : Nat := 697969803490894510973735

theorem tailTrace_4077874 : CollatzResearch.WordTrace tailWord_4077874 prefixEnd_4077874 697969803490894510973735 := by
  unfold tailWord_4077874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37183070907141604569364169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99154855752377612184971117 37183070907141604569364169)
  ·
    refine ⟨27887303180356203427023127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37183070907141604569364169 27887303180356203427023127)
    ·
      refine ⟨41830954770534305140534691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27887303180356203427023127 41830954770534305140534691)
      ·
        refine ⟨62746432155801457710802037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41830954770534305140534691 62746432155801457710802037)
        ·
          refine ⟨5882478014606386660387691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62746432155801457710802037 5882478014606386660387691)
          ·
            refine ⟨8823717021909579990581537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5882478014606386660387691 8823717021909579990581537)
            ·
              refine ⟨6617787766432184992936153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8823717021909579990581537 6617787766432184992936153)
              ·
                refine ⟨4963340824824138744702115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6617787766432184992936153 4963340824824138744702115)
                ·
                  refine ⟨7445011237236208117053173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963340824824138744702115 7445011237236208117053173)
                  ·
                    refine ⟨697969803490894510973735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7445011237236208117053173 697969803490894510973735)
                    ·
                      rfl

theorem cell23_4077874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 2, 1, 5].length) (baseStart_4077874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077874 prefixEnd_4077874 := by exact prefixLift 4077874
  have htrace : WordTrace (prefixWord ++ tailWord_4077874) baseStart_4077874 baseEnd_4077874 := by
    simpa [prefixWord, tailWord_4077874, baseEnd_4077874] using wordTrace_append hprefix tailTrace_4077874
  have hstable : (prefixWord ++ tailWord_4077874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077874).length < 2 ^ (prefixWord ++ tailWord_4077874).sum := by decide
  have hdescent : baseEnd_4077874 < baseStart_4077874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077877 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 2, 6, 2]
def baseStart_4077877 : Nat := 118140960795 + 4077877 * 2 ^ 59
def prefixEnd_4077877 : Nat := 4983230072969 + 3 ^ 40 * 4077877 * 2
def baseEnd_4077877 : Nat := 2093910950914647021183691

theorem tailTrace_4077877 : CollatzResearch.WordTrace tailWord_4077877 prefixEnd_4077877 2093910950914647021183691 := by
  unfold tailWord_4077877
  simp only [CollatzResearch.WordTrace]
  refine ⟨148732393047555549789815885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99154928698370366526543923 148732393047555549789815885)
  ·
    refine ⟨55774647392833331171180957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148732393047555549789815885 55774647392833331171180957)
    ·
      refine ⟨20915492772312499189192859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55774647392833331171180957 20915492772312499189192859)
      ·
        refine ⟨31373239158468748783789289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20915492772312499189192859 31373239158468748783789289)
        ·
          refine ⟨23529929368851561587841967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31373239158468748783789289 23529929368851561587841967)
          ·
            refine ⟨35294894053277342381762951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23529929368851561587841967 35294894053277342381762951)
            ·
              refine ⟨52942341079916013572644427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35294894053277342381762951 52942341079916013572644427)
              ·
                refine ⟨79413511619874020358966641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52942341079916013572644427 79413511619874020358966641)
                ·
                  refine ⟨59560133714905515269224981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 79413511619874020358966641 59560133714905515269224981)
                  ·
                    refine ⟨2791881267886196028244921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 59560133714905515269224981 2791881267886196028244921)
                    ·
                      refine ⟨2093910950914647021183691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791881267886196028244921 2093910950914647021183691)
                      ·
                        rfl

theorem cell23_4077877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_4077877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077877 prefixEnd_4077877 := by exact prefixLift 4077877
  have htrace : WordTrace (prefixWord ++ tailWord_4077877) baseStart_4077877 baseEnd_4077877 := by
    simpa [prefixWord, tailWord_4077877, baseEnd_4077877] using wordTrace_append hprefix tailTrace_4077877
  have hstable : (prefixWord ++ tailWord_4077877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077877).length < 2 ^ (prefixWord ++ tailWord_4077877).sum := by decide
  have hdescent : baseEnd_4077877 < baseStart_4077877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077961 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 3]
def baseStart_4077961 : Nat := 118140960795 + 4077961 * 2 ^ 59
def prefixEnd_4077961 : Nat := 4983230072969 + 3 ^ 40 * 4077961 * 2
def baseEnd_4077961 : Nat := 2093954083289624692533305

theorem tailTrace_4077961 : CollatzResearch.WordTrace tailWord_4077961 prefixEnd_4077961 2093954083289624692533305 := by
  unfold tailWord_4077961
  simp only [CollatzResearch.WordTrace]
  refine ⟨148735456779251232135873737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99156971186167488090582491 148735456779251232135873737)
  ·
    refine ⟨111551592584438424101905303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148735456779251232135873737 111551592584438424101905303)
    ·
      refine ⟨167327388876657636152857955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111551592584438424101905303 167327388876657636152857955)
      ·
        refine ⟨250991083314986454229286933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167327388876657636152857955 250991083314986454229286933)
        ·
          refine ⟨11765207030389990041997825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 250991083314986454229286933 11765207030389990041997825)
          ·
            refine ⟨8823905272792492531498369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11765207030389990041997825 8823905272792492531498369)
            ·
              refine ⟨6617928954594369398623777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8823905272792492531498369 6617928954594369398623777)
              ·
                refine ⟨4963446715945777048967833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6617928954594369398623777 4963446715945777048967833)
                ·
                  refine ⟨3722585036959332786725875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963446715945777048967833 3722585036959332786725875)
                  ·
                    refine ⟨5583877555438999180088813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3722585036959332786725875 5583877555438999180088813)
                    ·
                      refine ⟨2093954083289624692533305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5583877555438999180088813 2093954083289624692533305)
                      ·
                        rfl

theorem cell23_4077961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 3].length) (baseStart_4077961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077961 prefixEnd_4077961 := by exact prefixLift 4077961
  have htrace : WordTrace (prefixWord ++ tailWord_4077961) baseStart_4077961 baseEnd_4077961 := by
    simpa [prefixWord, tailWord_4077961, baseEnd_4077961] using wordTrace_append hprefix tailTrace_4077961
  have hstable : (prefixWord ++ tailWord_4077961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077961).length < 2 ^ (prefixWord ++ tailWord_4077961).sum := by decide
  have hdescent : baseEnd_4077961 < baseStart_4077961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4077984 : List Nat := [2, 1, 1, 4, 1, 3, 1, 3, 1, 4, 2]
def baseStart_4077984 : Nat := 118140960795 + 4077984 * 2 ^ 59
def prefixEnd_4077984 : Nat := 4983230072969 + 3 ^ 40 * 4077984 * 2
def baseEnd_4077984 : Nat := 2093965893344678102545699

theorem tailTrace_4077984 : CollatzResearch.WordTrace tailWord_4077984 prefixEnd_4077984 2093965893344678102545699 := by
  unfold tailWord_4077984
  simp only [CollatzResearch.WordTrace]
  refine ⟨74368147829083953531980503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99157530438778604709307337 74368147829083953531980503)
  ·
    refine ⟨111552221743625930297970755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74368147829083953531980503 111552221743625930297970755)
    ·
      refine ⟨167328332615438895446956133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111552221743625930297970755 167328332615438895446956133)
      ·
        refine ⟨31374062365394792896304275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 167328332615438895446956133 31374062365394792896304275)
        ·
          refine ⟨47061093548092189344456413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31374062365394792896304275 47061093548092189344456413)
          ·
            refine ⟨17647910080534571004171155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47061093548092189344456413 17647910080534571004171155)
            ·
              refine ⟨26471865120801856506256733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17647910080534571004171155 26471865120801856506256733)
              ·
                refine ⟨9926949420300696189846275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26471865120801856506256733 9926949420300696189846275)
                ·
                  refine ⟨14890424130451044284769413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9926949420300696189846275 14890424130451044284769413)
                  ·
                    refine ⟨2791954524459570803394265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14890424130451044284769413 2791954524459570803394265)
                    ·
                      refine ⟨2093965893344678102545699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791954524459570803394265 2093965893344678102545699)
                      ·
                        rfl

theorem cell23_4077984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_4077984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4077984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4077984 prefixEnd_4077984 := by exact prefixLift 4077984
  have htrace : WordTrace (prefixWord ++ tailWord_4077984) baseStart_4077984 baseEnd_4077984 := by
    simpa [prefixWord, tailWord_4077984, baseEnd_4077984] using wordTrace_append hprefix tailTrace_4077984
  have hstable : (prefixWord ++ tailWord_4077984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4077984).length < 2 ^ (prefixWord ++ tailWord_4077984).sum := by decide
  have hdescent : baseEnd_4077984 < baseStart_4077984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4077984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078005 : List Nat := [1, 3, 3, 2, 3, 2, 2, 1, 1, 3, 2]
def baseStart_4078005 : Nat := 118140960795 + 4078005 * 2 ^ 59
def prefixEnd_4078005 : Nat := 4983230072969 + 3 ^ 40 * 4078005 * 2
def baseEnd_4078005 : Nat := 2093976676438422520383103

theorem tailTrace_4078005 : CollatzResearch.WordTrace tailWord_4078005 prefixEnd_4078005 2093976676438422520383103 := by
  unfold tailWord_4078005
  simp only [CollatzResearch.WordTrace]
  refine ⟨148737061591091827650475469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99158041060727885100316979 148737061591091827650475469)
  ·
    refine ⟨55776398096659435368928301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148737061591091827650475469 55776398096659435368928301)
    ·
      refine ⟨20916149286247288263348113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55776398096659435368928301 20916149286247288263348113)
      ·
        refine ⟨15687111964685466197511085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20916149286247288263348113 15687111964685466197511085)
        ·
          refine ⟨5882666986757049824066657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15687111964685466197511085 5882666986757049824066657)
          ·
            refine ⟨4412000240067787368049993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5882666986757049824066657 4412000240067787368049993)
            ·
              refine ⟨3309000180050840526037495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4412000240067787368049993 3309000180050840526037495)
              ·
                refine ⟨4963500270076260789056243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309000180050840526037495 4963500270076260789056243)
                ·
                  refine ⟨7445250405114391183584365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4963500270076260789056243 7445250405114391183584365)
                  ·
                    refine ⟨2791968901917896693844137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7445250405114391183584365 2791968901917896693844137)
                    ·
                      refine ⟨2093976676438422520383103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2791968901917896693844137 2093976676438422520383103)
                      ·
                        rfl

theorem cell23_4078005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_4078005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078005 prefixEnd_4078005 := by exact prefixLift 4078005
  have htrace : WordTrace (prefixWord ++ tailWord_4078005) baseStart_4078005 baseEnd_4078005 := by
    simpa [prefixWord, tailWord_4078005, baseEnd_4078005] using wordTrace_append hprefix tailTrace_4078005
  have hstable : (prefixWord ++ tailWord_4078005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078005).length < 2 ^ (prefixWord ++ tailWord_4078005).sum := by decide
  have hdescent : baseEnd_4078005 < baseStart_4078005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078024 : List Nat := [2, 1, 3, 1, 3, 2, 2, 4, 5]
def baseStart_4078024 : Nat := 118140960795 + 4078024 * 2 ^ 59
def prefixEnd_4078024 : Nat := 4983230072969 + 3 ^ 40 * 4078024 * 2
def baseEnd_4078024 : Nat := 232665159174539771782835

theorem tailTrace_4078024 : CollatzResearch.WordTrace tailWord_4078024 prefixEnd_4078024 232665159174539771782835 := by
  unfold tailWord_4078024
  simp only [CollatzResearch.WordTrace]
  refine ⟨74368877289011496947708563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99158503052015329263611417 74368877289011496947708563)
  ·
    refine ⟨111553315933517245421562845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74368877289011496947708563 111553315933517245421562845)
    ·
      refine ⟨41832493475068967033086067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111553315933517245421562845 41832493475068967033086067)
      ·
        refine ⟨62748740212603450549629101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41832493475068967033086067 62748740212603450549629101)
        ·
          refine ⟨23530777579726293956110913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62748740212603450549629101 23530777579726293956110913)
          ·
            refine ⟨17648083184794720467083185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23530777579726293956110913 17648083184794720467083185)
            ·
              refine ⟨13236062388596040350312389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17648083184794720467083185 13236062388596040350312389)
              ·
                refine ⟨2481761697861757565683573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13236062388596040350312389 2481761697861757565683573)
                ·
                  refine ⟨232665159174539771782835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2481761697861757565683573 232665159174539771782835)
                  ·
                    rfl

theorem cell23_4078024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 4, 5].length) (baseStart_4078024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078024 prefixEnd_4078024 := by exact prefixLift 4078024
  have htrace : WordTrace (prefixWord ++ tailWord_4078024) baseStart_4078024 baseEnd_4078024 := by
    simpa [prefixWord, tailWord_4078024, baseEnd_4078024] using wordTrace_append hprefix tailTrace_4078024
  have hstable : (prefixWord ++ tailWord_4078024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078024).length < 2 ^ (prefixWord ++ tailWord_4078024).sum := by decide
  have hdescent : baseEnd_4078024 < baseStart_4078024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078037 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 1, 7]
def baseStart_4078037 : Nat := 118140960795 + 4078037 * 2 ^ 59
def prefixEnd_4078037 : Nat := 4983230072969 + 3 ^ 40 * 4078037 * 2
def baseEnd_4078037 : Nat := 697997702606455465060985

theorem tailTrace_4078037 : CollatzResearch.WordTrace tailWord_4078037 prefixEnd_4078037 697997702606455465060985 := by
  unfold tailWord_4078037
  simp only [CollatzResearch.WordTrace]
  refine ⟨148738228726975897115640365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99158819151317264743760243 148738228726975897115640365)
  ·
    refine ⟨55776835772615961418365137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148738228726975897115640365 55776835772615961418365137)
    ·
      refine ⟨41832626829461971063773853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55776835772615961418365137 41832626829461971063773853)
      ·
        refine ⟨15687235061048239148915195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41832626829461971063773853 15687235061048239148915195)
        ·
          refine ⟨23530852591572358723372793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15687235061048239148915195 23530852591572358723372793)
          ·
            refine ⟨17648139443679269042529595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23530852591572358723372793 17648139443679269042529595)
            ·
              refine ⟨26472209165518903563794393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17648139443679269042529595 26472209165518903563794393)
              ·
                refine ⟨19854156874139177672845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26472209165518903563794393 19854156874139177672845795)
                ·
                  refine ⟨29781235311208766509268693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19854156874139177672845795 29781235311208766509268693)
                  ·
                    refine ⟨697997702606455465060985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29781235311208766509268693 697997702606455465060985)
                    ·
                      rfl

theorem cell23_4078037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 1, 7].length) (baseStart_4078037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078037 prefixEnd_4078037 := by exact prefixLift 4078037
  have htrace : WordTrace (prefixWord ++ tailWord_4078037) baseStart_4078037 baseEnd_4078037 := by
    simpa [prefixWord, tailWord_4078037, baseEnd_4078037] using wordTrace_append hprefix tailTrace_4078037
  have hstable : (prefixWord ++ tailWord_4078037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078037).length < 2 ^ (prefixWord ++ tailWord_4078037).sum := by decide
  have hdescent : baseEnd_4078037 < baseStart_4078037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078074 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2]
def baseStart_4078074 : Nat := 118140960795 + 4078074 * 2 ^ 59
def prefixEnd_4078074 : Nat := 4983230072969 + 3 ^ 40 * 4078074 * 2
def baseEnd_4078074 : Nat := 2094012106603582750420285

theorem tailTrace_4078074 : CollatzResearch.WordTrace tailWord_4078074 prefixEnd_4078074 2094012106603582750420285 := by
  unfold tailWord_4078074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37184894556960463108684319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99159718818561234956491517 37184894556960463108684319)
  ·
    refine ⟨55777341835440694663026479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37184894556960463108684319 55777341835440694663026479)
    ·
      refine ⟨83666012753161041994539719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55777341835440694663026479 83666012753161041994539719)
      ·
        refine ⟨125499019129741562991809579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83666012753161041994539719 125499019129741562991809579)
        ·
          refine ⟨188248528694612344487714369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125499019129741562991809579 188248528694612344487714369)
          ·
            refine ⟨141186396520959258365785777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188248528694612344487714369 141186396520959258365785777)
            ·
              refine ⟨105889797390719443774339333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141186396520959258365785777 105889797390719443774339333)
              ·
                refine ⟨19854337010759895707688625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105889797390719443774339333 19854337010759895707688625)
                ·
                  refine ⟨14890752758069921780766469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19854337010759895707688625 14890752758069921780766469)
                  ·
                    refine ⟨2792016142138110333893713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14890752758069921780766469 2792016142138110333893713)
                    ·
                      refine ⟨2094012106603582750420285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792016142138110333893713 2094012106603582750420285)
                      ·
                        rfl

theorem cell23_4078074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 2, 4, 2].length) (baseStart_4078074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078074 prefixEnd_4078074 := by exact prefixLift 4078074
  have htrace : WordTrace (prefixWord ++ tailWord_4078074) baseStart_4078074 baseEnd_4078074 := by
    simpa [prefixWord, tailWord_4078074, baseEnd_4078074] using wordTrace_append hprefix tailTrace_4078074
  have hstable : (prefixWord ++ tailWord_4078074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078074).length < 2 ^ (prefixWord ++ tailWord_4078074).sum := by decide
  have hdescent : baseEnd_4078074 < baseStart_4078074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078086 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_4078086 : Nat := 118140960795 + 4078086 * 2 ^ 59
def prefixEnd_4078086 : Nat := 4983230072969 + 3 ^ 40 * 4078086 * 2
def baseEnd_4078086 : Nat := 2094018268371436703470231

theorem tailTrace_4078086 : CollatzResearch.WordTrace tailWord_4078086 prefixEnd_4078086 2094018268371436703470231 := by
  unfold tailWord_4078086
  simp only [CollatzResearch.WordTrace]
  refine ⟨4648125496993699327630441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99160010602532252322782741 4648125496993699327630441)
  ·
    refine ⟨3486094122745274495722831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4648125496993699327630441 3486094122745274495722831)
    ·
      refine ⟨5229141184117911743584247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486094122745274495722831 5229141184117911743584247)
      ·
        refine ⟨7843711776176867615376371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5229141184117911743584247 7843711776176867615376371)
        ·
          refine ⟨11765567664265301423064557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7843711776176867615376371 11765567664265301423064557)
          ·
            refine ⟨4412087874099488033649209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11765567664265301423064557 4412087874099488033649209)
            ·
              refine ⟨3309065905574616025236907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4412087874099488033649209 3309065905574616025236907)
              ·
                refine ⟨4963598858361924037855361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309065905574616025236907 4963598858361924037855361)
                ·
                  refine ⟨3722699143771443028391521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963598858361924037855361 3722699143771443028391521)
                  ·
                    refine ⟨2792024357828582271293641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3722699143771443028391521 2792024357828582271293641)
                    ·
                      refine ⟨2094018268371436703470231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792024357828582271293641 2094018268371436703470231)
                      ·
                        rfl

theorem cell23_4078086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_4078086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078086 prefixEnd_4078086 := by exact prefixLift 4078086
  have htrace : WordTrace (prefixWord ++ tailWord_4078086) baseStart_4078086 baseEnd_4078086 := by
    simpa [prefixWord, tailWord_4078086, baseEnd_4078086] using wordTrace_append hprefix tailTrace_4078086
  have hstable : (prefixWord ++ tailWord_4078086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078086).length < 2 ^ (prefixWord ++ tailWord_4078086).sum := by decide
  have hdescent : baseEnd_4078086 < baseStart_4078086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078191 : List Nat := [1, 1, 2, 1, 3, 2, 5, 2, 2, 4]
def baseStart_4078191 : Nat := 118140960795 + 4078191 * 2 ^ 59
def prefixEnd_4078191 : Nat := 4983230072969 + 3 ^ 40 * 4078191 * 2
def baseEnd_4078191 : Nat := 698024061280052930885749

theorem tailTrace_4078191 : CollatzResearch.WordTrace tailWord_4078191 prefixEnd_4078191 698024061280052930885749 := by
  unfold tailWord_4078191
  simp only [CollatzResearch.WordTrace]
  refine ⟨148743845568417981416746427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99162563712278654277830951 148743845568417981416746427)
  ·
    refine ⟨223115768352626972125119641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148743845568417981416746427 223115768352626972125119641)
    ·
      refine ⟨167336826264470229093839731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223115768352626972125119641 167336826264470229093839731)
      ·
        refine ⟨251005239396705343640759597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167336826264470229093839731 251005239396705343640759597)
        ·
          refine ⟨94126964773764503865284849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 251005239396705343640759597 94126964773764503865284849)
          ·
            refine ⟨70595223580323377898963637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94126964773764503865284849 70595223580323377898963637)
            ·
              refine ⟨6618302210655316678027841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70595223580323377898963637 6618302210655316678027841)
              ·
                refine ⟨4963726657991487508520881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6618302210655316678027841 4963726657991487508520881)
                ·
                  refine ⟨3722794993493615631390661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963726657991487508520881 3722794993493615631390661)
                  ·
                    refine ⟨698024061280052930885749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3722794993493615631390661 698024061280052930885749)
                    ·
                      rfl

theorem cell23_4078191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 2, 2, 4].length) (baseStart_4078191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078191 prefixEnd_4078191 := by exact prefixLift 4078191
  have htrace : WordTrace (prefixWord ++ tailWord_4078191) baseStart_4078191 baseEnd_4078191 := by
    simpa [prefixWord, tailWord_4078191, baseEnd_4078191] using wordTrace_append hprefix tailTrace_4078191
  have hstable : (prefixWord ++ tailWord_4078191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078191).length < 2 ^ (prefixWord ++ tailWord_4078191).sum := by decide
  have hdescent : baseEnd_4078191 < baseStart_4078191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078207 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 6]
def baseStart_4078207 : Nat := 118140960795 + 4078207 * 2 ^ 59
def prefixEnd_4078207 : Nat := 4983230072969 + 3 ^ 40 * 4078207 * 2
def baseEnd_4078207 : Nat := 2094080399530630730057173

theorem tailTrace_4078207 : CollatzResearch.WordTrace tailWord_4078207 prefixEnd_4078207 2094080399530630730057173 := by
  unfold tailWord_4078207
  simp only [CollatzResearch.WordTrace]
  refine ⟨148744429136360016149328875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99162952757573344099552583 148744429136360016149328875)
  ·
    refine ⟨223116643704540024223993313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148744429136360016149328875 223116643704540024223993313)
    ·
      refine ⟨167337482778405018167994985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223116643704540024223993313 167337482778405018167994985)
      ·
        refine ⟨125503112083803763625996239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167337482778405018167994985 125503112083803763625996239)
        ·
          refine ⟨188254668125705645438994359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125503112083803763625996239 188254668125705645438994359)
          ·
            refine ⟨282382002188558468158491539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188254668125705645438994359 282382002188558468158491539)
            ·
              refine ⟨423573003282837702237737309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282382002188558468158491539 423573003282837702237737309)
              ·
                refine ⟨158839876231064138339151491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423573003282837702237737309 158839876231064138339151491)
                ·
                  refine ⟨238259814346596207508727237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158839876231064138339151491 238259814346596207508727237)
                  ·
                    refine ⟨44673715189986788907886357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 238259814346596207508727237 44673715189986788907886357)
                    ·
                      refine ⟨2094080399530630730057173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44673715189986788907886357 2094080399530630730057173)
                      ·
                        rfl

theorem cell23_4078207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 6].length) (baseStart_4078207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078207 prefixEnd_4078207 := by exact prefixLift 4078207
  have htrace : WordTrace (prefixWord ++ tailWord_4078207) baseStart_4078207 baseEnd_4078207 := by
    simpa [prefixWord, tailWord_4078207, baseEnd_4078207] using wordTrace_append hprefix tailTrace_4078207
  have hstable : (prefixWord ++ tailWord_4078207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078207).length < 2 ^ (prefixWord ++ tailWord_4078207).sum := by decide
  have hdescent : baseEnd_4078207 < baseStart_4078207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078208 : List Nat := [2, 1, 1, 2, 1, 6, 3, 1, 2, 4]
def baseStart_4078208 : Nat := 118140960795 + 4078208 * 2 ^ 59
def prefixEnd_4078208 : Nat := 4983230072969 + 3 ^ 40 * 4078208 * 2
def baseEnd_4078208 : Nat := 698026971003761742048223

theorem tailTrace_4078208 : CollatzResearch.WordTrace tailWord_4078208 prefixEnd_4078208 698026971003761742048223 := by
  unfold tailWord_4078208
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372232804678196660057639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99162977072904262213410185 74372232804678196660057639)
  ·
    refine ⟨111558349207017294990086459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74372232804678196660057639 111558349207017294990086459)
    ·
      refine ⟨167337523810525942485129689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111558349207017294990086459 167337523810525942485129689)
      ·
        refine ⟨125503142857894456863847267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167337523810525942485129689 125503142857894456863847267)
        ·
          refine ⟨188254714286841685295770901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125503142857894456863847267 188254714286841685295770901)
          ·
            refine ⟨8824439732195703998239261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 188254714286841685295770901 8824439732195703998239261)
            ·
              refine ⟨3309164899573388999339723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8824439732195703998239261 3309164899573388999339723)
              ·
                refine ⟨4963747349360083499009585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309164899573388999339723 4963747349360083499009585)
                ·
                  refine ⟨3722810512020062624257189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963747349360083499009585 3722810512020062624257189)
                  ·
                    refine ⟨698026971003761742048223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3722810512020062624257189 698026971003761742048223)
                    ·
                      rfl

theorem cell23_4078208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 3, 1, 2, 4].length) (baseStart_4078208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078208 prefixEnd_4078208 := by exact prefixLift 4078208
  have htrace : WordTrace (prefixWord ++ tailWord_4078208) baseStart_4078208 baseEnd_4078208 := by
    simpa [prefixWord, tailWord_4078208, baseEnd_4078208] using wordTrace_append hprefix tailTrace_4078208
  have hstable : (prefixWord ++ tailWord_4078208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078208).length < 2 ^ (prefixWord ++ tailWord_4078208).sum := by decide
  have hdescent : baseEnd_4078208 < baseStart_4078208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078231 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 3]
def baseStart_4078231 : Nat := 118140960795 + 4078231 * 2 ^ 59
def prefixEnd_4078231 : Nat := 4983230072969 + 3 ^ 40 * 4078231 * 2
def baseEnd_4078231 : Nat := 2094092723066338636157063

theorem tailTrace_4078231 : CollatzResearch.WordTrace tailWord_4078231 prefixEnd_4078231 2094092723066338636157063 := by
  unfold tailWord_4078231
  simp only [CollatzResearch.WordTrace]
  refine ⟨148745304488273068248202547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99163536325515378832135031 148745304488273068248202547)
  ·
    refine ⟨223117956732409602372303821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148745304488273068248202547 223117956732409602372303821)
    ·
      refine ⟨83669233774653600889613933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223117956732409602372303821 83669233774653600889613933)
      ·
        refine ⟨31375962665495100333605225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83669233774653600889613933 31375962665495100333605225)
        ·
          refine ⟨23531971999121325250203919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31375962665495100333605225 23531971999121325250203919)
          ·
            refine ⟨35297957998681987875305879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23531971999121325250203919 35297957998681987875305879)
            ·
              refine ⟨52946936998022981812958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35297957998681987875305879 52946936998022981812958819)
              ·
                refine ⟨79420405497034472719438229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52946936998022981812958819 79420405497034472719438229)
                ·
                  refine ⟨3722831507673490908723667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79420405497034472719438229 3722831507673490908723667)
                  ·
                    refine ⟨5584247261510236363085501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3722831507673490908723667 5584247261510236363085501)
                    ·
                      refine ⟨2094092723066338636157063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5584247261510236363085501 2094092723066338636157063)
                      ·
                        rfl

theorem cell23_4078231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_4078231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078231 prefixEnd_4078231 := by exact prefixLift 4078231
  have htrace : WordTrace (prefixWord ++ tailWord_4078231) baseStart_4078231 baseEnd_4078231 := by
    simpa [prefixWord, tailWord_4078231, baseEnd_4078231] using wordTrace_append hprefix tailTrace_4078231
  have hstable : (prefixWord ++ tailWord_4078231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078231).length < 2 ^ (prefixWord ++ tailWord_4078231).sum := by decide
  have hdescent : baseEnd_4078231 < baseStart_4078231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078244 : List Nat := [2, 3, 1, 2, 2, 1, 1, 2, 2, 2, 5]
def baseStart_4078244 : Nat := 118140960795 + 4078244 * 2 ^ 59
def prefixEnd_4078244 : Nat := 4983230072969 + 3 ^ 40 * 4078244 * 2
def baseEnd_4078244 : Nat := 2094099398314847085294503

theorem tailTrace_4078244 : CollatzResearch.WordTrace tailWord_4078244 prefixEnd_4078244 2094099398314847085294503 := by
  unfold tailWord_4078244
  simp only [CollatzResearch.WordTrace]
  refine ⟨74372889318612985734212893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99163852424817314312283857 74372889318612985734212893)
  ·
    refine ⟨27889833494479869650329835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74372889318612985734212893 27889833494479869650329835)
    ·
      refine ⟨41834750241719804475494753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27889833494479869650329835 41834750241719804475494753)
      ·
        refine ⟨31376062681289853356621065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41834750241719804475494753 31376062681289853356621065)
        ·
          refine ⟨23532047010967390017465799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31376062681289853356621065 23532047010967390017465799)
          ·
            refine ⟨35298070516451085026198699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23532047010967390017465799 35298070516451085026198699)
            ·
              refine ⟨52947105774676627539298049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35298070516451085026198699 52947105774676627539298049)
              ·
                refine ⟨39710329331007470654473537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52947105774676627539298049 39710329331007470654473537)
                ·
                  refine ⟨29782746998255602990855153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39710329331007470654473537 29782746998255602990855153)
                  ·
                    refine ⟨22337060248691702243141365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29782746998255602990855153 22337060248691702243141365)
                    ·
                      refine ⟨2094099398314847085294503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22337060248691702243141365 2094099398314847085294503)
                      ·
                        rfl

theorem cell23_4078244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_4078244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078244 prefixEnd_4078244 := by exact prefixLift 4078244
  have htrace : WordTrace (prefixWord ++ tailWord_4078244) baseStart_4078244 baseEnd_4078244 := by
    simpa [prefixWord, tailWord_4078244, baseEnd_4078244] using wordTrace_append hprefix tailTrace_4078244
  have hstable : (prefixWord ++ tailWord_4078244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078244).length < 2 ^ (prefixWord ++ tailWord_4078244).sum := by decide
  have hdescent : baseEnd_4078244 < baseStart_4078244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078305 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 2, 2, 2]
def baseStart_4078305 : Nat := 118140960795 + 4078305 * 2 ^ 59
def prefixEnd_4078305 : Nat := 4983230072969 + 3 ^ 40 * 4078305 * 2
def baseEnd_4078305 : Nat := 2094130720634771346631723

theorem tailTrace_4078305 : CollatzResearch.WordTrace tailWord_4078305 prefixEnd_4078305 2094130720634771346631723 := by
  unfold tailWord_4078305
  simp only [CollatzResearch.WordTrace]
  refine ⟨148748003490004978886396369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99165335660003319257597579 148748003490004978886396369)
  ·
    refine ⟨111561002617503734164797277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148748003490004978886396369 111561002617503734164797277)
    ·
      refine ⟨41835375981563900311798979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111561002617503734164797277 41835375981563900311798979)
      ·
        refine ⟨62753063972345850467698469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41835375981563900311798979 62753063972345850467698469)
        ·
          refine ⟨11766199494814846962693463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62753063972345850467698469 11766199494814846962693463)
          ·
            refine ⟨17649299242222270444040195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766199494814846962693463 17649299242222270444040195)
            ·
              refine ⟨26473948863333405666060293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17649299242222270444040195 26473948863333405666060293)
              ·
                refine ⟨4963865411875013562386305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26473948863333405666060293 4963865411875013562386305)
                ·
                  refine ⟨3722899058906260171789729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4963865411875013562386305 3722899058906260171789729)
                  ·
                    refine ⟨2792174294179695128842297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3722899058906260171789729 2792174294179695128842297)
                    ·
                      refine ⟨2094130720634771346631723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792174294179695128842297 2094130720634771346631723)
                      ·
                        rfl

theorem cell23_4078305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 2, 2, 2].length) (baseStart_4078305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078305 prefixEnd_4078305 := by exact prefixLift 4078305
  have htrace : WordTrace (prefixWord ++ tailWord_4078305) baseStart_4078305 baseEnd_4078305 := by
    simpa [prefixWord, tailWord_4078305, baseEnd_4078305] using wordTrace_append hprefix tailTrace_4078305
  have hstable : (prefixWord ++ tailWord_4078305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078305).length < 2 ^ (prefixWord ++ tailWord_4078305).sum := by decide
  have hdescent : baseEnd_4078305 < baseStart_4078305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078314 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_4078314 : Nat := 118140960795 + 4078314 * 2 ^ 59
def prefixEnd_4078314 : Nat := 4983230072969 + 3 ^ 40 * 4078314 * 2
def baseEnd_4078314 : Nat := 2094135341960661811419181

theorem tailTrace_4078314 : CollatzResearch.WordTrace tailWord_4078314 prefixEnd_4078314 2094135341960661811419181 := by
  unfold tailWord_4078314
  simp only [CollatzResearch.WordTrace]
  refine ⟨37187082936743093355868499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99165554497981582282315997 37187082936743093355868499)
  ·
    refine ⟨55780624405114640033802749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37187082936743093355868499 55780624405114640033802749)
    ·
      refine ⟨20917734151917990012676031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55780624405114640033802749 20917734151917990012676031)
      ·
        refine ⟨31376601227876985019014047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20917734151917990012676031 31376601227876985019014047)
        ·
          refine ⟨47064901841815477528521071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31376601227876985019014047 47064901841815477528521071)
          ·
            refine ⟨70597352762723216292781607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47064901841815477528521071 70597352762723216292781607)
            ·
              refine ⟨105896029144084824439172411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70597352762723216292781607 105896029144084824439172411)
              ·
                refine ⟨158844043716127236658758617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105896029144084824439172411 158844043716127236658758617)
                ·
                  refine ⟨119133032787095427494068963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158844043716127236658758617 119133032787095427494068963)
                  ·
                    refine ⟨178699549180643141241103445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 119133032787095427494068963 178699549180643141241103445)
                    ·
                      refine ⟨2094135341960661811419181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 178699549180643141241103445 2094135341960661811419181)
                      ·
                        rfl

theorem cell23_4078314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_4078314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078314 prefixEnd_4078314 := by exact prefixLift 4078314
  have htrace : WordTrace (prefixWord ++ tailWord_4078314) baseStart_4078314 baseEnd_4078314 := by
    simpa [prefixWord, tailWord_4078314, baseEnd_4078314] using wordTrace_append hprefix tailTrace_4078314
  have hstable : (prefixWord ++ tailWord_4078314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078314).length < 2 ^ (prefixWord ++ tailWord_4078314).sum := by decide
  have hdescent : baseEnd_4078314 < baseStart_4078314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078321 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 3]
def baseStart_4078321 : Nat := 118140960795 + 4078321 * 2 ^ 59
def prefixEnd_4078321 : Nat := 4983230072969 + 3 ^ 40 * 4078321 * 2
def baseEnd_4078321 : Nat := 2094138936325243284031649

theorem tailTrace_4078321 : CollatzResearch.WordTrace tailWord_4078321 prefixEnd_4078321 2094138936325243284031649 := by
  unfold tailWord_4078321
  simp only [CollatzResearch.WordTrace]
  refine ⟨148748587057947013618978817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99165724705298009079319211 148748587057947013618978817)
  ·
    refine ⟨111561440293460260214234113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148748587057947013618978817 111561440293460260214234113)
    ·
      refine ⟨83671080220095195160675585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111561440293460260214234113 83671080220095195160675585)
      ·
        refine ⟨62753310165071396370506689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83671080220095195160675585 62753310165071396370506689)
        ·
          refine ⟨47064982623803547277880017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62753310165071396370506689 47064982623803547277880017)
          ·
            refine ⟨35298736967852660458410013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47064982623803547277880017 35298736967852660458410013)
            ·
              refine ⟨13237026362944747671903755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35298736967852660458410013 13237026362944747671903755)
              ·
                refine ⟨19855539544417121507855633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13237026362944747671903755 19855539544417121507855633)
                ·
                  refine ⟨14891654658312841130891725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19855539544417121507855633 14891654658312841130891725)
                  ·
                    refine ⟨5584370496867315424084397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14891654658312841130891725 5584370496867315424084397)
                    ·
                      refine ⟨2094138936325243284031649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5584370496867315424084397 2094138936325243284031649)
                      ·
                        rfl

theorem cell23_4078321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_4078321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078321 prefixEnd_4078321 := by exact prefixLift 4078321
  have htrace : WordTrace (prefixWord ++ tailWord_4078321) baseStart_4078321 baseEnd_4078321 := by
    simpa [prefixWord, tailWord_4078321, baseEnd_4078321] using wordTrace_append hprefix tailTrace_4078321
  have hstable : (prefixWord ++ tailWord_4078321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078321).length < 2 ^ (prefixWord ++ tailWord_4078321).sum := by decide
  have hdescent : baseEnd_4078321 < baseStart_4078321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078431 : List Nat := [1, 1, 2, 3, 1, 3, 2, 2, 3, 5]
def baseStart_4078431 : Nat := 118140960795 + 4078431 * 2 ^ 59
def prefixEnd_4078431 : Nat := 4983230072969 + 3 ^ 40 * 4078431 * 2
def baseEnd_4078431 : Nat := 698065139732412617885381

theorem tailTrace_4078431 : CollatzResearch.WordTrace tailWord_4078431 prefixEnd_4078431 698065139732412617885381 := by
  unfold tailWord_4078431
  simp only [CollatzResearch.WordTrace]
  refine ⟨148752599087548502405483147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99168399391699001603655431 148752599087548502405483147)
  ·
    refine ⟨223128898631322753608224721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148752599087548502405483147 223128898631322753608224721)
    ·
      refine ⟨167346673973492065206168541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223128898631322753608224721 167346673973492065206168541)
      ·
        refine ⟨62755002740059524452313203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167346673973492065206168541 62755002740059524452313203)
        ·
          refine ⟨94132504110089286678469805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62755002740059524452313203 94132504110089286678469805)
          ·
            refine ⟨35299689041283482504426177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 94132504110089286678469805 35299689041283482504426177)
            ·
              refine ⟨26474766780962611878319633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35299689041283482504426177 26474766780962611878319633)
              ·
                refine ⟨19856075085721958908739725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26474766780962611878319633 19856075085721958908739725)
                ·
                  refine ⟨7446028157145734590777397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19856075085721958908739725 7446028157145734590777397)
                  ·
                    refine ⟨698065139732412617885381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7446028157145734590777397 698065139732412617885381)
                    ·
                      rfl

theorem cell23_4078431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 2, 3, 5].length) (baseStart_4078431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078431 prefixEnd_4078431 := by exact prefixLift 4078431
  have htrace : WordTrace (prefixWord ++ tailWord_4078431) baseStart_4078431 baseEnd_4078431 := by
    simpa [prefixWord, tailWord_4078431, baseEnd_4078431] using wordTrace_append hprefix tailTrace_4078431
  have hstable : (prefixWord ++ tailWord_4078431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078431).length < 2 ^ (prefixWord ++ tailWord_4078431).sum := by decide
  have hdescent : baseEnd_4078431 < baseStart_4078431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078435 : List Nat := [1, 1, 1, 5, 3, 3, 2, 1, 6]
def baseStart_4078435 : Nat := 118140960795 + 4078435 * 2 ^ 59
def prefixEnd_4078435 : Nat := 4983230072969 + 3 ^ 40 * 4078435 * 2
def baseEnd_4078435 : Nat := 232688608124428426445125

theorem tailTrace_4078435 : CollatzResearch.WordTrace tailWord_4078435 prefixEnd_4078435 232688608124428426445125 := by
  unfold tailWord_4078435
  simp only [CollatzResearch.WordTrace]
  refine ⟨148752744979534011088628759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99168496653022674059085839 148752744979534011088628759)
  ·
    refine ⟨223129117469301016632943139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148752744979534011088628759 223129117469301016632943139)
    ·
      refine ⟨334693676203951524949414709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223129117469301016632943139 334693676203951524949414709)
      ·
        refine ⟨31377532144120455464007629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 334693676203951524949414709 31377532144120455464007629)
        ·
          refine ⟨11766574554045170799002861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31377532144120455464007629 11766574554045170799002861)
          ·
            refine ⟨4412465457766939049626073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11766574554045170799002861 4412465457766939049626073)
            ·
              refine ⟨3309349093325204287219555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4412465457766939049626073 3309349093325204287219555)
              ·
                refine ⟨4964023639987806430829333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3309349093325204287219555 4964023639987806430829333)
                ·
                  refine ⟨232688608124428426445125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4964023639987806430829333 232688608124428426445125)
                  ·
                    rfl

theorem cell23_4078435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 1, 6].length) (baseStart_4078435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078435 prefixEnd_4078435 := by exact prefixLift 4078435
  have htrace : WordTrace (prefixWord ++ tailWord_4078435) baseStart_4078435 baseEnd_4078435 := by
    simpa [prefixWord, tailWord_4078435, baseEnd_4078435] using wordTrace_append hprefix tailTrace_4078435
  have hstable : (prefixWord ++ tailWord_4078435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078435).length < 2 ^ (prefixWord ++ tailWord_4078435).sum := by decide
  have hdescent : baseEnd_4078435 < baseStart_4078435 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078448 : List Nat := [2, 1, 1, 1, 4, 1, 5, 2, 1, 5]
def baseStart_4078448 : Nat := 118140960795 + 4078448 * 2 ^ 59
def prefixEnd_4078448 : Nat := 4983230072969 + 3 ^ 40 * 4078448 * 2
def baseEnd_4078448 : Nat := 698068049456121429047855

theorem tailTrace_4078448 : CollatzResearch.WordTrace tailWord_4078448 prefixEnd_4078448 698068049456121429047855 := by
  unfold tailWord_4078448
  simp only [CollatzResearch.WordTrace]
  refine ⟨74376609564243457154425999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99168812752324609539234665 74376609564243457154425999)
  ·
    refine ⟨111564914346365185731638999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74376609564243457154425999 111564914346365185731638999)
    ·
      refine ⟨167347371519547778597458499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111564914346365185731638999 167347371519547778597458499)
      ·
        refine ⟨251021057279321667896187749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167347371519547778597458499 251021057279321667896187749)
        ·
          refine ⟨47066448239872812730535203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 251021057279321667896187749 47066448239872812730535203)
          ·
            refine ⟨70599672359809219095802805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47066448239872812730535203 70599672359809219095802805)
            ·
              refine ⟨6618719283732114290231513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70599672359809219095802805 6618719283732114290231513)
              ·
                refine ⟨4964039462799085717673635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6618719283732114290231513 4964039462799085717673635)
                ·
                  refine ⟨7446059194198628576510453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964039462799085717673635 7446059194198628576510453)
                  ·
                    refine ⟨698068049456121429047855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7446059194198628576510453 698068049456121429047855)
                    ·
                      rfl

theorem cell23_4078448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 2, 1, 5].length) (baseStart_4078448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078448 prefixEnd_4078448 := by exact prefixLift 4078448
  have htrace : WordTrace (prefixWord ++ tailWord_4078448) baseStart_4078448 baseEnd_4078448 := by
    simpa [prefixWord, tailWord_4078448, baseEnd_4078448] using wordTrace_append hprefix tailTrace_4078448
  have hstable : (prefixWord ++ tailWord_4078448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078448).length < 2 ^ (prefixWord ++ tailWord_4078448).sum := by decide
  have hdescent : baseEnd_4078448 < baseStart_4078448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078461 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 3, 6]
def baseStart_4078461 : Nat := 118140960795 + 4078461 * 2 ^ 59
def prefixEnd_4078461 : Nat := 4983230072969 + 3 ^ 40 * 4078461 * 2
def baseEnd_4078461 : Nat := 698070274538957578760335

theorem tailTrace_4078461 : CollatzResearch.WordTrace tailWord_4078461 prefixEnd_4078461 698070274538957578760335 := by
  unfold tailWord_4078461
  simp only [CollatzResearch.WordTrace]
  refine ⟨148753693277439817529075237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99169128851626545019383491 148753693277439817529075237)
  ·
    refine ⟨27891317489519965786701607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148753693277439817529075237 27891317489519965786701607)
    ·
      refine ⟨41836976234279948680052411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27891317489519965786701607 41836976234279948680052411)
      ·
        refine ⟨62755464351419923020078617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41836976234279948680052411 62755464351419923020078617)
        ·
          refine ⟨47066598263564942265058963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62755464351419923020078617 47066598263564942265058963)
          ·
            refine ⟨70599897395347413397588445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47066598263564942265058963 70599897395347413397588445)
            ·
              refine ⟨26474961523255280024095667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70599897395347413397588445 26474961523255280024095667)
              ·
                refine ⟨39712442284882920036143501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26474961523255280024095667 39712442284882920036143501)
                ·
                  refine ⟨14892165856831095013553813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39712442284882920036143501 14892165856831095013553813)
                  ·
                    refine ⟨698070274538957578760335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14892165856831095013553813 698070274538957578760335)
                    ·
                      rfl

theorem cell23_4078461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 6].length) (baseStart_4078461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078461 prefixEnd_4078461 := by exact prefixLift 4078461
  have htrace : WordTrace (prefixWord ++ tailWord_4078461) baseStart_4078461 baseEnd_4078461 := by
    simpa [prefixWord, tailWord_4078461, baseEnd_4078461] using wordTrace_append hprefix tailTrace_4078461
  have hstable : (prefixWord ++ tailWord_4078461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078461).length < 2 ^ (prefixWord ++ tailWord_4078461).sum := by decide
  have hdescent : baseEnd_4078461 < baseStart_4078461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078481 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 4]
def baseStart_4078481 : Nat := 118140960795 + 4078481 * 2 ^ 59
def prefixEnd_4078481 : Nat := 4983230072969 + 3 ^ 40 * 4078481 * 2
def baseEnd_4078481 : Nat := 2094221093229962658030913

theorem tailTrace_4078481 : CollatzResearch.WordTrace tailWord_4078481 prefixEnd_4078481 2094221093229962658030913 := by
  unfold tailWord_4078481
  simp only [CollatzResearch.WordTrace]
  refine ⟨148754422737367360944803297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99169615158244907296535531 148754422737367360944803297)
  ·
    refine ⟨111565817053025520708602473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148754422737367360944803297 111565817053025520708602473)
    ·
      refine ⟨83674362789769140531451855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111565817053025520708602473 83674362789769140531451855)
      ·
        refine ⟨125511544184653710797177783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83674362789769140531451855 125511544184653710797177783)
        ·
          refine ⟨188267316276980566195766675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125511544184653710797177783 188267316276980566195766675)
          ·
            refine ⟨282400974415470849293650013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188267316276980566195766675 282400974415470849293650013)
            ·
              refine ⟨105900365405801568485118755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282400974415470849293650013 105900365405801568485118755)
              ·
                refine ⟨158850548108702352727678133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105900365405801568485118755 158850548108702352727678133)
                ·
                  refine ⟨14892238885190845568219825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158850548108702352727678133 14892238885190845568219825)
                  ·
                    refine ⟨11169179163893134176164869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14892238885190845568219825 11169179163893134176164869)
                    ·
                      refine ⟨2094221093229962658030913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11169179163893134176164869 2094221093229962658030913)
                      ·
                        rfl

theorem cell23_4078481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_4078481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078481 prefixEnd_4078481 := by exact prefixLift 4078481
  have htrace : WordTrace (prefixWord ++ tailWord_4078481) baseStart_4078481 baseEnd_4078481 := by
    simpa [prefixWord, tailWord_4078481, baseEnd_4078481] using wordTrace_append hprefix tailTrace_4078481
  have hstable : (prefixWord ++ tailWord_4078481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078481).length < 2 ^ (prefixWord ++ tailWord_4078481).sum := by decide
  have hdescent : baseEnd_4078481 < baseStart_4078481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078495 : List Nat := [1, 1, 2, 5, 2, 1, 2, 3, 2, 4]
def baseStart_4078495 : Nat := 118140960795 + 4078495 * 2 ^ 59
def prefixEnd_4078495 : Nat := 4983230072969 + 3 ^ 40 * 4078495 * 2
def baseEnd_4078495 : Nat := 698076093986375201085283

theorem tailTrace_4078495 : CollatzResearch.WordTrace tailWord_4078495 prefixEnd_4078495 698076093986375201085283 := by
  unfold tailWord_4078495
  simp only [CollatzResearch.WordTrace]
  refine ⟨148754933359316641335812939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99169955572877760890541959 148754933359316641335812939)
  ·
    refine ⟨223132400038974962003719409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148754933359316641335812939 223132400038974962003719409)
    ·
      refine ⟨167349300029231221502789557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223132400038974962003719409 167349300029231221502789557)
      ·
        refine ⟨15688996877740427015886521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167349300029231221502789557 15688996877740427015886521)
        ·
          refine ⟨11766747658305320261914891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15688996877740427015886521 11766747658305320261914891)
          ·
            refine ⟨17650121487457980392872337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11766747658305320261914891 17650121487457980392872337)
            ·
              refine ⟨13237591115593485294654253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17650121487457980392872337 13237591115593485294654253)
              ·
                refine ⟨4964096668347556985495345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13237591115593485294654253 4964096668347556985495345)
                ·
                  refine ⟨3723072501260667739121509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4964096668347556985495345 3723072501260667739121509)
                  ·
                    refine ⟨698076093986375201085283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3723072501260667739121509 698076093986375201085283)
                    ·
                      rfl

theorem cell23_4078495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 4].length) (baseStart_4078495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078495 prefixEnd_4078495 := by exact prefixLift 4078495
  have htrace : WordTrace (prefixWord ++ tailWord_4078495) baseStart_4078495 baseEnd_4078495 := by
    simpa [prefixWord, tailWord_4078495, baseEnd_4078495] using wordTrace_append hprefix tailTrace_4078495
  have hstable : (prefixWord ++ tailWord_4078495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078495).length < 2 ^ (prefixWord ++ tailWord_4078495).sum := by decide
  have hdescent : baseEnd_4078495 < baseStart_4078495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078531 : List Nat := [1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5]
def baseStart_4078531 : Nat := 118140960795 + 4078531 * 2 ^ 59
def prefixEnd_4078531 : Nat := 4983230072969 + 3 ^ 40 * 4078531 * 2
def baseEnd_4078531 : Nat := 2094246767262687462405683

theorem tailTrace_4078531 : CollatzResearch.WordTrace tailWord_4078531 prefixEnd_4078531 2094246767262687462405683 := by
  unfold tailWord_4078531
  simp only [CollatzResearch.WordTrace]
  refine ⟨148756246387186219484123447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99170830924790812989415631 148756246387186219484123447)
  ·
    refine ⟨223134369580779329226185171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148756246387186219484123447 223134369580779329226185171)
    ·
      refine ⟨334701554371168993839277757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223134369580779329226185171 334701554371168993839277757)
      ·
        refine ⟨125513082889188372689729159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334701554371168993839277757 125513082889188372689729159)
        ·
          refine ⟨188269624333782559034593739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125513082889188372689729159 188269624333782559034593739)
          ·
            refine ⟨282404436500673838551890609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188269624333782559034593739 282404436500673838551890609)
            ·
              refine ⟨211803327375505378913917957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282404436500673838551890609 211803327375505378913917957)
              ·
                refine ⟨39713123882907258546359617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 211803327375505378913917957 39713123882907258546359617)
                ·
                  refine ⟨29784842912180443909769713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39713123882907258546359617 29784842912180443909769713)
                  ·
                    refine ⟨22338632184135332932327285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29784842912180443909769713 22338632184135332932327285)
                    ·
                      refine ⟨2094246767262687462405683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22338632184135332932327285 2094246767262687462405683)
                      ·
                        rfl

theorem cell23_4078531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_4078531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078531 prefixEnd_4078531 := by exact prefixLift 4078531
  have htrace : WordTrace (prefixWord ++ tailWord_4078531) baseStart_4078531 baseEnd_4078531 := by
    simpa [prefixWord, tailWord_4078531, baseEnd_4078531] using wordTrace_append hprefix tailTrace_4078531
  have hstable : (prefixWord ++ tailWord_4078531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078531).length < 2 ^ (prefixWord ++ tailWord_4078531).sum := by decide
  have hdescent : baseEnd_4078531 < baseStart_4078531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078551 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 1, 8]
def baseStart_4078551 : Nat := 118140960795 + 4078551 * 2 ^ 59
def prefixEnd_4078551 : Nat := 4983230072969 + 3 ^ 40 * 4078551 * 2
def baseEnd_4078551 : Nat := 698085678958592461385197

theorem tailTrace_4078551 : CollatzResearch.WordTrace tailWord_4078551 prefixEnd_4078551 698085678958592461385197 := by
  unfold tailWord_4078551
  simp only [CollatzResearch.WordTrace]
  refine ⟨148756975847113762899851507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99171317231409175266567671 148756975847113762899851507)
  ·
    refine ⟨223135463770670644349777261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148756975847113762899851507 223135463770670644349777261)
    ·
      refine ⟨83675798914001491631166473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223135463770670644349777261 83675798914001491631166473)
      ·
        refine ⟨62756849185501118723374855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83675798914001491631166473 62756849185501118723374855)
        ·
          refine ⟨94135273778251678085062283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62756849185501118723374855 94135273778251678085062283)
          ·
            refine ⟨141202910667377517127593425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94135273778251678085062283 141202910667377517127593425)
            ·
              refine ⟨105902183000533137845695069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141202910667377517127593425 105902183000533137845695069)
              ·
                refine ⟨39713318625199926692135651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105902183000533137845695069 39713318625199926692135651)
                ·
                  refine ⟨59569977937799890038203477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39713318625199926692135651 59569977937799890038203477)
                  ·
                    refine ⟨698085678958592461385197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59569977937799890038203477 698085678958592461385197)
                    ·
                      rfl

theorem cell23_4078551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 1, 8].length) (baseStart_4078551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078551 prefixEnd_4078551 := by exact prefixLift 4078551
  have htrace : WordTrace (prefixWord ++ tailWord_4078551) baseStart_4078551 baseEnd_4078551 := by
    simpa [prefixWord, tailWord_4078551, baseEnd_4078551] using wordTrace_append hprefix tailTrace_4078551
  have hstable : (prefixWord ++ tailWord_4078551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078551).length < 2 ^ (prefixWord ++ tailWord_4078551).sum := by decide
  have hdescent : baseEnd_4078551 < baseStart_4078551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078649 : List Nat := [1, 2, 1, 5, 2, 3, 2, 2, 5]
def baseStart_4078649 : Nat := 118140960795 + 4078649 * 2 ^ 59
def prefixEnd_4078649 : Nat := 4983230072969 + 3 ^ 40 * 4078649 * 2
def baseEnd_4078649 : Nat := 232700817553324222303349

theorem tailTrace_4078649 : CollatzResearch.WordTrace tailWord_4078649 prefixEnd_4078649 232700817553324222303349 := by
  unfold tailWord_4078649
  simp only [CollatzResearch.WordTrace]
  refine ⟨148760550200758725636919001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99173700133839150424612667 148760550200758725636919001)
  ·
    refine ⟨111570412650569044227689251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148760550200758725636919001 111570412650569044227689251)
    ·
      refine ⟨167355618975853566341533877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111570412650569044227689251 167355618975853566341533877)
      ·
        refine ⟨15689589278986271844518801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167355618975853566341533877 15689589278986271844518801)
        ·
          refine ⟨11767191959239703883389101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15689589278986271844518801 11767191959239703883389101)
          ·
            refine ⟨4412696984714888956270913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11767191959239703883389101 4412696984714888956270913)
            ·
              refine ⟨3309522738536166717203185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4412696984714888956270913 3309522738536166717203185)
              ·
                refine ⟨2482142053902125037902389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3309522738536166717203185 2482142053902125037902389)
                ·
                  refine ⟨232700817553324222303349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2482142053902125037902389 232700817553324222303349)
                  ·
                    rfl

theorem cell23_4078649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 2, 5].length) (baseStart_4078649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078649 prefixEnd_4078649 := by exact prefixLift 4078649
  have htrace : WordTrace (prefixWord ++ tailWord_4078649) baseStart_4078649 baseEnd_4078649 := by
    simpa [prefixWord, tailWord_4078649, baseEnd_4078649] using wordTrace_append hprefix tailTrace_4078649
  have hstable : (prefixWord ++ tailWord_4078649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078649).length < 2 ^ (prefixWord ++ tailWord_4078649).sum := by decide
  have hdescent : baseEnd_4078649 < baseStart_4078649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078688 : List Nat := [2, 1, 1, 3, 2, 2, 2, 2, 8]
def baseStart_4078688 : Nat := 118140960795 + 4078688 * 2 ^ 59
def prefixEnd_4078688 : Nat := 4983230072969 + 3 ^ 40 * 4078688 * 2
def baseEnd_4078688 : Nat := 232703042636160372015829

theorem tailTrace_4078688 : CollatzResearch.WordTrace tailWord_4078688 prefixEnd_4078688 232703042636160372015829 := by
  unfold tailWord_4078688
  simp only [CollatzResearch.WordTrace]
  refine ⟨74380986323808717648794359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99174648431744956865059145 74380986323808717648794359)
  ·
    refine ⟨111571479485713076473191539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74380986323808717648794359 111571479485713076473191539)
    ·
      refine ⟨167357219228569614709787309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111571479485713076473191539 167357219228569614709787309)
      ·
        refine ⟨62758957210713605516170241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167357219228569614709787309 62758957210713605516170241)
        ·
          refine ⟨47069217908035204137127681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62758957210713605516170241 47069217908035204137127681)
          ·
            refine ⟨35301913431026403102845761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47069217908035204137127681 35301913431026403102845761)
            ·
              refine ⟨26476435073269802327134321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35301913431026403102845761 26476435073269802327134321)
              ·
                refine ⟨19857326304952351745350741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26476435073269802327134321 19857326304952351745350741)
                ·
                  refine ⟨232703042636160372015829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19857326304952351745350741 232703042636160372015829)
                  ·
                    rfl

theorem cell23_4078688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 2, 8].length) (baseStart_4078688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078688 prefixEnd_4078688 := by exact prefixLift 4078688
  have htrace : WordTrace (prefixWord ++ tailWord_4078688) baseStart_4078688 baseEnd_4078688 := by
    simpa [prefixWord, tailWord_4078688, baseEnd_4078688] using wordTrace_append hprefix tailTrace_4078688
  have hstable : (prefixWord ++ tailWord_4078688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078688).length < 2 ^ (prefixWord ++ tailWord_4078688).sum := by decide
  have hdescent : baseEnd_4078688 < baseStart_4078688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078759 : List Nat := [1, 1, 6, 2, 1, 1, 1, 1, 4, 3, 2]
def baseStart_4078759 : Nat := 118140960795 + 4078759 * 2 ^ 59
def prefixEnd_4078759 : Nat := 4983230072969 + 3 ^ 40 * 4078759 * 2
def baseEnd_4078759 : Nat := 2094363840851912570354635

theorem tailTrace_4078759 : CollatzResearch.WordTrace tailWord_4078759 prefixEnd_4078759 2094363840851912570354635 := by
  unfold tailWord_4078759
  simp only [CollatzResearch.WordTrace]
  refine ⟨148764562230360214423423331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99176374820240142948948887 148764562230360214423423331)
  ·
    refine ⟨223146843345540321635134997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148764562230360214423423331 223146843345540321635134997)
    ·
      refine ⟨10460008281822202576646953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 223146843345540321635134997 10460008281822202576646953)
      ·
        refine ⟨7845006211366651932485215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10460008281822202576646953 7845006211366651932485215)
        ·
          refine ⟨11767509317049977898727823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7845006211366651932485215 11767509317049977898727823)
          ·
            refine ⟨17651263975574966848091735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11767509317049977898727823 17651263975574966848091735)
            ·
              refine ⟨26476895963362450272137603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17651263975574966848091735 26476895963362450272137603)
              ·
                refine ⟨39715343945043675408206405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26476895963362450272137603 39715343945043675408206405)
                ·
                  refine ⟨7446626989695689139038701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39715343945043675408206405 7446626989695689139038701)
                  ·
                    refine ⟨2792485121135883427139513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7446626989695689139038701 2792485121135883427139513)
                    ·
                      refine ⟨2094363840851912570354635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792485121135883427139513 2094363840851912570354635)
                      ·
                        rfl

theorem cell23_4078759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_4078759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078759 prefixEnd_4078759 := by exact prefixLift 4078759
  have htrace : WordTrace (prefixWord ++ tailWord_4078759) baseStart_4078759 baseEnd_4078759 := by
    simpa [prefixWord, tailWord_4078759, baseEnd_4078759] using wordTrace_append hprefix tailTrace_4078759
  have hstable : (prefixWord ++ tailWord_4078759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078759).length < 2 ^ (prefixWord ++ tailWord_4078759).sum := by decide
  have hdescent : baseEnd_4078759 < baseStart_4078759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078775 : List Nat := [1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 5]
def baseStart_4078775 : Nat := 118140960795 + 4078775 * 2 ^ 59
def prefixEnd_4078775 : Nat := 4983230072969 + 3 ^ 40 * 4078775 * 2
def baseEnd_4078775 : Nat := 2094372056542384507754561

theorem tailTrace_4078775 : CollatzResearch.WordTrace tailWord_4078775 prefixEnd_4078775 2094372056542384507754561 := by
  unfold tailWord_4078775
  simp only [CollatzResearch.WordTrace]
  refine ⟨148765145798302249156005779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99176763865534832770670519 148765145798302249156005779)
  ·
    refine ⟨223147718697453373734008669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148765145798302249156005779 223147718697453373734008669)
    ·
      refine ⟨83680394511545015150253251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 223147718697453373734008669 83680394511545015150253251)
      ·
        refine ⟨125520591767317522725379877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83680394511545015150253251 125520591767317522725379877)
        ·
          refine ⟨23535110956372035511008727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125520591767317522725379877 23535110956372035511008727)
          ·
            refine ⟨35302666434558053266513091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23535110956372035511008727 35302666434558053266513091)
            ·
              refine ⟨52953999651837079899769637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35302666434558053266513091 52953999651837079899769637)
              ·
                refine ⟨9928874934719452481206807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52953999651837079899769637 9928874934719452481206807)
                ·
                  refine ⟨14893312402079178721810211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928874934719452481206807 14893312402079178721810211)
                  ·
                    refine ⟨22339968603118768082715317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14893312402079178721810211 22339968603118768082715317)
                    ·
                      refine ⟨2094372056542384507754561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22339968603118768082715317 2094372056542384507754561)
                      ·
                        rfl

theorem cell23_4078775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 5].length) (baseStart_4078775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078775 prefixEnd_4078775 := by exact prefixLift 4078775
  have htrace : WordTrace (prefixWord ++ tailWord_4078775) baseStart_4078775 baseEnd_4078775 := by
    simpa [prefixWord, tailWord_4078775, baseEnd_4078775] using wordTrace_append hprefix tailTrace_4078775
  have hstable : (prefixWord ++ tailWord_4078775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078775).length < 2 ^ (prefixWord ++ tailWord_4078775).sum := by decide
  have hdescent : baseEnd_4078775 < baseStart_4078775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078786 : List Nat := [3, 5, 1, 1, 2, 1, 1, 1, 3, 5]
def baseStart_4078786 : Nat := 118140960795 + 4078786 * 2 ^ 59
def prefixEnd_4078786 : Nat := 4983230072969 + 3 ^ 40 * 4078786 * 2
def baseEnd_4078786 : Nat := 698125901609861321572337

theorem tailTrace_4078786 : CollatzResearch.WordTrace tailWord_4078786 prefixEnd_4078786 698125901609861321572337 := by
  unfold tailWord_4078786
  simp only [CollatzResearch.WordTrace]
  refine ⟨37191386750315599508664053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99177031334174932023104141 37191386750315599508664053)
  ·
    refine ⟨3486692507842087453937255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37191386750315599508664053 3486692507842087453937255)
    ·
      refine ⟨5230038761763131180905883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3486692507842087453937255 5230038761763131180905883)
      ·
        refine ⟨7845058142644696771358825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230038761763131180905883 7845058142644696771358825)
        ·
          refine ⟨5883793606983522578519119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7845058142644696771358825 5883793606983522578519119)
          ·
            refine ⟨8825690410475283867778679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5883793606983522578519119 8825690410475283867778679)
            ·
              refine ⟨13238535615712925801668019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8825690410475283867778679 13238535615712925801668019)
              ·
                refine ⟨19857803423569388702502029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13238535615712925801668019 19857803423569388702502029)
                ·
                  refine ⟨7446676283838520763438261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19857803423569388702502029 7446676283838520763438261)
                  ·
                    refine ⟨698125901609861321572337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7446676283838520763438261 698125901609861321572337)
                    ·
                      rfl

theorem cell23_4078786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_4078786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078786 prefixEnd_4078786 := by exact prefixLift 4078786
  have htrace : WordTrace (prefixWord ++ tailWord_4078786) baseStart_4078786 baseEnd_4078786 := by
    simpa [prefixWord, tailWord_4078786, baseEnd_4078786] using wordTrace_append hprefix tailTrace_4078786
  have hstable : (prefixWord ++ tailWord_4078786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078786).length < 2 ^ (prefixWord ++ tailWord_4078786).sum := by decide
  have hdescent : baseEnd_4078786 < baseStart_4078786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078802 : List Nat := [3, 2, 2, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4078802 : Nat := 118140960795 + 4078802 * 2 ^ 59
def prefixEnd_4078802 : Nat := 4983230072969 + 3 ^ 40 * 4078802 * 2
def baseEnd_4078802 : Nat := 2094385920520055902116937

theorem tailTrace_4078802 : CollatzResearch.WordTrace tailWord_4078802 prefixEnd_4078802 2094385920520055902116937 := by
  unfold tailWord_4078802
  simp only [CollatzResearch.WordTrace]
  refine ⟨37191532642301108191809665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99177420379469621844825773 37191532642301108191809665)
  ·
    refine ⟨27893649481725831143857249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37191532642301108191809665 27893649481725831143857249)
    ·
      refine ⟨20920237111294373357892937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27893649481725831143857249 20920237111294373357892937)
      ·
        refine ⟨15690177833470780018419703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20920237111294373357892937 15690177833470780018419703)
        ·
          refine ⟨23535266750206170027629555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15690177833470780018419703 23535266750206170027629555)
          ·
            refine ⟨35302900125309255041444333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23535266750206170027629555 35302900125309255041444333)
            ·
              refine ⟨13238587546990970640541625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35302900125309255041444333 13238587546990970640541625)
              ·
                refine ⟨9928940660243227980406219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13238587546990970640541625 9928940660243227980406219)
                ·
                  refine ⟨14893410990364841970609329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9928940660243227980406219 14893410990364841970609329)
                  ·
                    refine ⟨11170058242773631477956997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14893410990364841970609329 11170058242773631477956997)
                    ·
                      refine ⟨2094385920520055902116937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11170058242773631477956997 2094385920520055902116937)
                      ·
                        rfl

theorem cell23_4078802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4078802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078802 prefixEnd_4078802 := by exact prefixLift 4078802
  have htrace : WordTrace (prefixWord ++ tailWord_4078802) baseStart_4078802 baseEnd_4078802 := by
    simpa [prefixWord, tailWord_4078802, baseEnd_4078802] using wordTrace_append hprefix tailTrace_4078802
  have hstable : (prefixWord ++ tailWord_4078802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078802).length < 2 ^ (prefixWord ++ tailWord_4078802).sum := by decide
  have hdescent : baseEnd_4078802 < baseStart_4078802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078849 : List Nat := [1, 2, 4, 1, 1, 3, 2, 1, 3, 3, 2]
def baseStart_4078849 : Nat := 118140960795 + 4078849 * 2 ^ 59
def prefixEnd_4078849 : Nat := 4983230072969 + 3 ^ 40 * 4078849 * 2
def baseEnd_4078849 : Nat := 2094410054110817218229221

theorem tailTrace_4078849 : CollatzResearch.WordTrace tailWord_4078849 prefixEnd_4078849 2094410054110817218229221 := by
  unfold tailWord_4078849
  simp only [CollatzResearch.WordTrace]
  refine ⟨148767844800034159794199601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99178563200022773196133067 148767844800034159794199601)
  ·
    refine ⟨111575883600025619845649701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148767844800034159794199601 111575883600025619845649701)
    ·
      refine ⟨20920478175004803721059319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111575883600025619845649701 20920478175004803721059319)
      ·
        refine ⟨31380717262507205581588979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20920478175004803721059319 31380717262507205581588979)
        ·
          refine ⟨47071075893760808372383469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31380717262507205581588979 47071075893760808372383469)
          ·
            refine ⟨17651653460160303139643801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47071075893760808372383469 17651653460160303139643801)
            ·
              refine ⟨13238740095120227354732851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17651653460160303139643801 13238740095120227354732851)
              ·
                refine ⟨19858110142680341032099277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13238740095120227354732851 19858110142680341032099277)
                ·
                  refine ⟨7446791303505127887037229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19858110142680341032099277 7446791303505127887037229)
                  ·
                    refine ⟨2792546738814422957638961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7446791303505127887037229 2792546738814422957638961)
                    ·
                      refine ⟨2094410054110817218229221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792546738814422957638961 2094410054110817218229221)
                      ·
                        rfl

theorem cell23_4078849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_4078849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078849 prefixEnd_4078849 := by exact prefixLift 4078849
  have htrace : WordTrace (prefixWord ++ tailWord_4078849) baseStart_4078849 baseEnd_4078849 := by
    simpa [prefixWord, tailWord_4078849, baseEnd_4078849] using wordTrace_append hprefix tailTrace_4078849
  have hstable : (prefixWord ++ tailWord_4078849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078849).length < 2 ^ (prefixWord ++ tailWord_4078849).sum := by decide
  have hdescent : baseEnd_4078849 < baseStart_4078849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078865 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 5]
def baseStart_4078865 : Nat := 118140960795 + 4078865 * 2 ^ 59
def prefixEnd_4078865 : Nat := 4983230072969 + 3 ^ 40 * 4078865 * 2
def baseEnd_4078865 : Nat := 2094418269801289155629147

theorem tailTrace_4078865 : CollatzResearch.WordTrace tailWord_4078865 prefixEnd_4078865 2094418269801289155629147 := by
  unfold tailWord_4078865
  simp only [CollatzResearch.WordTrace]
  refine ⟨148768428367976194526782049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99178952245317463017854699 148768428367976194526782049)
  ·
    refine ⟨111576321275982145895086537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148768428367976194526782049 111576321275982145895086537)
    ·
      refine ⟨83682240956986609421314903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111576321275982145895086537 83682240956986609421314903)
      ·
        refine ⟨125523361435479914131972355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83682240956986609421314903 125523361435479914131972355)
        ·
          refine ⟨188285042153219871197958533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125523361435479914131972355 188285042153219871197958533)
          ·
            refine ⟨35303445403728725849617225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188285042153219871197958533 35303445403728725849617225)
            ·
              refine ⟨26477584052796544387212919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35303445403728725849617225 26477584052796544387212919)
              ·
                refine ⟨39716376079194816580819379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26477584052796544387212919 39716376079194816580819379)
                ·
                  refine ⟨59574564118792224871229069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39716376079194816580819379 59574564118792224871229069)
                  ·
                    refine ⟨22340461544547084326710901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 59574564118792224871229069 22340461544547084326710901)
                    ·
                      refine ⟨2094418269801289155629147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22340461544547084326710901 2094418269801289155629147)
                      ·
                        rfl

theorem cell23_4078865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_4078865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078865 prefixEnd_4078865 := by exact prefixLift 4078865
  have htrace : WordTrace (prefixWord ++ tailWord_4078865) baseStart_4078865 baseEnd_4078865 := by
    simpa [prefixWord, tailWord_4078865, baseEnd_4078865] using wordTrace_append hprefix tailTrace_4078865
  have hstable : (prefixWord ++ tailWord_4078865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078865).length < 2 ^ (prefixWord ++ tailWord_4078865).sum := by decide
  have hdescent : baseEnd_4078865 < baseStart_4078865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4078919 : List Nat := [1, 1, 4, 1, 2, 3, 3, 3, 5]
def baseStart_4078919 : Nat := 118140960795 + 4078919 * 2 ^ 59
def prefixEnd_4078919 : Nat := 4983230072969 + 3 ^ 40 * 4078919 * 2
def baseEnd_4078919 : Nat := 232716221972959104928211

theorem tailTrace_4078919 : CollatzResearch.WordTrace tailWord_4078919 prefixEnd_4078919 232716221972959104928211 := by
  unfold tailWord_4078919
  simp only [CollatzResearch.WordTrace]
  refine ⟨148770397909780561749247811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99180265273187041166165207 148770397909780561749247811)
  ·
    refine ⟨223155596864670842623871717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148770397909780561749247811 223155596864670842623871717)
    ·
      refine ⟨41841674412125782991975947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223155596864670842623871717 41841674412125782991975947)
      ·
        refine ⟨62762511618188674487963921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41841674412125782991975947 62762511618188674487963921)
        ·
          refine ⟨47071883713641505865972941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62762511618188674487963921 47071883713641505865972941)
          ·
            refine ⟨17651956392615564699739853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47071883713641505865972941 17651956392615564699739853)
            ·
              refine ⟨6619483647230836762402445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17651956392615564699739853 6619483647230836762402445)
              ·
                refine ⟨2482306367711563785900917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6619483647230836762402445 2482306367711563785900917)
                ·
                  refine ⟨232716221972959104928211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2482306367711563785900917 232716221972959104928211)
                  ·
                    rfl

theorem cell23_4078919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 3, 5].length) (baseStart_4078919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4078919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4078919 prefixEnd_4078919 := by exact prefixLift 4078919
  have htrace : WordTrace (prefixWord ++ tailWord_4078919) baseStart_4078919 baseEnd_4078919 := by
    simpa [prefixWord, tailWord_4078919, baseEnd_4078919] using wordTrace_append hprefix tailTrace_4078919
  have hstable : (prefixWord ++ tailWord_4078919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4078919).length < 2 ^ (prefixWord ++ tailWord_4078919).sum := by decide
  have hdescent : baseEnd_4078919 < baseStart_4078919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4078919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079093 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4079093 : Nat := 118140960795 + 4079093 * 2 ^ 59
def prefixEnd_4079093 : Nat := 4983230072969 + 3 ^ 40 * 4079093 * 2
def baseEnd_4079093 : Nat := 2094535343390514263578099

theorem tailTrace_4079093 : CollatzResearch.WordTrace tailWord_4079093 prefixEnd_4079093 2094535343390514263578099 := by
  unfold tailWord_4079093
  simp only [CollatzResearch.WordTrace]
  refine ⟨148776744211150189466081933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99184496140766792977387955 148776744211150189466081933)
  ·
    refine ⟨55791279079181321049780725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148776744211150189466081933 55791279079181321049780725)
    ·
      refine ⟨5230432413673248848416943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55791279079181321049780725 5230432413673248848416943)
      ·
        refine ⟨7845648620509873272625415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5230432413673248848416943 7845648620509873272625415)
        ·
          refine ⟨11768472930764809908938123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7845648620509873272625415 11768472930764809908938123)
          ·
            refine ⟨17652709396147214863407185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11768472930764809908938123 17652709396147214863407185)
            ·
              refine ⟨13239532047110411147555389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17652709396147214863407185 13239532047110411147555389)
              ·
                refine ⟨4964824517666404180333271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13239532047110411147555389 4964824517666404180333271)
                ·
                  refine ⟨7447236776499606270499907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964824517666404180333271 7447236776499606270499907)
                  ·
                    refine ⟨11170855164749409405749861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7447236776499606270499907 11170855164749409405749861)
                    ·
                      refine ⟨2094535343390514263578099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11170855164749409405749861 2094535343390514263578099)
                      ·
                        rfl

theorem cell23_4079093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4079093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079093 prefixEnd_4079093 := by exact prefixLift 4079093
  have htrace : WordTrace (prefixWord ++ tailWord_4079093) baseStart_4079093 baseEnd_4079093 := by
    simpa [prefixWord, tailWord_4079093, baseEnd_4079093] using wordTrace_append hprefix tailTrace_4079093
  have hstable : (prefixWord ++ tailWord_4079093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079093).length < 2 ^ (prefixWord ++ tailWord_4079093).sum := by decide
  have hdescent : baseEnd_4079093 < baseStart_4079093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079096 : List Nat := [2, 1, 2, 1, 1, 5, 2, 3, 1, 2, 3]
def baseStart_4079096 : Nat := 118140960795 + 4079096 * 2 ^ 59
def prefixEnd_4079096 : Nat := 4983230072969 + 3 ^ 40 * 4079096 * 2
def baseEnd_4079096 : Nat := 2094536883832477751840585

theorem tailTrace_4079096 : CollatzResearch.WordTrace tailWord_4079096 prefixEnd_4079096 2094536883832477751840585 := by
  unfold tailWord_4079096
  simp only [CollatzResearch.WordTrace]
  refine ⟨74388426815069660489220571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99184569086759547318960761 74388426815069660489220571)
  ·
    refine ⟨111582640222604490733830857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74388426815069660489220571 111582640222604490733830857)
    ·
      refine ⟨83686980166953368050373143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111582640222604490733830857 83686980166953368050373143)
      ·
        refine ⟨125530470250430052075559715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83686980166953368050373143 125530470250430052075559715)
        ·
          refine ⟨188295705375645078113339573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125530470250430052075559715 188295705375645078113339573)
          ·
            refine ⟨17652722378966726073125585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 188295705375645078113339573 17652722378966726073125585)
            ·
              refine ⟨13239541784225044554844189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17652722378966726073125585 13239541784225044554844189)
              ·
                refine ⟨4964828169084391708066571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13239541784225044554844189 4964828169084391708066571)
                ·
                  refine ⟨7447242253626587562099857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4964828169084391708066571 7447242253626587562099857)
                  ·
                    refine ⟨5585431690219940671574893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7447242253626587562099857 5585431690219940671574893)
                    ·
                      refine ⟨2094536883832477751840585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5585431690219940671574893 2094536883832477751840585)
                      ·
                        rfl

theorem cell23_4079096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 3, 1, 2, 3].length) (baseStart_4079096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079096 prefixEnd_4079096 := by exact prefixLift 4079096
  have htrace : WordTrace (prefixWord ++ tailWord_4079096) baseStart_4079096 baseEnd_4079096 := by
    simpa [prefixWord, tailWord_4079096, baseEnd_4079096] using wordTrace_append hprefix tailTrace_4079096
  have hstable : (prefixWord ++ tailWord_4079096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079096).length < 2 ^ (prefixWord ++ tailWord_4079096).sum := by decide
  have hdescent : baseEnd_4079096 < baseStart_4079096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079106 : List Nat := [3, 4, 1, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_4079106 : Nat := 118140960795 + 4079106 * 2 ^ 59
def prefixEnd_4079106 : Nat := 4983230072969 + 3 ^ 40 * 4079106 * 2
def baseEnd_4079106 : Nat := 2094542018639022712715539

theorem tailTrace_4079106 : CollatzResearch.WordTrace tailWord_4079106 prefixEnd_4079106 2094542018639022712715539 := by
  unfold tailWord_4079106
  simp only [CollatzResearch.WordTrace]
  refine ⟨37194304590025773171576293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99184812240068728457536781 37194304590025773171576293)
  ·
    refine ⟨6973932110629832469670555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37194304590025773171576293 6973932110629832469670555)
    ·
      refine ⟨10460898165944748704505833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6973932110629832469670555 10460898165944748704505833)
      ·
        refine ⟨7845673624458561528379375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10460898165944748704505833 7845673624458561528379375)
        ·
          refine ⟨11768510436687842292569063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7845673624458561528379375 11768510436687842292569063)
          ·
            refine ⟨17652765655031763438853595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11768510436687842292569063 17652765655031763438853595)
            ·
              refine ⟨26479148482547645158280393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17652765655031763438853595 26479148482547645158280393)
              ·
                refine ⟨19859361361910733868710295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26479148482547645158280393 19859361361910733868710295)
                ·
                  refine ⟨29789042042866100803065443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19859361361910733868710295 29789042042866100803065443)
                  ·
                    refine ⟨44683563064299151204598165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29789042042866100803065443 44683563064299151204598165)
                    ·
                      refine ⟨2094542018639022712715539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44683563064299151204598165 2094542018639022712715539)
                      ·
                        rfl

theorem cell23_4079106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_4079106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079106 prefixEnd_4079106 := by exact prefixLift 4079106
  have htrace : WordTrace (prefixWord ++ tailWord_4079106) baseStart_4079106 baseEnd_4079106 := by
    simpa [prefixWord, tailWord_4079106, baseEnd_4079106] using wordTrace_append hprefix tailTrace_4079106
  have hstable : (prefixWord ++ tailWord_4079106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079106).length < 2 ^ (prefixWord ++ tailWord_4079106).sum := by decide
  have hdescent : baseEnd_4079106 < baseStart_4079106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079216 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_4079216 : Nat := 118140960795 + 4079216 * 2 ^ 59
def prefixEnd_4079216 : Nat := 4983230072969 + 3 ^ 40 * 4079216 * 2
def baseEnd_4079216 : Nat := 2094598501511017282340033

theorem tailTrace_4079216 : CollatzResearch.WordTrace tailWord_4079216 prefixEnd_4079216 2094598501511017282340033 := by
  unfold tailWord_4079216
  simp only [CollatzResearch.WordTrace]
  refine ⟨74390615194852290736404751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99187486926469720981873001 74390615194852290736404751)
  ·
    refine ⟨111585922792278436104607127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74390615194852290736404751 111585922792278436104607127)
    ·
      refine ⟨167378884188417654156910691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111585922792278436104607127 167378884188417654156910691)
      ·
        refine ⟨251068326282626481235366037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167378884188417654156910691 251068326282626481235366037)
        ·
          refine ⟨11768827794498116307907783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 251068326282626481235366037 11768827794498116307907783)
          ·
            refine ⟨17653241691747174461861675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11768827794498116307907783 17653241691747174461861675)
            ·
              refine ⟨26479862537620761692792513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17653241691747174461861675 26479862537620761692792513)
              ·
                refine ⟨19859896903215571269594385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26479862537620761692792513 19859896903215571269594385)
                ·
                  refine ⟨14894922677411678452195789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19859896903215571269594385 14894922677411678452195789)
                  ·
                    refine ⟨5585596004029379419573421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14894922677411678452195789 5585596004029379419573421)
                    ·
                      refine ⟨2094598501511017282340033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5585596004029379419573421 2094598501511017282340033)
                      ·
                        rfl

theorem cell23_4079216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_4079216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079216 prefixEnd_4079216 := by exact prefixLift 4079216
  have htrace : WordTrace (prefixWord ++ tailWord_4079216) baseStart_4079216 baseEnd_4079216 := by
    simpa [prefixWord, tailWord_4079216, baseEnd_4079216] using wordTrace_append hprefix tailTrace_4079216
  have hstable : (prefixWord ++ tailWord_4079216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079216).length < 2 ^ (prefixWord ++ tailWord_4079216).sum := by decide
  have hdescent : baseEnd_4079216 < baseStart_4079216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079226 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2]
def baseStart_4079226 : Nat := 118140960795 + 4079226 * 2 ^ 59
def prefixEnd_4079226 : Nat := 4983230072969 + 3 ^ 40 * 4079226 * 2
def baseEnd_4079226 : Nat := 2094603636317562243214987

theorem tailTrace_4079226 : CollatzResearch.WordTrace tailWord_4079226 prefixEnd_4079226 2094603636317562243214987 := by
  unfold tailWord_4079226
  simp only [CollatzResearch.WordTrace]
  refine ⟨37195398779917088295168383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99187730079778902120449021 37195398779917088295168383)
  ·
    refine ⟨55793098169875632442752575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37195398779917088295168383 55793098169875632442752575)
    ·
      refine ⟨83689647254813448664128863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55793098169875632442752575 83689647254813448664128863)
      ·
        refine ⟨125534470882220172996193295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83689647254813448664128863 125534470882220172996193295)
        ·
          refine ⟨188301706323330259494289943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125534470882220172996193295 188301706323330259494289943)
          ·
            refine ⟨282452559484995389241434915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188301706323330259494289943 282452559484995389241434915)
            ·
              refine ⟨423678839227493083862152373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282452559484995389241434915 423678839227493083862152373)
              ·
                refine ⟨39719891177577476612076785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 423678839227493083862152373 39719891177577476612076785)
                ·
                  refine ⟨29789918383183107459057589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39719891177577476612076785 29789918383183107459057589)
                  ·
                    refine ⟨2792804848423416324286649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29789918383183107459057589 2792804848423416324286649)
                    ·
                      refine ⟨2094603636317562243214987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792804848423416324286649 2094603636317562243214987)
                      ·
                        rfl

theorem cell23_4079226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 2, 5, 2].length) (baseStart_4079226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079226 prefixEnd_4079226 := by exact prefixLift 4079226
  have htrace : WordTrace (prefixWord ++ tailWord_4079226) baseStart_4079226 baseEnd_4079226 := by
    simpa [prefixWord, tailWord_4079226, baseEnd_4079226] using wordTrace_append hprefix tailTrace_4079226
  have hstable : (prefixWord ++ tailWord_4079226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079226).length < 2 ^ (prefixWord ++ tailWord_4079226).sum := by decide
  have hdescent : baseEnd_4079226 < baseStart_4079226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079256 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4079256 : Nat := 118140960795 + 4079256 * 2 ^ 59
def prefixEnd_4079256 : Nat := 4983230072969 + 3 ^ 40 * 4079256 * 2
def baseEnd_4079256 : Nat := 2094619040737197125839849

theorem tailTrace_4079256 : CollatzResearch.WordTrace tailWord_4079256 prefixEnd_4079256 2094619040737197125839849 := by
  unfold tailWord_4079256
  simp only [CollatzResearch.WordTrace]
  refine ⟨74391344654779834152132811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99188459539706445536177081 74391344654779834152132811)
  ·
    refine ⟨111587016982169751228199217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74391344654779834152132811 111587016982169751228199217)
    ·
      refine ⟨83690262736627313421149413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111587016982169751228199217 83690262736627313421149413)
      ·
        refine ⟨15691924263117621266465515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83690262736627313421149413 15691924263117621266465515)
        ·
          refine ⟨23537886394676431899698273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15691924263117621266465515 23537886394676431899698273)
          ·
            refine ⟨17653414796007323924773705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23537886394676431899698273 17653414796007323924773705)
            ·
              refine ⟨13240061097005492943580279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17653414796007323924773705 13240061097005492943580279)
              ·
                refine ⟨19860091645508239415370419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13240061097005492943580279 19860091645508239415370419)
                ·
                  refine ⟨29790137468262359123055629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19860091645508239415370419 29790137468262359123055629)
                  ·
                    refine ⟨11171301550598384671145861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29790137468262359123055629 11171301550598384671145861)
                    ·
                      refine ⟨2094619040737197125839849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11171301550598384671145861 2094619040737197125839849)
                      ·
                        rfl

theorem cell23_4079256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4079256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079256 prefixEnd_4079256 := by exact prefixLift 4079256
  have htrace : WordTrace (prefixWord ++ tailWord_4079256) baseStart_4079256 baseEnd_4079256 := by
    simpa [prefixWord, tailWord_4079256, baseEnd_4079256] using wordTrace_append hprefix tailTrace_4079256
  have hstable : (prefixWord ++ tailWord_4079256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079256).length < 2 ^ (prefixWord ++ tailWord_4079256).sum := by decide
  have hdescent : baseEnd_4079256 < baseStart_4079256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079269 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 6]
def baseStart_4079269 : Nat := 118140960795 + 4079269 * 2 ^ 59
def prefixEnd_4079269 : Nat := 4983230072969 + 3 ^ 40 * 4079269 * 2
def baseEnd_4079269 : Nat := 2094625715985705574977289

theorem tailTrace_4079269 : CollatzResearch.WordTrace tailWord_4079269 prefixEnd_4079269 2094625715985705574977289 := by
  unfold tailWord_4079269
  simp only [CollatzResearch.WordTrace]
  refine ⟨148783163458512571524488861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99188775639008381016325907 148783163458512571524488861)
  ·
    refine ⟨55793686296942214321683323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148783163458512571524488861 55793686296942214321683323)
    ·
      refine ⟨83690529445413321482524985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55793686296942214321683323 83690529445413321482524985)
      ·
        refine ⟨62767897084059991111893739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83690529445413321482524985 62767897084059991111893739)
        ·
          refine ⟨94151845626089986667840609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62767897084059991111893739 94151845626089986667840609)
          ·
            refine ⟨70613884219567490000880457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94151845626089986667840609 70613884219567490000880457)
            ·
              refine ⟨52960413164675617500660343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70613884219567490000880457 52960413164675617500660343)
              ·
                refine ⟨79440619747013426250990515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52960413164675617500660343 79440619747013426250990515)
                ·
                  refine ⟨119160929620520139376485773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79440619747013426250990515 119160929620520139376485773)
                  ·
                    refine ⟨44685348607695052266182165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 119160929620520139376485773 44685348607695052266182165)
                    ·
                      refine ⟨2094625715985705574977289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44685348607695052266182165 2094625715985705574977289)
                      ·
                        rfl

theorem cell23_4079269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_4079269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079269 prefixEnd_4079269 := by exact prefixLift 4079269
  have htrace : WordTrace (prefixWord ++ tailWord_4079269) baseStart_4079269 baseEnd_4079269 := by
    simpa [prefixWord, tailWord_4079269, baseEnd_4079269] using wordTrace_append hprefix tailTrace_4079269
  have hstable : (prefixWord ++ tailWord_4079269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079269).length < 2 ^ (prefixWord ++ tailWord_4079269).sum := by decide
  have hdescent : baseEnd_4079269 < baseStart_4079269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079279 : List Nat := [1, 1, 2, 1, 2, 4, 1, 3, 8]
def baseStart_4079279 : Nat := 118140960795 + 4079279 * 2 ^ 59
def prefixEnd_4079279 : Nat := 4983230072969 + 3 ^ 40 * 4079279 * 2
def baseEnd_4079279 : Nat := 232736761199138948428027

theorem tailTrace_4079279 : CollatzResearch.WordTrace tailWord_4079279 prefixEnd_4079279 232736761199138948428027 := by
  unfold tailWord_4079279
  simp only [CollatzResearch.WordTrace]
  refine ⟨148783528188476343232352891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99189018792317562154901927 148783528188476343232352891)
  ·
    refine ⟨223175292282714514848529337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148783528188476343232352891 223175292282714514848529337)
    ·
      refine ⟨167381469212035886136397003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223175292282714514848529337 167381469212035886136397003)
      ·
        refine ⟨251072203818053829204595505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167381469212035886136397003 251072203818053829204595505)
        ·
          refine ⟨188304152863540371903446629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251072203818053829204595505 188304152863540371903446629)
          ·
            refine ⟨35307028661913819731896243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 188304152863540371903446629 35307028661913819731896243)
            ·
              refine ⟨52960542992870729597844365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35307028661913819731896243 52960542992870729597844365)
              ·
                refine ⟨19860203622326523599191637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52960542992870729597844365 19860203622326523599191637)
                ·
                  refine ⟨232736761199138948428027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19860203622326523599191637 232736761199138948428027)
                  ·
                    rfl

theorem cell23_4079279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 3, 8].length) (baseStart_4079279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079279 prefixEnd_4079279 := by exact prefixLift 4079279
  have htrace : WordTrace (prefixWord ++ tailWord_4079279) baseStart_4079279 baseEnd_4079279 := by
    simpa [prefixWord, tailWord_4079279, baseEnd_4079279] using wordTrace_append hprefix tailTrace_4079279
  have hstable : (prefixWord ++ tailWord_4079279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079279).length < 2 ^ (prefixWord ++ tailWord_4079279).sum := by decide
  have hdescent : baseEnd_4079279 < baseStart_4079279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079296 : List Nat := [2, 1, 1, 2, 4, 1, 3, 3, 6]
def baseStart_4079296 : Nat := 118140960795 + 4079296 * 2 ^ 59
def prefixEnd_4079296 : Nat := 4983230072969 + 3 ^ 40 * 4079296 * 2
def baseEnd_4079296 : Nat := 232737731107041885482185

theorem tailTrace_4079296 : CollatzResearch.WordTrace tailWord_4079296 prefixEnd_4079296 232737731107041885482185 := by
  unfold tailWord_4079296
  simp only [CollatzResearch.WordTrace]
  refine ⟨74392074114707377567860871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99189432152943170090481161 74392074114707377567860871)
  ·
    refine ⟨111588111172061066351791307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74392074114707377567860871 111588111172061066351791307)
    ·
      refine ⟨167382166758091599527686961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111588111172061066351791307 167382166758091599527686961)
      ·
        refine ⟨125536625068568699645765221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167382166758091599527686961 125536625068568699645765221)
        ·
          refine ⟨23538117200356631183580979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125536625068568699645765221 23538117200356631183580979)
          ·
            refine ⟨35307175800534946775371469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23538117200356631183580979 35307175800534946775371469)
            ·
              refine ⟨13240190925200605040764301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35307175800534946775371469 13240190925200605040764301)
              ·
                refine ⟨4965071596950226890286613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13240190925200605040764301 4965071596950226890286613)
                ·
                  refine ⟨232737731107041885482185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4965071596950226890286613 232737731107041885482185)
                  ·
                    rfl

theorem cell23_4079296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 3, 6].length) (baseStart_4079296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079296 prefixEnd_4079296 := by exact prefixLift 4079296
  have htrace : WordTrace (prefixWord ++ tailWord_4079296) baseStart_4079296 baseEnd_4079296 := by
    simpa [prefixWord, tailWord_4079296, baseEnd_4079296] using wordTrace_append hprefix tailTrace_4079296
  have hstable : (prefixWord ++ tailWord_4079296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079296).length < 2 ^ (prefixWord ++ tailWord_4079296).sum := by decide
  have hdescent : baseEnd_4079296 < baseStart_4079296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079386 : List Nat := [3, 1, 1, 3, 2, 3, 10]
def baseStart_4079386 : Nat := 118140960795 + 4079386 * 2 ^ 59
def prefixEnd_4079386 : Nat := 4983230072969 + 3 ^ 40 * 4079386 * 2
def baseEnd_4079386 : Nat := 25860318434842982928571

theorem tailTrace_4079386 : CollatzResearch.WordTrace tailWord_4079386 prefixEnd_4079386 25860318434842982928571 := by
  unfold tailWord_4079386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37196857699772175126624503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99191620532725800337665341 37196857699772175126624503)
  ·
    refine ⟨55795286549658262689936755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37196857699772175126624503 55795286549658262689936755)
    ·
      refine ⟨83692929824487394034905133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55795286549658262689936755 83692929824487394034905133)
      ·
        refine ⟨31384848684182772763089425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83692929824487394034905133 31384848684182772763089425)
        ·
          refine ⟨23538636513137079572317069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31384848684182772763089425 23538636513137079572317069)
          ·
            refine ⟨8826988692426404839618901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23538636513137079572317069 8826988692426404839618901)
            ·
              refine ⟨25860318434842982928571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 8826988692426404839618901 25860318434842982928571)
              ·
                rfl

theorem cell23_4079386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 10].length) (baseStart_4079386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079386 prefixEnd_4079386 := by exact prefixLift 4079386
  have htrace : WordTrace (prefixWord ++ tailWord_4079386) baseStart_4079386 baseEnd_4079386 := by
    simpa [prefixWord, tailWord_4079386, baseEnd_4079386] using wordTrace_append hprefix tailTrace_4079386
  have hstable : (prefixWord ++ tailWord_4079386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079386).length < 2 ^ (prefixWord ++ tailWord_4079386).sum := by decide
  have hdescent : baseEnd_4079386 < baseStart_4079386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079397 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 3, 2, 2]
def baseStart_4079397 : Nat := 118140960795 + 4079397 * 2 ^ 59
def prefixEnd_4079397 : Nat := 4983230072969 + 3 ^ 40 * 4079397 * 2
def baseEnd_4079397 : Nat := 2094691441509481074176701

theorem tailTrace_4079397 : CollatzResearch.WordTrace tailWord_4079397 prefixEnd_4079397 2094691441509481074176701 := by
  unfold tailWord_4079397
  simp only [CollatzResearch.WordTrace]
  refine ⟨148787832002048849385148445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99191888001365899590098963 148787832002048849385148445)
  ·
    refine ⟨55795437000768318519430667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148787832002048849385148445 55795437000768318519430667)
    ·
      refine ⟨83693155501152477779146001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55795437000768318519430667 83693155501152477779146001)
      ·
        refine ⟨62769866625864358334359501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83693155501152477779146001 62769866625864358334359501)
        ·
          refine ⟨23538699984699134375384813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62769866625864358334359501 23538699984699134375384813)
          ·
            refine ⟨8827012494262175390769305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23538699984699134375384813 8827012494262175390769305)
            ·
              refine ⟨6620259370696631543076979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8827012494262175390769305 6620259370696631543076979)
              ·
                refine ⟨9930389056044947314615469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620259370696631543076979 9930389056044947314615469)
                ·
                  refine ⟨3723895896016855242980801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9930389056044947314615469 3723895896016855242980801)
                  ·
                    refine ⟨2792921922012641432235601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3723895896016855242980801 2792921922012641432235601)
                    ·
                      refine ⟨2094691441509481074176701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792921922012641432235601 2094691441509481074176701)
                      ·
                        rfl

theorem cell23_4079397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_4079397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079397 prefixEnd_4079397 := by exact prefixLift 4079397
  have htrace : WordTrace (prefixWord ++ tailWord_4079397) baseStart_4079397 baseEnd_4079397 := by
    simpa [prefixWord, tailWord_4079397, baseEnd_4079397] using wordTrace_append hprefix tailTrace_4079397
  have hstable : (prefixWord ++ tailWord_4079397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079397).length < 2 ^ (prefixWord ++ tailWord_4079397).sum := by decide
  have hdescent : baseEnd_4079397 < baseStart_4079397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079410 : List Nat := [3, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_4079410 : Nat := 118140960795 + 4079410 * 2 ^ 59
def prefixEnd_4079410 : Nat := 4983230072969 + 3 ^ 40 * 4079410 * 2
def baseEnd_4079410 : Nat := 2094698116757989523314141

theorem tailTrace_4079410 : CollatzResearch.WordTrace tailWord_4079410 prefixEnd_4079410 2094698116757989523314141 := by
  unfold tailWord_4079410
  simp only [CollatzResearch.WordTrace]
  refine ⟨37197076537750438151342921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99192204100667835070247789 37197076537750438151342921)
  ·
    refine ⟨27897807403312828613507191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37197076537750438151342921 27897807403312828613507191)
    ·
      refine ⟨41846711104969242920260787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27897807403312828613507191 41846711104969242920260787)
      ·
        refine ⟨62770066657453864380391181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41846711104969242920260787 62770066657453864380391181)
        ·
          refine ⟨23538774996545199142646693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62770066657453864380391181 23538774996545199142646693)
          ·
            refine ⟨4413520311852224839246255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23538774996545199142646693 4413520311852224839246255)
            ·
              refine ⟨6620280467778337258869383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4413520311852224839246255 6620280467778337258869383)
              ·
                refine ⟨9930420701667505888304075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6620280467778337258869383 9930420701667505888304075)
                ·
                  refine ⟨14895631052501258832456113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9930420701667505888304075 14895631052501258832456113)
                  ·
                    refine ⟨11171723289375944124342085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14895631052501258832456113 11171723289375944124342085)
                    ·
                      refine ⟨2094698116757989523314141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11171723289375944124342085 2094698116757989523314141)
                      ·
                        rfl

theorem cell23_4079410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_4079410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079410 prefixEnd_4079410 := by exact prefixLift 4079410
  have htrace : WordTrace (prefixWord ++ tailWord_4079410) baseStart_4079410 baseEnd_4079410 := by
    simpa [prefixWord, tailWord_4079410, baseEnd_4079410] using wordTrace_append hprefix tailTrace_4079410
  have hstable : (prefixWord ++ tailWord_4079410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079410).length < 2 ^ (prefixWord ++ tailWord_4079410).sum := by decide
  have hdescent : baseEnd_4079410 < baseStart_4079410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079414 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4079414 : Nat := 118140960795 + 4079414 * 2 ^ 59
def prefixEnd_4079414 : Nat := 4983230072969 + 3 ^ 40 * 4079414 * 2
def baseEnd_4079414 : Nat := 2094700170680607507664123

theorem tailTrace_4079414 : CollatzResearch.WordTrace tailWord_4079414 prefixEnd_4079414 2094700170680607507664123 := by
  unfold tailWord_4079414
  simp only [CollatzResearch.WordTrace]
  refine ⟨9299278252686703830532331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99192301361991507525678197 9299278252686703830532331)
  ·
    refine ⟨13948917379030055745798497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9299278252686703830532331 13948917379030055745798497)
    ·
      refine ⟨10461688034272541809348873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13948917379030055745798497 10461688034272541809348873)
      ·
        refine ⟨7846266025704406357011655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10461688034272541809348873 7846266025704406357011655)
        ·
          refine ⟨11769399038556609535517483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846266025704406357011655 11769399038556609535517483)
          ·
            refine ⟨17654098557834914303276225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11769399038556609535517483 17654098557834914303276225)
            ·
              refine ⟨13240573918376185727457169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17654098557834914303276225 13240573918376185727457169)
              ·
                refine ⟨9930430438782139295592877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13240573918376185727457169 9930430438782139295592877)
                ·
                  refine ⟨3723911414543302235847329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9930430438782139295592877 3723911414543302235847329)
                  ·
                    refine ⟨2792933560907476676885497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3723911414543302235847329 2792933560907476676885497)
                    ·
                      refine ⟨2094700170680607507664123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2792933560907476676885497 2094700170680607507664123)
                      ·
                        rfl

theorem cell23_4079414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4079414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079414 prefixEnd_4079414 := by exact prefixLift 4079414
  have htrace : WordTrace (prefixWord ++ tailWord_4079414) baseStart_4079414 baseEnd_4079414 := by
    simpa [prefixWord, tailWord_4079414, baseEnd_4079414] using wordTrace_append hprefix tailTrace_4079414
  have hstable : (prefixWord ++ tailWord_4079414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079414).length < 2 ^ (prefixWord ++ tailWord_4079414).sum := by decide
  have hdescent : baseEnd_4079414 < baseStart_4079414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079614 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4079614 : Nat := 118140960795 + 4079614 * 2 ^ 59
def prefixEnd_4079614 : Nat := 4983230072969 + 3 ^ 40 * 4079614 * 2
def baseEnd_4079614 : Nat := 2094802866811506725163203

theorem tailTrace_4079614 : CollatzResearch.WordTrace tailWord_4079614 prefixEnd_4079614 2094802866811506725163203 := by
  unfold tailWord_4079614
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599468330282836930724737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99197164428175130297198597 18599468330282836930724737)
  ·
    refine ⟨13949601247712127698043553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18599468330282836930724737 13949601247712127698043553)
    ·
      refine ⟨10462200935784095773532665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13949601247712127698043553 10462200935784095773532665)
      ·
        refine ⟨7846650701838071830149499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10462200935784095773532665 7846650701838071830149499)
        ·
          refine ⟨11769976052757107745224249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7846650701838071830149499 11769976052757107745224249)
          ·
            refine ⟨8827482039567830808918187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11769976052757107745224249 8827482039567830808918187)
            ·
              refine ⟨13241223059351746213377281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827482039567830808918187 13241223059351746213377281)
              ·
                refine ⟨9930917294513809660032961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13241223059351746213377281 9930917294513809660032961)
                ·
                  refine ⟨7448187970885357245024721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9930917294513809660032961 7448187970885357245024721)
                  ·
                    refine ⟨5586140978164017933768541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448187970885357245024721 5586140978164017933768541)
                    ·
                      refine ⟨2094802866811506725163203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5586140978164017933768541 2094802866811506725163203)
                      ·
                        rfl

theorem cell23_4079614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4079614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079614 prefixEnd_4079614 := by exact prefixLift 4079614
  have htrace : WordTrace (prefixWord ++ tailWord_4079614) baseStart_4079614 baseEnd_4079614 := by
    simpa [prefixWord, tailWord_4079614, baseEnd_4079614] using wordTrace_append hprefix tailTrace_4079614
  have hstable : (prefixWord ++ tailWord_4079614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079614).length < 2 ^ (prefixWord ++ tailWord_4079614).sum := by decide
  have hdescent : baseEnd_4079614 < baseStart_4079614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079630 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 3, 5]
def baseStart_4079630 : Nat := 118140960795 + 4079630 * 2 ^ 59
def prefixEnd_4079630 : Nat := 4983230072969 + 3 ^ 40 * 4079630 * 2
def baseEnd_4079630 : Nat := 698270360833992887521043

theorem tailTrace_4079630 : CollatzResearch.WordTrace tailWord_4079630 prefixEnd_4079630 698270360833992887521043 := by
  unfold tailWord_4079630
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599541276275591272297543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99197553473469820118920229 18599541276275591272297543)
  ·
    refine ⟨27899311914413386908446315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18599541276275591272297543 27899311914413386908446315)
    ·
      refine ⟨41848967871620080362669473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27899311914413386908446315 41848967871620080362669473)
      ·
        refine ⟨31386725903715060272002105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41848967871620080362669473 31386725903715060272002105)
        ·
          refine ⟨23540044427786295204001579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31386725903715060272002105 23540044427786295204001579)
          ·
            refine ⟨35310066641679442806002369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23540044427786295204001579 35310066641679442806002369)
            ·
              refine ⟨26482549981259582104501777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35310066641679442806002369 26482549981259582104501777)
              ·
                refine ⟨19861912485944686578376333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26482549981259582104501777 19861912485944686578376333)
                ·
                  refine ⟨7448217182229257466891125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19861912485944686578376333 7448217182229257466891125)
                  ·
                    refine ⟨698270360833992887521043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7448217182229257466891125 698270360833992887521043)
                    ·
                      rfl

theorem cell23_4079630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_4079630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079630 prefixEnd_4079630 := by exact prefixLift 4079630
  have htrace : WordTrace (prefixWord ++ tailWord_4079630) baseStart_4079630 baseEnd_4079630 := by
    simpa [prefixWord, tailWord_4079630, baseEnd_4079630] using wordTrace_append hprefix tailTrace_4079630
  have hstable : (prefixWord ++ tailWord_4079630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079630).length < 2 ^ (prefixWord ++ tailWord_4079630).sum := by decide
  have hdescent : baseEnd_4079630 < baseStart_4079630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079633 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 4]
def baseStart_4079633 : Nat := 118140960795 + 4079633 * 2 ^ 59
def prefixEnd_4079633 : Nat := 4983230072969 + 3 ^ 40 * 4079633 * 2
def baseEnd_4079633 : Nat := 2094812622943942150825615

theorem tailTrace_4079633 : CollatzResearch.WordTrace tailWord_4079633 prefixEnd_4079633 2094812622943942150825615 := by
  unfold tailWord_4079633
  simp only [CollatzResearch.WordTrace]
  refine ⟨148796439629193861690739553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99197626419462574460493035 148796439629193861690739553)
  ·
    refine ⟨111597329721895396268054665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148796439629193861690739553 111597329721895396268054665)
    ·
      refine ⟨83697997291421547201040999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111597329721895396268054665 83697997291421547201040999)
      ·
        refine ⟨125546995937132320801561499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83697997291421547201040999 125546995937132320801561499)
        ·
          refine ⟨188320493905698481202342249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125546995937132320801561499 188320493905698481202342249)
          ·
            refine ⟨141240370429273860901756687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188320493905698481202342249 141240370429273860901756687)
            ·
              refine ⟨211860555643910791352635031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 141240370429273860901756687 211860555643910791352635031)
              ·
                refine ⟨317790833465866187028952547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211860555643910791352635031 317790833465866187028952547)
                ·
                  refine ⟨476686250198799280543428821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 317790833465866187028952547 476686250198799280543428821)
                  ·
                    refine ⟨11172333989034358137736613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 476686250198799280543428821 11172333989034358137736613)
                    ·
                      refine ⟨2094812622943942150825615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11172333989034358137736613 2094812622943942150825615)
                      ·
                        rfl

theorem cell23_4079633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 4].length) (baseStart_4079633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079633 prefixEnd_4079633 := by exact prefixLift 4079633
  have htrace : WordTrace (prefixWord ++ tailWord_4079633) baseStart_4079633 baseEnd_4079633 := by
    simpa [prefixWord, tailWord_4079633, baseEnd_4079633] using wordTrace_append hprefix tailTrace_4079633
  have hstable : (prefixWord ++ tailWord_4079633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079633).length < 2 ^ (prefixWord ++ tailWord_4079633).sum := by decide
  have hdescent : baseEnd_4079633 < baseStart_4079633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079660 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 4, 4]
def baseStart_4079660 : Nat := 118140960795 + 4079660 * 2 ^ 59
def prefixEnd_4079660 : Nat := 4983230072969 + 3 ^ 40 * 4079660 * 2
def baseEnd_4079660 : Nat := 698275495640537848395997

theorem tailTrace_4079660 : CollatzResearch.WordTrace tailWord_4079660 prefixEnd_4079660 698275495640537848395997 := by
  unfold tailWord_4079660
  simp only [CollatzResearch.WordTrace]
  refine ⟨74398712200048022650986217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99198282933397363534648289 74398712200048022650986217)
  ·
    refine ⟨55799034150036016988239663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74398712200048022650986217 55799034150036016988239663)
    ·
      refine ⟨83698551225054025482359495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55799034150036016988239663 83698551225054025482359495)
      ·
        refine ⟨125547826837581038223539243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83698551225054025482359495 125547826837581038223539243)
        ·
          refine ⟨188321740256371557335308865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125547826837581038223539243 188321740256371557335308865)
          ·
            refine ⟨141241305192278668001481649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188321740256371557335308865 141241305192278668001481649)
            ·
              refine ⟨105930978894209001001111237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141241305192278668001481649 105930978894209001001111237)
              ·
                refine ⟨19862058542664187687708357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105930978894209001001111237 19862058542664187687708357)
                ·
                  refine ⟨3724135976749535191445317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19862058542664187687708357 3724135976749535191445317)
                  ·
                    refine ⟨698275495640537848395997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3724135976749535191445317 698275495640537848395997)
                    ·
                      rfl

theorem cell23_4079660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 4].length) (baseStart_4079660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079660 prefixEnd_4079660 := by exact prefixLift 4079660
  have htrace : WordTrace (prefixWord ++ tailWord_4079660) baseStart_4079660 baseEnd_4079660 := by
    simpa [prefixWord, tailWord_4079660, baseEnd_4079660] using wordTrace_append hprefix tailTrace_4079660
  have hstable : (prefixWord ++ tailWord_4079660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079660).length < 2 ^ (prefixWord ++ tailWord_4079660).sum := by decide
  have hdescent : baseEnd_4079660 < baseStart_4079660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079663 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 6]
def baseStart_4079663 : Nat := 118140960795 + 4079663 * 2 ^ 59
def prefixEnd_4079663 : Nat := 4983230072969 + 3 ^ 40 * 4079663 * 2
def baseEnd_4079663 : Nat := 2094828027363577033450477

theorem tailTrace_4079663 : CollatzResearch.WordTrace tailWord_4079663 prefixEnd_4079663 2094828027363577033450477 := by
  unfold tailWord_4079663
  simp only [CollatzResearch.WordTrace]
  refine ⟨148797533819085176814331643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99198355879390117876221095 148797533819085176814331643)
  ·
    refine ⟨223196300728627765221497465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148797533819085176814331643 223196300728627765221497465)
    ·
      refine ⟨167397225546470823916123099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223196300728627765221497465 167397225546470823916123099)
      ·
        refine ⟨251095838319706235874184649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167397225546470823916123099 251095838319706235874184649)
        ·
          refine ⟨188321878739779676905638487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251095838319706235874184649 188321878739779676905638487)
          ·
            refine ⟨282482818109669515358457731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188321878739779676905638487 282482818109669515358457731)
            ·
              refine ⟨423724227164504273037686597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282482818109669515358457731 423724227164504273037686597)
              ·
                refine ⟨79448292593344551194566237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 423724227164504273037686597 79448292593344551194566237)
                ·
                  refine ⟨29793109722504206697962339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79448292593344551194566237 29793109722504206697962339)
                  ·
                    refine ⟨44689664583756310046943509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29793109722504206697962339 44689664583756310046943509)
                    ·
                      refine ⟨2094828027363577033450477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44689664583756310046943509 2094828027363577033450477)
                      ·
                        rfl

theorem cell23_4079663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 6].length) (baseStart_4079663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079663 prefixEnd_4079663 := by exact prefixLift 4079663
  have htrace : WordTrace (prefixWord ++ tailWord_4079663) baseStart_4079663 baseEnd_4079663 := by
    simpa [prefixWord, tailWord_4079663, baseEnd_4079663] using wordTrace_append hprefix tailTrace_4079663
  have hstable : (prefixWord ++ tailWord_4079663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079663).length < 2 ^ (prefixWord ++ tailWord_4079663).sum := by decide
  have hdescent : baseEnd_4079663 < baseStart_4079663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079673 : List Nat := [1, 2, 1, 5, 14]
def baseStart_4079673 : Nat := 118140960795 + 4079673 * 2 ^ 59
def prefixEnd_4079673 : Nat := 4983230072969 + 3 ^ 40 * 4079673 * 2
def baseEnd_4079673 : Nat := 2873570867174378593039

theorem tailTrace_4079673 : CollatzResearch.WordTrace tailWord_4079673 prefixEnd_4079673 2873570867174378593039 := by
  unfold tailWord_4079673
  simp only [CollatzResearch.WordTrace]
  refine ⟨148797898549048948522195673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99198599032699299014797115 148797898549048948522195673)
  ·
    refine ⟨111598423911786711391646755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148797898549048948522195673 111598423911786711391646755)
    ·
      refine ⟨167397635867680067087470133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111598423911786711391646755 167397635867680067087470133)
      ·
        refine ⟨15693528362595006289450325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167397635867680067087470133 15693528362595006289450325)
        ·
          refine ⟨2873570867174378593039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 15693528362595006289450325 2873570867174378593039)
          ·
            rfl

theorem cell23_4079673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 14].length) (baseStart_4079673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079673 prefixEnd_4079673 := by exact prefixLift 4079673
  have htrace : WordTrace (prefixWord ++ tailWord_4079673) baseStart_4079673 baseEnd_4079673 := by
    simpa [prefixWord, tailWord_4079673, baseEnd_4079673] using wordTrace_append hprefix tailTrace_4079673
  have hstable : (prefixWord ++ tailWord_4079673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079673).length < 2 ^ (prefixWord ++ tailWord_4079673).sum := by decide
  have hdescent : baseEnd_4079673 < baseStart_4079673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079678 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4079678 : Nat := 118140960795 + 4079678 * 2 ^ 59
def prefixEnd_4079678 : Nat := 4983230072969 + 3 ^ 40 * 4079678 * 2
def baseEnd_4079678 : Nat := 2094835729573394474762909

theorem tailTrace_4079678 : CollatzResearch.WordTrace tailWord_4079678 prefixEnd_4079678 2094835729573394474762909 := by
  unfold tailWord_4079678
  simp only [CollatzResearch.WordTrace]
  refine ⟨18599760114253854297015961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99198720609353889584085125 18599760114253854297015961)
  ·
    refine ⟨13949820085690390722761971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18599760114253854297015961 13949820085690390722761971)
    ·
      refine ⟨20924730128535586084142957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13949820085690390722761971 20924730128535586084142957)
      ·
        refine ⟨7846773798200844781553609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20924730128535586084142957 7846773798200844781553609)
        ·
          refine ⟨5885080348650633586165207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7846773798200844781553609 5885080348650633586165207)
          ·
            refine ⟨8827620522975950379247811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885080348650633586165207 8827620522975950379247811)
            ·
              refine ⟨13241430784463925568871717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827620522975950379247811 13241430784463925568871717)
              ·
                refine ⟨2482768272086986044163447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13241430784463925568871717 2482768272086986044163447)
                ·
                  refine ⟨3724152408130479066245171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2482768272086986044163447 3724152408130479066245171)
                  ·
                    refine ⟨5586228612195718599367757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3724152408130479066245171 5586228612195718599367757)
                    ·
                      refine ⟨2094835729573394474762909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5586228612195718599367757 2094835729573394474762909)
                      ·
                        rfl

theorem cell23_4079678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4079678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079678 prefixEnd_4079678 := by exact prefixLift 4079678
  have htrace : WordTrace (prefixWord ++ tailWord_4079678) baseStart_4079678 baseEnd_4079678 := by
    simpa [prefixWord, tailWord_4079678, baseEnd_4079678] using wordTrace_append hprefix tailTrace_4079678
  have hstable : (prefixWord ++ tailWord_4079678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079678).length < 2 ^ (prefixWord ++ tailWord_4079678).sum := by decide
  have hdescent : baseEnd_4079678 < baseStart_4079678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079683 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7]
def baseStart_4079683 : Nat := 118140960795 + 4079683 * 2 ^ 59
def prefixEnd_4079683 : Nat := 4983230072969 + 3 ^ 40 * 4079683 * 2
def baseEnd_4079683 : Nat := 2094838296976666955200385

theorem tailTrace_4079683 : CollatzResearch.WordTrace tailWord_4079683 prefixEnd_4079683 2094838296976666955200385 := by
  unfold tailWord_4079683
  simp only [CollatzResearch.WordTrace]
  refine ⟨148798263279012720230059703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99198842186008480153373135 148798263279012720230059703)
  ·
    refine ⟨223197394918519080345089555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148798263279012720230059703 223197394918519080345089555)
    ·
      refine ⟨334796092377778620517634333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223197394918519080345089555 334796092377778620517634333)
      ·
        refine ⟨125548534641666982694112875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334796092377778620517634333 125548534641666982694112875)
        ·
          refine ⟨188322801962500474041169313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125548534641666982694112875 188322801962500474041169313)
          ·
            refine ⟨141242101471875355530876985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 188322801962500474041169313 141242101471875355530876985)
            ·
              refine ⟨105931576103906516648157739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 141242101471875355530876985 105931576103906516648157739)
              ·
                refine ⟨158897364155859774972236609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105931576103906516648157739 158897364155859774972236609)
                ·
                  refine ⟨119173023116894831229177457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158897364155859774972236609 119173023116894831229177457)
                  ·
                    refine ⟨89379767337671123421883093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 119173023116894831229177457 89379767337671123421883093)
                    ·
                      refine ⟨2094838296976666955200385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 89379767337671123421883093 2094838296976666955200385)
                      ·
                        rfl

theorem cell23_4079683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_4079683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079683 prefixEnd_4079683 := by exact prefixLift 4079683
  have htrace : WordTrace (prefixWord ++ tailWord_4079683) baseStart_4079683 baseEnd_4079683 := by
    simpa [prefixWord, tailWord_4079683, baseEnd_4079683] using wordTrace_append hprefix tailTrace_4079683
  have hstable : (prefixWord ++ tailWord_4079683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079683).length < 2 ^ (prefixWord ++ tailWord_4079683).sum := by decide
  have hdescent : baseEnd_4079683 < baseStart_4079683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079717 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 3]
def baseStart_4079717 : Nat := 118140960795 + 4079717 * 2 ^ 59
def prefixEnd_4079717 : Nat := 4983230072969 + 3 ^ 40 * 4079717 * 2
def baseEnd_4079717 : Nat := 2094855755318919822175229

theorem tailTrace_4079717 : CollatzResearch.WordTrace tailWord_4079717 prefixEnd_4079717 2094855755318919822175229 := by
  unfold tailWord_4079717
  simp only [CollatzResearch.WordTrace]
  refine ⟨148799503360889544036797405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99199668907259696024531603 148799503360889544036797405)
  ·
    refine ⟨55799813760333579013799027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148799503360889544036797405 55799813760333579013799027)
    ·
      refine ⟨83699720640500368520698541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55799813760333579013799027 83699720640500368520698541)
      ·
        refine ⟨31387395240187638195261953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83699720640500368520698541 31387395240187638195261953)
        ·
          refine ⟨23540546430140728646446465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31387395240187638195261953 23540546430140728646446465)
          ·
            refine ⟨17655409822605546484834849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23540546430140728646446465 17655409822605546484834849)
            ·
              refine ⟨13241557366954159863626137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17655409822605546484834849 13241557366954159863626137)
              ·
                refine ⟨9931168025215619897719603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13241557366954159863626137 9931168025215619897719603)
                ·
                  refine ⟨14896752037823429846579405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931168025215619897719603 14896752037823429846579405)
                  ·
                    refine ⟨5586282014183786192467277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14896752037823429846579405 5586282014183786192467277)
                    ·
                      refine ⟨2094855755318919822175229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5586282014183786192467277 2094855755318919822175229)
                      ·
                        rfl

theorem cell23_4079717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_4079717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079717 prefixEnd_4079717 := by exact prefixLift 4079717
  have htrace : WordTrace (prefixWord ++ tailWord_4079717) baseStart_4079717 baseEnd_4079717 := by
    simpa [prefixWord, tailWord_4079717, baseEnd_4079717] using wordTrace_append hprefix tailTrace_4079717
  have hstable : (prefixWord ++ tailWord_4079717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079717).length < 2 ^ (prefixWord ++ tailWord_4079717).sum := by decide
  have hdescent : baseEnd_4079717 < baseStart_4079717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079760 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_4079760 : Nat := 118140960795 + 4079760 * 2 ^ 59
def prefixEnd_4079760 : Nat := 4983230072969 + 3 ^ 40 * 4079760 * 2
def baseEnd_4079760 : Nat := 2094877834987063153937531

theorem tailTrace_4079760 : CollatzResearch.WordTrace tailWord_4079760 prefixEnd_4079760 2094877834987063153937531 := by
  unfold tailWord_4079760
  simp only [CollatzResearch.WordTrace]
  refine ⟨74400535849866881190306367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99200714466489174920408489 74400535849866881190306367)
  ·
    refine ⟨111600803774800321785459551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74400535849866881190306367 111600803774800321785459551)
    ·
      refine ⟨167401205662200482678189327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111600803774800321785459551 167401205662200482678189327)
      ·
        refine ⟨251101808493300724017283991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167401205662200482678189327 251101808493300724017283991)
        ·
          refine ⟨376652712739951086025925987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251101808493300724017283991 376652712739951086025925987)
          ·
            refine ⟨564979069109926629038888981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 376652712739951086025925987 564979069109926629038888981)
            ·
              refine ⟨26483393864527810736197921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 564979069109926629038888981 26483393864527810736197921)
              ·
                refine ⟨19862545398395858052148441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26483393864527810736197921 19862545398395858052148441)
                ·
                  refine ⟨14896909048796893539111331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19862545398395858052148441 14896909048796893539111331)
                  ·
                    refine ⟨22345363573195340308666997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14896909048796893539111331 22345363573195340308666997)
                    ·
                      refine ⟨2094877834987063153937531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22345363573195340308666997 2094877834987063153937531)
                      ·
                        rfl

theorem cell23_4079760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_4079760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079760 prefixEnd_4079760 := by exact prefixLift 4079760
  have htrace : WordTrace (prefixWord ++ tailWord_4079760) baseStart_4079760 baseEnd_4079760 := by
    simpa [prefixWord, tailWord_4079760, baseEnd_4079760] using wordTrace_append hprefix tailTrace_4079760
  have hstable : (prefixWord ++ tailWord_4079760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079760).length < 2 ^ (prefixWord ++ tailWord_4079760).sum := by decide
  have hdescent : baseEnd_4079760 < baseStart_4079760 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079777 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 5]
def baseStart_4079777 : Nat := 118140960795 + 4079777 * 2 ^ 59
def prefixEnd_4079777 : Nat := 4983230072969 + 3 ^ 40 * 4079777 * 2
def baseEnd_4079777 : Nat := 2094886564158189587424953

theorem tailTrace_4079777 : CollatzResearch.WordTrace tailWord_4079777 prefixEnd_4079777 2094886564158189587424953 := by
  unfold tailWord_4079777
  simp only [CollatzResearch.WordTrace]
  refine ⟨148801691740672174283981585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99201127827114782855987723 148801691740672174283981585)
  ·
    refine ⟨111601268805504130712986189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148801691740672174283981585 111601268805504130712986189)
    ·
      refine ⟨41850475802064049017369821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111601268805504130712986189 41850475802064049017369821)
      ·
        refine ⟨15693928425774018381513683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41850475802064049017369821 15693928425774018381513683)
        ·
          refine ⟨23540892638661027572270525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15693928425774018381513683 23540892638661027572270525)
          ·
            refine ⟨8827834739497885339601447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23540892638661027572270525 8827834739497885339601447)
            ·
              refine ⟨13241752109246828009402171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8827834739497885339601447 13241752109246828009402171)
              ·
                refine ⟨19862628163870242014103257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13241752109246828009402171 19862628163870242014103257)
                ·
                  refine ⟨14896971122902681510577443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19862628163870242014103257 14896971122902681510577443)
                  ·
                    refine ⟨22345456684354022265866165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14896971122902681510577443 22345456684354022265866165)
                    ·
                      refine ⟨2094886564158189587424953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22345456684354022265866165 2094886564158189587424953)
                      ·
                        rfl

theorem cell23_4079777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_4079777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079777 prefixEnd_4079777 := by exact prefixLift 4079777
  have htrace : WordTrace (prefixWord ++ tailWord_4079777) baseStart_4079777 baseEnd_4079777 := by
    simpa [prefixWord, tailWord_4079777, baseEnd_4079777] using wordTrace_append hprefix tailTrace_4079777
  have hstable : (prefixWord ++ tailWord_4079777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079777).length < 2 ^ (prefixWord ++ tailWord_4079777).sum := by decide
  have hdescent : baseEnd_4079777 < baseStart_4079777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079808 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 2, 2, 2]
def baseStart_4079808 : Nat := 118140960795 + 4079808 * 2 ^ 59
def prefixEnd_4079808 : Nat := 4983230072969 + 3 ^ 40 * 4079808 * 2
def baseEnd_4079808 : Nat := 2094902482058478966137311

theorem tailTrace_4079808 : CollatzResearch.WordTrace tailWord_4079808 prefixEnd_4079808 2094902482058478966137311 := by
  unfold tailWord_4079808
  simp only [CollatzResearch.WordTrace]
  refine ⟨74401411201779933289180039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99201881602373244385573385 74401411201779933289180039)
  ·
    refine ⟨111602116802669899933770059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74401411201779933289180039 111602116802669899933770059)
    ·
      refine ⟨167403175204004849900655089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111602116802669899933770059 167403175204004849900655089)
      ·
        refine ⟨125552381403003637425491317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167403175204004849900655089 125552381403003637425491317)
        ·
          refine ⟨11770535756531591008639811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125552381403003637425491317 11770535756531591008639811)
          ·
            refine ⟨17655803634797386512959717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11770535756531591008639811 17655803634797386512959717)
            ·
              refine ⟨3310463181524509971179947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17655803634797386512959717 3310463181524509971179947)
              ·
                refine ⟨4965694772286764956769921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310463181524509971179947 4965694772286764956769921)
                ·
                  refine ⟨3724271079215073717577441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965694772286764956769921 3724271079215073717577441)
                  ·
                    refine ⟨2793203309411305288183081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3724271079215073717577441 2793203309411305288183081)
                    ·
                      refine ⟨2094902482058478966137311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793203309411305288183081 2094902482058478966137311)
                      ·
                        rfl

theorem cell23_4079808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 2, 2, 2].length) (baseStart_4079808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079808 prefixEnd_4079808 := by exact prefixLift 4079808
  have htrace : WordTrace (prefixWord ++ tailWord_4079808) baseStart_4079808 baseEnd_4079808 := by
    simpa [prefixWord, tailWord_4079808, baseEnd_4079808] using wordTrace_append hprefix tailTrace_4079808
  have hstable : (prefixWord ++ tailWord_4079808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079808).length < 2 ^ (prefixWord ++ tailWord_4079808).sum := by decide
  have hdescent : baseEnd_4079808 < baseStart_4079808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079817 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 4, 5, 2]
def baseStart_4079817 : Nat := 118140960795 + 4079817 * 2 ^ 59
def prefixEnd_4079817 : Nat := 4983230072969 + 3 ^ 40 * 4079817 * 2
def baseEnd_4079817 : Nat := 2094907103384369430924769

theorem tailTrace_4079817 : CollatzResearch.WordTrace tailWord_4079817 prefixEnd_4079817 2094907103384369430924769 := by
  unfold tailWord_4079817
  simp only [CollatzResearch.WordTrace]
  refine ⟨148803150660527261115437705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99202100440351507410291803 148803150660527261115437705)
  ·
    refine ⟨111602362995395445836578279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148803150660527261115437705 111602362995395445836578279)
    ·
      refine ⟨167403544493093168754867419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111602362995395445836578279 167403544493093168754867419)
      ·
        refine ⟨251105316739639753132301129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167403544493093168754867419 251105316739639753132301129)
        ·
          refine ⟨188328987554729814849225847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251105316739639753132301129 188328987554729814849225847)
          ·
            refine ⟨282493481332094722273838771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188328987554729814849225847 282493481332094722273838771)
            ·
              refine ⟨423740221998142083410758157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 282493481332094722273838771 423740221998142083410758157)
              ·
                refine ⟨158902583249303281279034309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 423740221998142083410758157 158902583249303281279034309)
                ·
                  refine ⟨29794234359244365239818933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158902583249303281279034309 29794234359244365239818933)
                  ·
                    refine ⟨2793209471179159241233025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29794234359244365239818933 2793209471179159241233025)
                    ·
                      refine ⟨2094907103384369430924769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793209471179159241233025 2094907103384369430924769)
                      ·
                        rfl

theorem cell23_4079817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 5, 2].length) (baseStart_4079817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079817 prefixEnd_4079817 := by exact prefixLift 4079817
  have htrace : WordTrace (prefixWord ++ tailWord_4079817) baseStart_4079817 baseEnd_4079817 := by
    simpa [prefixWord, tailWord_4079817, baseEnd_4079817] using wordTrace_append hprefix tailTrace_4079817
  have hstable : (prefixWord ++ tailWord_4079817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079817).length < 2 ^ (prefixWord ++ tailWord_4079817).sum := by decide
  have hdescent : baseEnd_4079817 < baseStart_4079817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079904 : List Nat := [2, 1, 1, 5, 2, 1, 3, 2, 6]
def baseStart_4079904 : Nat := 118140960795 + 4079904 * 2 ^ 59
def prefixEnd_4079904 : Nat := 4983230072969 + 3 ^ 40 * 4079904 * 2
def baseEnd_4079904 : Nat := 232772419577923398948541

theorem tailTrace_4079904 : CollatzResearch.WordTrace tailWord_4079904 prefixEnd_4079904 232772419577923398948541 := by
  unfold tailWord_4079904
  simp only [CollatzResearch.WordTrace]
  refine ⟨74403161905606037486927383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99204215874141383315903177 74403161905606037486927383)
  ·
    refine ⟨111604742858409056230391075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74403161905606037486927383 111604742858409056230391075)
    ·
      refine ⟨167407114287613584345586613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111604742858409056230391075 167407114287613584345586613)
      ·
        refine ⟨15694416964463773532398745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167407114287613584345586613 15694416964463773532398745)
        ·
          refine ⟨11770812723347830149299059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15694416964463773532398745 11770812723347830149299059)
          ·
            refine ⟨17656219085021745223948589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11770812723347830149299059 17656219085021745223948589)
            ·
              refine ⟨6621082156883154458980721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17656219085021745223948589 6621082156883154458980721)
              ·
                refine ⟨4965811617662365844235541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621082156883154458980721 4965811617662365844235541)
                ·
                  refine ⟨232772419577923398948541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4965811617662365844235541 232772419577923398948541)
                  ·
                    rfl

theorem cell23_4079904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 2, 6].length) (baseStart_4079904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079904 prefixEnd_4079904 := by exact prefixLift 4079904
  have htrace : WordTrace (prefixWord ++ tailWord_4079904) baseStart_4079904 baseEnd_4079904 := by
    simpa [prefixWord, tailWord_4079904, baseEnd_4079904] using wordTrace_append hprefix tailTrace_4079904
  have hstable : (prefixWord ++ tailWord_4079904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079904).length < 2 ^ (prefixWord ++ tailWord_4079904).sum := by decide
  have hdescent : baseEnd_4079904 < baseStart_4079904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079921 : List Nat := [1, 2, 2, 3, 4, 1, 3, 1, 6]
def baseStart_4079921 : Nat := 118140960795 + 4079921 * 2 ^ 59
def prefixEnd_4079921 : Nat := 4983230072969 + 3 ^ 40 * 4079921 * 2
def baseEnd_4079921 : Nat := 232773389485826336002699

theorem tailTrace_4079921 : CollatzResearch.WordTrace tailWord_4079921 prefixEnd_4079921 232773389485826336002699 := by
  unfold tailWord_4079921
  simp only [CollatzResearch.WordTrace]
  refine ⟨148806943852150486877223617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99204629234766991251482411 148806943852150486877223617)
  ·
    refine ⟨111605207889112865157917713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148806943852150486877223617 111605207889112865157917713)
    ·
      refine ⟨83703905916834648868438285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111605207889112865157917713 83703905916834648868438285)
      ·
        refine ⟨31388964718812993325664357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83703905916834648868438285 31388964718812993325664357)
        ·
          refine ⟨5885430884777436248562067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31388964718812993325664357 5885430884777436248562067)
          ·
            refine ⟨8828146327166154372843101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885430884777436248562067 8828146327166154372843101)
            ·
              refine ⟨3310554872687307889816163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8828146327166154372843101 3310554872687307889816163)
              ·
                refine ⟨4965832309030961834724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310554872687307889816163 4965832309030961834724245)
                ·
                  refine ⟨232773389485826336002699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4965832309030961834724245 232773389485826336002699)
                  ·
                    rfl

theorem cell23_4079921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 1, 6].length) (baseStart_4079921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079921 prefixEnd_4079921 := by exact prefixLift 4079921
  have htrace : WordTrace (prefixWord ++ tailWord_4079921) baseStart_4079921 baseEnd_4079921 := by
    simpa [prefixWord, tailWord_4079921, baseEnd_4079921] using wordTrace_append hprefix tailTrace_4079921
  have hstable : (prefixWord ++ tailWord_4079921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079921).length < 2 ^ (prefixWord ++ tailWord_4079921).sum := by decide
  have hdescent : baseEnd_4079921 < baseStart_4079921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079967 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 6]
def baseStart_4079967 : Nat := 118140960795 + 4079967 * 2 ^ 59
def prefixEnd_4079967 : Nat := 4983230072969 + 3 ^ 40 * 4079967 * 2
def baseEnd_4079967 : Nat := 2094984125482543844049079

theorem tailTrace_4079967 : CollatzResearch.WordTrace tailWord_4079967 prefixEnd_4079967 2094984125482543844049079 := by
  unfold tailWord_4079967
  simp only [CollatzResearch.WordTrace]
  refine ⟨148808621609983836733398155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99205747739989224488932103 148808621609983836733398155)
  ·
    refine ⟨223212932414975755100097233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148808621609983836733398155 223212932414975755100097233)
    ·
      refine ⟨167409699311231816325072925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223212932414975755100097233 167409699311231816325072925)
      ·
        refine ⟨62778637241711931121902347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 167409699311231816325072925 62778637241711931121902347)
        ·
          refine ⟨94167955862567896682853521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62778637241711931121902347 94167955862567896682853521)
          ·
            refine ⟨70625966896925922512140141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 94167955862567896682853521 70625966896925922512140141)
            ·
              refine ⟨26484737586347220942052553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70625966896925922512140141 26484737586347220942052553)
              ·
                refine ⟨19863553189760415706539415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26484737586347220942052553 19863553189760415706539415)
                ·
                  refine ⟨29795329784640623559809123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19863553189760415706539415 29795329784640623559809123)
                  ·
                    refine ⟨44692994676960935339713685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29795329784640623559809123 44692994676960935339713685)
                    ·
                      refine ⟨2094984125482543844049079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44692994676960935339713685 2094984125482543844049079)
                      ·
                        rfl

theorem cell23_4079967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_4079967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079967 prefixEnd_4079967 := by exact prefixLift 4079967
  have htrace : WordTrace (prefixWord ++ tailWord_4079967) baseStart_4079967 baseEnd_4079967 := by
    simpa [prefixWord, tailWord_4079967, baseEnd_4079967] using wordTrace_append hprefix tailTrace_4079967
  have hstable : (prefixWord ++ tailWord_4079967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079967).length < 2 ^ (prefixWord ++ tailWord_4079967).sum := by decide
  have hdescent : baseEnd_4079967 < baseStart_4079967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079977 : List Nat := [1, 2, 1, 1, 1, 3, 6, 8]
def baseStart_4079977 : Nat := 118140960795 + 4079977 * 2 ^ 59
def prefixEnd_4079977 : Nat := 4983230072969 + 3 ^ 40 * 4079977 * 2
def baseEnd_4079977 : Nat := 77592194825521807589779

theorem tailTrace_4079977 : CollatzResearch.WordTrace tailWord_4079977 prefixEnd_4079977 77592194825521807589779 := by
  unfold tailWord_4079977
  simp only [CollatzResearch.WordTrace]
  refine ⟨148808986339947608441262185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99205990893298405627508123 148808986339947608441262185)
  ·
    refine ⟨111606739754960706330946639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148808986339947608441262185 111606739754960706330946639)
    ·
      refine ⟨167410109632441059496419959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111606739754960706330946639 167410109632441059496419959)
      ·
        refine ⟨251115164448661589244629939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167410109632441059496419959 251115164448661589244629939)
        ·
          refine ⟨376672746672992383866944909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251115164448661589244629939 376672746672992383866944909)
          ·
            refine ⟨141252280002372143950104341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 376672746672992383866944909 141252280002372143950104341)
            ·
              refine ⟨6621200625111194247661141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 141252280002372143950104341 6621200625111194247661141)
              ·
                refine ⟨77592194825521807589779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6621200625111194247661141 77592194825521807589779)
                ·
                  rfl

theorem cell23_4079977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 8].length) (baseStart_4079977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079977 prefixEnd_4079977 := by exact prefixLift 4079977
  have htrace : WordTrace (prefixWord ++ tailWord_4079977) baseStart_4079977 baseEnd_4079977 := by
    simpa [prefixWord, tailWord_4079977, baseEnd_4079977] using wordTrace_append hprefix tailTrace_4079977
  have hstable : (prefixWord ++ tailWord_4079977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079977).length < 2 ^ (prefixWord ++ tailWord_4079977).sum := by decide
  have hdescent : baseEnd_4079977 < baseStart_4079977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4079981 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 2, 4]
def baseStart_4079981 : Nat := 118140960795 + 4079981 * 2 ^ 59
def prefixEnd_4079981 : Nat := 4983230072969 + 3 ^ 40 * 4079981 * 2
def baseEnd_4079981 : Nat := 698330438070568929758005

theorem tailTrace_4079981 : CollatzResearch.WordTrace tailWord_4079981 prefixEnd_4079981 698330438070568929758005 := by
  unfold tailWord_4079981
  simp only [CollatzResearch.WordTrace]
  refine ⟨148809132231933117124407797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99206088154622078082938531 148809132231933117124407797)
  ·
    refine ⟨13950856146743729730413231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148809132231933117124407797 13950856146743729730413231)
    ·
      refine ⟨20926284220115594595619847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13950856146743729730413231 20926284220115594595619847)
      ·
        refine ⟨31389426330173391893429771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20926284220115594595619847 31389426330173391893429771)
        ·
          refine ⟨47084139495260087840144657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31389426330173391893429771 47084139495260087840144657)
          ·
            refine ⟨35313104621445065880108493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47084139495260087840144657 35313104621445065880108493)
            ·
              refine ⟨13242414233041899705040685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35313104621445065880108493 13242414233041899705040685)
              ·
                refine ⟨4965905337390712389390257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13242414233041899705040685 4965905337390712389390257)
                ·
                  refine ⟨3724429003043034292042693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4965905337390712389390257 3724429003043034292042693)
                  ·
                    refine ⟨698330438070568929758005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3724429003043034292042693 698330438070568929758005)
                    ·
                      rfl

theorem cell23_4079981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_4079981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4079981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4079981 prefixEnd_4079981 := by exact prefixLift 4079981
  have htrace : WordTrace (prefixWord ++ tailWord_4079981) baseStart_4079981 baseEnd_4079981 := by
    simpa [prefixWord, tailWord_4079981, baseEnd_4079981] using wordTrace_append hprefix tailTrace_4079981
  have hstable : (prefixWord ++ tailWord_4079981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4079981).length < 2 ^ (prefixWord ++ tailWord_4079981).sum := by decide
  have hdescent : baseEnd_4079981 < baseStart_4079981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4079981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080001 : List Nat := [1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4080001 : Nat := 118140960795 + 4080001 * 2 ^ 59
def prefixEnd_4080001 : Nat := 4983230072969 + 3 ^ 40 * 4080001 * 2
def baseEnd_4080001 : Nat := 2095001583824796711023923

theorem tailTrace_4080001 : CollatzResearch.WordTrace tailWord_4080001 prefixEnd_4080001 2095001583824796711023923 := by
  unfold tailWord_4080001
  simp only [CollatzResearch.WordTrace]
  refine ⟨148809861691860660540135857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99206574461240440360090571 148809861691860660540135857)
  ·
    refine ⟨111607396268895495405101893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148809861691860660540135857 111607396268895495405101893)
    ·
      refine ⟨20926386800417905388456605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111607396268895495405101893 20926386800417905388456605)
      ·
        refine ⟨7847395050156714520671227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20926386800417905388456605 7847395050156714520671227)
        ·
          refine ⟨11771092575235071781006841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847395050156714520671227 11771092575235071781006841)
          ·
            refine ⟨8828319431426303835755131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11771092575235071781006841 8828319431426303835755131)
            ·
              refine ⟨13242479147139455753632697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8828319431426303835755131 13242479147139455753632697)
              ·
                refine ⟨9931859360354591815224523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13242479147139455753632697 9931859360354591815224523)
                ·
                  refine ⟨14897789040531887722836785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9931859360354591815224523 14897789040531887722836785)
                  ·
                    refine ⟨11173341780398915792127589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14897789040531887722836785 11173341780398915792127589)
                    ·
                      refine ⟨2095001583824796711023923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11173341780398915792127589 2095001583824796711023923)
                      ·
                        rfl

theorem cell23_4080001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4080001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080001 prefixEnd_4080001 := by exact prefixLift 4080001
  have htrace : WordTrace (prefixWord ++ tailWord_4080001) baseStart_4080001 baseEnd_4080001 := by
    simpa [prefixWord, tailWord_4080001, baseEnd_4080001] using wordTrace_append hprefix tailTrace_4080001
  have hstable : (prefixWord ++ tailWord_4080001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080001).length < 2 ^ (prefixWord ++ tailWord_4080001).sum := by decide
  have hdescent : baseEnd_4080001 < baseStart_4080001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080008 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 1, 2, 3]
def baseStart_4080008 : Nat := 118140960795 + 4080008 * 2 ^ 59
def prefixEnd_4080008 : Nat := 4983230072969 + 3 ^ 40 * 4080008 * 2
def baseEnd_4080008 : Nat := 2095005178189378183636391

theorem tailTrace_4080008 : CollatzResearch.WordTrace tailWord_4080008 prefixEnd_4080008 2095005178189378183636391 := by
  unfold tailWord_4080008
  simp only [CollatzResearch.WordTrace]
  refine ⟨74405058501417650367820339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99206744668556867157093785 74405058501417650367820339)
  ·
    refine ⟨111607587752126475551730509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74405058501417650367820339 111607587752126475551730509)
    ·
      refine ⟨41852845407047428331898941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111607587752126475551730509 41852845407047428331898941)
      ·
        refine ⟨15694817027642785624462103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41852845407047428331898941 15694817027642785624462103)
        ·
          refine ⟨23542225541464178436693155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694817027642785624462103 23542225541464178436693155)
          ·
            refine ⟨35313338312196267655039733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542225541464178436693155 35313338312196267655039733)
            ·
              refine ⟨3310625466768400092659975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35313338312196267655039733 3310625466768400092659975)
              ·
                refine ⟨4965938200152600138989963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3310625466768400092659975 4965938200152600138989963)
                ·
                  refine ⟨7448907300228900208484945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4965938200152600138989963 7448907300228900208484945)
                  ·
                    refine ⟨5586680475171675156363709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7448907300228900208484945 5586680475171675156363709)
                    ·
                      refine ⟨2095005178189378183636391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5586680475171675156363709 2095005178189378183636391)
                      ·
                        rfl

theorem cell23_4080008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_4080008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080008 prefixEnd_4080008 := by exact prefixLift 4080008
  have htrace : WordTrace (prefixWord ++ tailWord_4080008) baseStart_4080008 baseEnd_4080008 := by
    simpa [prefixWord, tailWord_4080008, baseEnd_4080008] using wordTrace_append hprefix tailTrace_4080008
  have hstable : (prefixWord ++ tailWord_4080008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080008).length < 2 ^ (prefixWord ++ tailWord_4080008).sum := by decide
  have hdescent : baseEnd_4080008 < baseStart_4080008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080024 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 2, 7]
def baseStart_4080024 : Nat := 118140960795 + 4080024 * 2 ^ 59
def prefixEnd_4080024 : Nat := 4983230072969 + 3 ^ 40 * 4080024 * 2
def baseEnd_4080024 : Nat := 698337797959950040345439

theorem tailTrace_4080024 : CollatzResearch.WordTrace tailWord_4080024 prefixEnd_4080024 698337797959950040345439 := by
  unfold tailWord_4080024
  simp only [CollatzResearch.WordTrace]
  refine ⟨74405350285388667734111563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99207133713851556978815417 74405350285388667734111563)
  ·
    refine ⟨111608025428083001601167345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74405350285388667734111563 111608025428083001601167345)
    ·
      refine ⟨83706019071062251200875509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111608025428083001601167345 83706019071062251200875509)
      ·
        refine ⟨7847439287912086050082079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83706019071062251200875509 7847439287912086050082079)
        ·
          refine ⟨11771158931868129075123119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847439287912086050082079 11771158931868129075123119)
          ·
            refine ⟨17656738397802193612684679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771158931868129075123119 17656738397802193612684679)
            ·
              refine ⟨26485107596703290419027019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17656738397802193612684679 26485107596703290419027019)
              ·
                refine ⟨39727661395054935628540529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26485107596703290419027019 39727661395054935628540529)
                ·
                  refine ⟨29795746046291201721405397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39727661395054935628540529 29795746046291201721405397)
                  ·
                    refine ⟨698337797959950040345439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 29795746046291201721405397 698337797959950040345439)
                    ·
                      rfl

theorem cell23_4080024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_4080024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080024 prefixEnd_4080024 := by exact prefixLift 4080024
  have htrace : WordTrace (prefixWord ++ tailWord_4080024) baseStart_4080024 baseEnd_4080024 := by
    simpa [prefixWord, tailWord_4080024, baseEnd_4080024] using wordTrace_append hprefix tailTrace_4080024
  have hstable : (prefixWord ++ tailWord_4080024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080024).length < 2 ^ (prefixWord ++ tailWord_4080024).sum := by decide
  have hdescent : baseEnd_4080024 < baseStart_4080024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080031 : List Nat := [1, 1, 2, 5, 1, 1, 1, 1, 5, 3, 2]
def baseStart_4080031 : Nat := 118140960795 + 4080031 * 2 ^ 59
def prefixEnd_4080031 : Nat := 4983230072969 + 3 ^ 40 * 4080031 * 2
def baseEnd_4080031 : Nat := 2095016988244431593648785

theorem tailTrace_4080031 : CollatzResearch.WordTrace tailWord_4080031 prefixEnd_4080031 2095016988244431593648785 := by
  unfold tailWord_4080031
  simp only [CollatzResearch.WordTrace]
  refine ⟨148810955881751975663727947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99207303921167983775818631 148810955881751975663727947)
  ·
    refine ⟨223216433822627963495591921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148810955881751975663727947 223216433822627963495591921)
    ·
      refine ⟨167412325366970972621693941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223216433822627963495591921 167412325366970972621693941)
      ·
        refine ⟨15694905503153528683283807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 167412325366970972621693941 15694905503153528683283807)
        ·
          refine ⟨23542358254730293024925711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15694905503153528683283807 23542358254730293024925711)
          ·
            refine ⟨35313537382095439537388567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23542358254730293024925711 35313537382095439537388567)
            ·
              refine ⟨52970306073143159306082851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35313537382095439537388567 52970306073143159306082851)
              ·
                refine ⟨79455459109714738959124277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52970306073143159306082851 79455459109714738959124277)
                ·
                  refine ⟨7448949291535756777417901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79455459109714738959124277 7448949291535756777417901)
                  ·
                    refine ⟨2793355984325908791531713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7448949291535756777417901 2793355984325908791531713)
                    ·
                      refine ⟨2095016988244431593648785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793355984325908791531713 2095016988244431593648785)
                      ·
                        rfl

theorem cell23_4080031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_4080031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080031 prefixEnd_4080031 := by exact prefixLift 4080031
  have htrace : WordTrace (prefixWord ++ tailWord_4080031) baseStart_4080031 baseEnd_4080031 := by
    simpa [prefixWord, tailWord_4080031, baseEnd_4080031] using wordTrace_append hprefix tailTrace_4080031
  have hstable : (prefixWord ++ tailWord_4080031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080031).length < 2 ^ (prefixWord ++ tailWord_4080031).sum := by decide
  have hdescent : baseEnd_4080031 < baseStart_4080031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080067 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 11]
def baseStart_4080067 : Nat := 118140960795 + 4080067 * 2 ^ 59
def prefixEnd_4080067 : Nat := 4983230072969 + 3 ^ 40 * 4080067 * 2
def baseEnd_4080067 : Nat := 232781719283110383644291

theorem tailTrace_4080067 : CollatzResearch.WordTrace tailWord_4080067 prefixEnd_4080067 232781719283110383644291 := by
  unfold tailWord_4080067
  simp only [CollatzResearch.WordTrace]
  refine ⟨148812268909621553812038455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99208179273081035874692303 148812268909621553812038455)
  ·
    refine ⟨223218403364432330718057683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148812268909621553812038455 223218403364432330718057683)
    ·
      refine ⟨334827605046648496077086525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223218403364432330718057683 334827605046648496077086525)
      ·
        refine ⟨125560351892493186028907447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 334827605046648496077086525 125560351892493186028907447)
        ·
          refine ⟨188340527838739779043361171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125560351892493186028907447 188340527838739779043361171)
          ·
            refine ⟨282510791758109668565041757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188340527838739779043361171 282510791758109668565041757)
            ·
              refine ⟨105941546909291125711890659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282510791758109668565041757 105941546909291125711890659)
              ·
                refine ⟨158912320363936688567835989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105941546909291125711890659 158912320363936688567835989)
                ·
                  refine ⟨232781719283110383644291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 158912320363936688567835989 232781719283110383644291)
                  ·
                    rfl

theorem cell23_4080067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 11].length) (baseStart_4080067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080067 prefixEnd_4080067 := by exact prefixLift 4080067
  have htrace : WordTrace (prefixWord ++ tailWord_4080067) baseStart_4080067 baseEnd_4080067 := by
    simpa [prefixWord, tailWord_4080067, baseEnd_4080067] using wordTrace_append hprefix tailTrace_4080067
  have hstable : (prefixWord ++ tailWord_4080067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080067).length < 2 ^ (prefixWord ++ tailWord_4080067).sum := by decide
  have hdescent : baseEnd_4080067 < baseStart_4080067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080074 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4]
def baseStart_4080074 : Nat := 118140960795 + 4080074 * 2 ^ 59
def prefixEnd_4080074 : Nat := 4983230072969 + 3 ^ 40 * 4080074 * 2
def baseEnd_4080074 : Nat := 2095039067912574925411087

theorem tailTrace_4080074 : CollatzResearch.WordTrace tailWord_4080074 prefixEnd_4080074 2095039067912574925411087 := by
  unfold tailWord_4080074
  simp only [CollatzResearch.WordTrace]
  refine ⟨37203131055149048501885819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99208349480397462671695517 37203131055149048501885819)
  ·
    refine ⟨55804696582723572752828729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37203131055149048501885819 55804696582723572752828729)
    ·
      refine ⟨41853522437042679564621547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55804696582723572752828729 41853522437042679564621547)
      ·
        refine ⟨62780283655564019346932321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41853522437042679564621547 62780283655564019346932321)
        ·
          refine ⟨47085212741673014510199241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62780283655564019346932321 47085212741673014510199241)
          ·
            refine ⟨35313909556254760882649431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47085212741673014510199241 35313909556254760882649431)
            ·
              refine ⟨52970864334382141323974147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35313909556254760882649431 52970864334382141323974147)
              ·
                refine ⟨79456296501573211985961221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52970864334382141323974147 79456296501573211985961221)
                ·
                  refine ⟨14898055594044977247367729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79456296501573211985961221 14898055594044977247367729)
                  ·
                    refine ⟨11173541695533732935525797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14898055594044977247367729 11173541695533732935525797)
                    ·
                      refine ⟨2095039067912574925411087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11173541695533732935525797 2095039067912574925411087)
                      ·
                        rfl

theorem cell23_4080074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_4080074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080074 prefixEnd_4080074 := by exact prefixLift 4080074
  have htrace : WordTrace (prefixWord ++ tailWord_4080074) baseStart_4080074 baseEnd_4080074 := by
    simpa [prefixWord, tailWord_4080074, baseEnd_4080074] using wordTrace_append hprefix tailTrace_4080074
  have hstable : (prefixWord ++ tailWord_4080074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080074).length < 2 ^ (prefixWord ++ tailWord_4080074).sum := by decide
  have hdescent : baseEnd_4080074 < baseStart_4080074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080124 : List Nat := [2, 2, 2, 1, 2, 1, 1, 4, 1, 2, 5]
def baseStart_4080124 : Nat := 118140960795 + 4080124 * 2 ^ 59
def prefixEnd_4080124 : Nat := 4983230072969 + 3 ^ 40 * 4080124 * 2
def baseEnd_4080124 : Nat := 2095064741945299729785857

theorem tailTrace_4080124 : CollatzResearch.WordTrace tailWord_4080124 prefixEnd_4080124 2095064741945299729785857 := by
  unfold tailWord_4080124
  simp only [CollatzResearch.WordTrace]
  refine ⟨74407173935207526273431713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99209565246943368364575617 74407173935207526273431713)
  ·
    refine ⟨55805380451405644705073785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74407173935207526273431713 55805380451405644705073785)
    ·
      refine ⟨41854035338554233528805339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55805380451405644705073785 41854035338554233528805339)
      ·
        refine ⟨62781053007831350293208009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41854035338554233528805339 62781053007831350293208009)
        ·
          refine ⟨47085789755873512719906007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62781053007831350293208009 47085789755873512719906007)
          ·
            refine ⟨70628684633810269079859011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47085789755873512719906007 70628684633810269079859011)
            ·
              refine ⟨105943026950715403619788517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70628684633810269079859011 105943026950715403619788517)
              ·
                refine ⟨19864317553259138178710347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105943026950715403619788517 19864317553259138178710347)
                ·
                  refine ⟨29796476329888707268065521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19864317553259138178710347 29796476329888707268065521)
                  ·
                    refine ⟨22347357247416530451049141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29796476329888707268065521 22347357247416530451049141)
                    ·
                      refine ⟨2095064741945299729785857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22347357247416530451049141 2095064741945299729785857)
                      ·
                        rfl

theorem cell23_4080124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 4, 1, 2, 5].length) (baseStart_4080124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080124 prefixEnd_4080124 := by exact prefixLift 4080124
  have htrace : WordTrace (prefixWord ++ tailWord_4080124) baseStart_4080124 baseEnd_4080124 := by
    simpa [prefixWord, tailWord_4080124, baseEnd_4080124] using wordTrace_append hprefix tailTrace_4080124
  have hstable : (prefixWord ++ tailWord_4080124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080124).length < 2 ^ (prefixWord ++ tailWord_4080124).sum := by decide
  have hdescent : baseEnd_4080124 < baseStart_4080124 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080135 : List Nat := [1, 1, 4, 3, 3, 1, 3, 2, 5]
def baseStart_4080135 : Nat := 118140960795 + 4080135 * 2 ^ 59
def prefixEnd_4080135 : Nat := 4983230072969 + 3 ^ 40 * 4080135 * 2
def baseEnd_4080135 : Nat := 232785598914722131860923

theorem tailTrace_4080135 : CollatzResearch.WordTrace tailWord_4080135 prefixEnd_4080135 232785598914722131860923 := by
  unfold tailWord_4080135
  simp only [CollatzResearch.WordTrace]
  refine ⟨148814749073375201425513859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99209832715583467617009239 148814749073375201425513859)
  ·
    refine ⟨223222123610062802138270789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148814749073375201425513859 223222123610062802138270789)
    ·
      refine ⟨41854148176886775400925773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 223222123610062802138270789 41854148176886775400925773)
      ·
        refine ⟨15695305566332540775347165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41854148176886775400925773 15695305566332540775347165)
        ·
          refine ⟨5885739587374702790755187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15695305566332540775347165 5885739587374702790755187)
          ·
            refine ⟨8828609381062054186132781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5885739587374702790755187 8828609381062054186132781)
            ·
              refine ⟨3310728517898270319799793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8828609381062054186132781 3310728517898270319799793)
              ·
                refine ⟨2483046388423702739849845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3310728517898270319799793 2483046388423702739849845)
                ·
                  refine ⟨232785598914722131860923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483046388423702739849845 232785598914722131860923)
                  ·
                    rfl

theorem cell23_4080135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 2, 5].length) (baseStart_4080135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080135 prefixEnd_4080135 := by exact prefixLift 4080135
  have htrace : WordTrace (prefixWord ++ tailWord_4080135) baseStart_4080135 baseEnd_4080135 := by
    simpa [prefixWord, tailWord_4080135, baseEnd_4080135] using wordTrace_append hprefix tailTrace_4080135
  have hstable : (prefixWord ++ tailWord_4080135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080135).length < 2 ^ (prefixWord ++ tailWord_4080135).sum := by decide
  have hdescent : baseEnd_4080135 < baseStart_4080135 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080161 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 5, 4]
def baseStart_4080161 : Nat := 118140960795 + 4080161 * 2 ^ 59
def prefixEnd_4080161 : Nat := 4983230072969 + 3 ^ 40 * 4080161 * 2
def baseEnd_4080161 : Nat := 698361246909838695007729

theorem tailTrace_4080161 : CollatzResearch.WordTrace tailWord_4080161 prefixEnd_4080161 698361246909838695007729 := by
  unfold tailWord_4080161
  simp only [CollatzResearch.WordTrace]
  refine ⟨148815697371281007865960337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99210464914187338577306891 148815697371281007865960337)
  ·
    refine ⟨111611773028460755899470253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148815697371281007865960337 111611773028460755899470253)
    ·
      refine ⟨41854414885672783462301345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111611773028460755899470253 41854414885672783462301345)
      ·
        refine ⟨31390811164254587596726009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41854414885672783462301345 31390811164254587596726009)
        ·
          refine ⟨23543108373190940697544507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31390811164254587596726009 23543108373190940697544507)
          ·
            refine ⟨35314662559786411046316761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23543108373190940697544507 35314662559786411046316761)
            ·
              refine ⟨26485996919839808284737571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35314662559786411046316761 26485996919839808284737571)
              ·
                refine ⟨39728995379759712427106357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26485996919839808284737571 39728995379759712427106357)
                ·
                  refine ⟨3724593316852473040041221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39728995379759712427106357 3724593316852473040041221)
                  ·
                    refine ⟨698361246909838695007729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3724593316852473040041221 698361246909838695007729)
                    ·
                      rfl

theorem cell23_4080161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 4].length) (baseStart_4080161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080161 prefixEnd_4080161 := by exact prefixLift 4080161
  have htrace : WordTrace (prefixWord ++ tailWord_4080161) baseStart_4080161 baseEnd_4080161 := by
    simpa [prefixWord, tailWord_4080161, baseEnd_4080161] using wordTrace_append hprefix tailTrace_4080161
  have hstable : (prefixWord ++ tailWord_4080161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080161).length < 2 ^ (prefixWord ++ tailWord_4080161).sum := by decide
  have hdescent : baseEnd_4080161 < baseStart_4080161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080168 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4080168 : Nat := 118140960795 + 4080168 * 2 ^ 59
def prefixEnd_4080168 : Nat := 4983230072969 + 3 ^ 40 * 4080168 * 2
def baseEnd_4080168 : Nat := 2095087335094097557635655

theorem tailTrace_4080168 : CollatzResearch.WordTrace tailWord_4080168 prefixEnd_4080168 2095087335094097557635655 := by
  unfold tailWord_4080168
  simp only [CollatzResearch.WordTrace]
  refine ⟨74407976341127824030732579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99210635121503765374310105 74407976341127824030732579)
  ·
    refine ⟨111611964511691736046098869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74407976341127824030732579 111611964511691736046098869)
    ·
      refine ⟨10463621672971100254321769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111611964511691736046098869 10463621672971100254321769)
      ·
        refine ⟨7847716254728325190741327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10463621672971100254321769 7847716254728325190741327)
        ·
          refine ⟨11771574382092487786111991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847716254728325190741327 11771574382092487786111991)
          ·
            refine ⟨17657361573138731679167987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771574382092487786111991 17657361573138731679167987)
            ·
              refine ⟨26486042359708097518751981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17657361573138731679167987 26486042359708097518751981)
              ·
                refine ⟨9932265884890536569531993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26486042359708097518751981 9932265884890536569531993)
                ·
                  refine ⟨7449199413667902427148995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932265884890536569531993 7449199413667902427148995)
                  ·
                    refine ⟨11173799120501853640723493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449199413667902427148995 11173799120501853640723493)
                    ·
                      refine ⟨2095087335094097557635655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11173799120501853640723493 2095087335094097557635655)
                      ·
                        rfl

theorem cell23_4080168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4080168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080168 prefixEnd_4080168 := by exact prefixLift 4080168
  have htrace : WordTrace (prefixWord ++ tailWord_4080168) baseStart_4080168 baseEnd_4080168 := by
    simpa [prefixWord, tailWord_4080168, baseEnd_4080168] using wordTrace_append hprefix tailTrace_4080168
  have hstable : (prefixWord ++ tailWord_4080168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080168).length < 2 ^ (prefixWord ++ tailWord_4080168).sum := by decide
  have hdescent : baseEnd_4080168 < baseStart_4080168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080188 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 3]
def baseStart_4080188 : Nat := 118140960795 + 4080188 * 2 ^ 59
def prefixEnd_4080188 : Nat := 4983230072969 + 3 ^ 40 * 4080188 * 2
def baseEnd_4080188 : Nat := 2095097604707187479385563

theorem tailTrace_4080188 : CollatzResearch.WordTrace tailWord_4080188 prefixEnd_4080188 2095097604707187479385563 := by
  unfold tailWord_4080188
  simp only [CollatzResearch.WordTrace]
  refine ⟨74408341071091595738596609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99211121428122127651462145 74408341071091595738596609)
  ·
    refine ⟨55806255803318696803947457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74408341071091595738596609 55806255803318696803947457)
    ·
      refine ⟨41854691852489022602960593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55806255803318696803947457 41854691852489022602960593)
      ·
        refine ⟨31391018889366766952220445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41854691852489022602960593 31391018889366766952220445)
        ·
          refine ⟨11771632083512537607082667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31391018889366766952220445 11771632083512537607082667)
          ·
            refine ⟨17657448125268806410624001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11771632083512537607082667 17657448125268806410624001)
            ·
              refine ⟨13243086093951604807968001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17657448125268806410624001 13243086093951604807968001)
              ·
                refine ⟨9932314570463703605976001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13243086093951604807968001 9932314570463703605976001)
                ·
                  refine ⟨7449235927847777704482001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9932314570463703605976001 7449235927847777704482001)
                  ·
                    refine ⟨5586926945885833278361501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7449235927847777704482001 5586926945885833278361501)
                    ·
                      refine ⟨2095097604707187479385563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5586926945885833278361501 2095097604707187479385563)
                      ·
                        rfl

theorem cell23_4080188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 2, 3].length) (baseStart_4080188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080188 prefixEnd_4080188 := by exact prefixLift 4080188
  have htrace : WordTrace (prefixWord ++ tailWord_4080188) baseStart_4080188 baseEnd_4080188 := by
    simpa [prefixWord, tailWord_4080188, baseEnd_4080188] using wordTrace_append hprefix tailTrace_4080188
  have hstable : (prefixWord ++ tailWord_4080188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080188).length < 2 ^ (prefixWord ++ tailWord_4080188).sum := by decide
  have hdescent : baseEnd_4080188 < baseStart_4080188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080191 : List Nat := [1, 1, 2, 2, 3, 2, 4, 2, 6]
def baseStart_4080191 : Nat := 118140960795 + 4080191 * 2 ^ 59
def prefixEnd_4080191 : Nat := 4983230072969 + 3 ^ 40 * 4080191 * 2
def baseEnd_4080191 : Nat := 232788793905461218627561

theorem tailTrace_4080191 : CollatzResearch.WordTrace tailWord_4080191 prefixEnd_4080191 232788793905461218627561 := by
  unfold tailWord_4080191
  simp only [CollatzResearch.WordTrace]
  refine ⟨148816791561172322989552427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99211194374114881993034951 148816791561172322989552427)
  ·
    refine ⟨223225187341758484484328641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148816791561172322989552427 223225187341758484484328641)
    ·
      refine ⟨167418890506318863363246481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223225187341758484484328641 167418890506318863363246481)
      ·
        refine ⟨125564167879739147522434861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 167418890506318863363246481 125564167879739147522434861)
        ·
          refine ⟨47086562954902180320913073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125564167879739147522434861 47086562954902180320913073)
          ·
            refine ⟨35314922216176635240684805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47086562954902180320913073 35314922216176635240684805)
            ·
              refine ⟨6621547915533119107628401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35314922216176635240684805 6621547915533119107628401)
              ·
                refine ⟨4966160936649839330721301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621547915533119107628401 4966160936649839330721301)
                ·
                  refine ⟨232788793905461218627561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4966160936649839330721301 232788793905461218627561)
                  ·
                    rfl

theorem cell23_4080191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 6].length) (baseStart_4080191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080191 prefixEnd_4080191 := by exact prefixLift 4080191
  have htrace : WordTrace (prefixWord ++ tailWord_4080191) baseStart_4080191 baseEnd_4080191 := by
    simpa [prefixWord, tailWord_4080191, baseEnd_4080191] using wordTrace_append hprefix tailTrace_4080191
  have hstable : (prefixWord ++ tailWord_4080191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080191).length < 2 ^ (prefixWord ++ tailWord_4080191).sum := by decide
  have hdescent : baseEnd_4080191 < baseStart_4080191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080228 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 1, 5, 2]
def baseStart_4080228 : Nat := 118140960795 + 4080228 * 2 ^ 59
def prefixEnd_4080228 : Nat := 4983230072969 + 3 ^ 40 * 4080228 * 2
def baseEnd_4080228 : Nat := 2095118143933367322885379

theorem tailTrace_4080228 : CollatzResearch.WordTrace tailWord_4080228 prefixEnd_4080228 2095118143933367322885379 := by
  unfold tailWord_4080228
  simp only [CollatzResearch.WordTrace]
  refine ⟨74409070531019139154324669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99212094041358852205766225 74409070531019139154324669)
  ·
    refine ⟨27903401449132177182871751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74409070531019139154324669 27903401449132177182871751)
    ·
      refine ⟨41855102173698265774307627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27903401449132177182871751 41855102173698265774307627)
      ·
        refine ⟨62782653260547398661461441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41855102173698265774307627 62782653260547398661461441)
        ·
          refine ⟨47086989945410548996096081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62782653260547398661461441 47086989945410548996096081)
          ·
            refine ⟨35315242459057911747072061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47086989945410548996096081 35315242459057911747072061)
            ·
              refine ⟨13243215922146716905152023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35315242459057911747072061 13243215922146716905152023)
              ·
                refine ⟨19864823883220075357728035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13243215922146716905152023 19864823883220075357728035)
                ·
                  refine ⟨29797235824830113036592053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19864823883220075357728035 29797235824830113036592053)
                  ·
                    refine ⟨2793490858577823097180505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 29797235824830113036592053 2793490858577823097180505)
                    ·
                      refine ⟨2095118143933367322885379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793490858577823097180505 2095118143933367322885379)
                      ·
                        rfl

theorem cell23_4080228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 1, 5, 2].length) (baseStart_4080228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080228 prefixEnd_4080228 := by exact prefixLift 4080228
  have htrace : WordTrace (prefixWord ++ tailWord_4080228) baseStart_4080228 baseEnd_4080228 := by
    simpa [prefixWord, tailWord_4080228, baseEnd_4080228] using wordTrace_append hprefix tailTrace_4080228
  have hstable : (prefixWord ++ tailWord_4080228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080228).length < 2 ^ (prefixWord ++ tailWord_4080228).sum := by decide
  have hdescent : baseEnd_4080228 < baseStart_4080228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080261 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 5]
def baseStart_4080261 : Nat := 118140960795 + 4080261 * 2 ^ 59
def prefixEnd_4080261 : Nat := 4983230072969 + 3 ^ 40 * 4080261 * 2
def baseEnd_4080261 : Nat := 2095135088794965693772727

theorem tailTrace_4080261 : CollatzResearch.WordTrace tailWord_4080261 prefixEnd_4080261 2095135088794965693772727 := by
  unfold tailWord_4080261
  simp only [CollatzResearch.WordTrace]
  refine ⟨148819344670918724944600637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99212896447279149963067091 148819344670918724944600637)
  ·
    refine ⟨55807254251594521854225239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148819344670918724944600637 55807254251594521854225239)
    ·
      refine ⟨83710881377391782781337859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55807254251594521854225239 83710881377391782781337859)
      ·
        refine ⟨125566322066087674172006789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83710881377391782781337859 125566322066087674172006789)
        ·
          refine ⟨23543685387391438907251273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125566322066087674172006789 23543685387391438907251273)
          ·
            refine ⟨17657764040543579180438455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23543685387391438907251273 17657764040543579180438455)
            ·
              refine ⟨26486646060815368770657683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17657764040543579180438455 26486646060815368770657683)
              ·
                refine ⟨39729969091223053155986525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26486646060815368770657683 39729969091223053155986525)
                ·
                  refine ⟨14898738409208644933494947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39729969091223053155986525 14898738409208644933494947)
                  ·
                    refine ⟨22348107613812967400242421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14898738409208644933494947 22348107613812967400242421)
                    ·
                      refine ⟨2095135088794965693772727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22348107613812967400242421 2095135088794965693772727)
                      ·
                        rfl

theorem cell23_4080261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_4080261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080261 prefixEnd_4080261 := by exact prefixLift 4080261
  have htrace : WordTrace (prefixWord ++ tailWord_4080261) baseStart_4080261 baseEnd_4080261 := by
    simpa [prefixWord, tailWord_4080261, baseEnd_4080261] using wordTrace_append hprefix tailTrace_4080261
  have hstable : (prefixWord ++ tailWord_4080261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080261).length < 2 ^ (prefixWord ++ tailWord_4080261).sum := by decide
  have hdescent : baseEnd_4080261 < baseStart_4080261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080309 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 3, 2, 2]
def baseStart_4080309 : Nat := 118140960795 + 4080309 * 2 ^ 59
def prefixEnd_4080309 : Nat := 4983230072969 + 3 ^ 40 * 4080309 * 2
def baseEnd_4080309 : Nat := 2095159735866381505972507

theorem tailTrace_4080309 : CollatzResearch.WordTrace tailWord_4080309 prefixEnd_4080309 2095159735866381505972507 := by
  unfold tailWord_4080309
  simp only [CollatzResearch.WordTrace]
  refine ⟨148821095374744829142347981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99214063583163219428231987 148821095374744829142347981)
  ·
    refine ⟨55807910765529310928380493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148821095374744829142347981 55807910765529310928380493)
    ·
      refine ⟨20927966537073491598142685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55807910765529310928380493 20927966537073491598142685)
      ·
        refine ⟨7847987451402559349303507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20927966537073491598142685 7847987451402559349303507)
        ·
          refine ⟨11771981177103839023955261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7847987451402559349303507 11771981177103839023955261)
          ·
            refine ⟨4414492941413939633983223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11771981177103839023955261 4414492941413939633983223)
            ·
              refine ⟨6621739412120909450974835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414492941413939633983223 6621739412120909450974835)
              ·
                refine ⟨9932609118181364176462253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6621739412120909450974835 9932609118181364176462253)
                ·
                  refine ⟨3724728419318011566173345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9932609118181364176462253 3724728419318011566173345)
                  ·
                    refine ⟨2793546314488508674630009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3724728419318011566173345 2793546314488508674630009)
                    ·
                      refine ⟨2095159735866381505972507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793546314488508674630009 2095159735866381505972507)
                      ·
                        rfl

theorem cell23_4080309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_4080309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080309 prefixEnd_4080309 := by exact prefixLift 4080309
  have htrace : WordTrace (prefixWord ++ tailWord_4080309) baseStart_4080309 baseEnd_4080309 := by
    simpa [prefixWord, tailWord_4080309, baseEnd_4080309] using wordTrace_append hprefix tailTrace_4080309
  have hstable : (prefixWord ++ tailWord_4080309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080309).length < 2 ^ (prefixWord ++ tailWord_4080309).sum := by decide
  have hdescent : baseEnd_4080309 < baseStart_4080309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080326 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4]
def baseStart_4080326 : Nat := 118140960795 + 4080326 * 2 ^ 59
def prefixEnd_4080326 : Nat := 4983230072969 + 3 ^ 40 * 4080326 * 2
def baseEnd_4080326 : Nat := 2095168465037507939459929

theorem tailTrace_4080326 : CollatzResearch.WordTrace tailWord_4080326 prefixEnd_4080326 2095168465037507939459929 := by
  unfold tailWord_4080326
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650678606740101282678651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 99214476943788827363811221 4650678606740101282678651)
  ·
    refine ⟨6976017910110151924017977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4650678606740101282678651 6976017910110151924017977)
    ·
      refine ⟨5232013432582613943013483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6976017910110151924017977 5232013432582613943013483)
      ·
        refine ⟨7848020148873920914520225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232013432582613943013483 7848020148873920914520225)
        ·
          refine ⟨5886015111655440685890169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7848020148873920914520225 5886015111655440685890169)
          ·
            refine ⟨4414511333741580514417627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5886015111655440685890169 4414511333741580514417627)
            ·
              refine ⟨6621767000612370771626441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414511333741580514417627 6621767000612370771626441)
              ·
                refine ⟨4966325250459278078719831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6621767000612370771626441 4966325250459278078719831)
                ·
                  refine ⟨7449487875688917118079747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4966325250459278078719831 7449487875688917118079747)
                  ·
                    refine ⟨11174231813533375677119621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7449487875688917118079747 11174231813533375677119621)
                    ·
                      refine ⟨2095168465037507939459929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11174231813533375677119621 2095168465037507939459929)
                      ·
                        rfl

theorem cell23_4080326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_4080326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080326 prefixEnd_4080326 := by exact prefixLift 4080326
  have htrace : WordTrace (prefixWord ++ tailWord_4080326) baseStart_4080326 baseEnd_4080326 := by
    simpa [prefixWord, tailWord_4080326, baseEnd_4080326] using wordTrace_append hprefix tailTrace_4080326
  have hstable : (prefixWord ++ tailWord_4080326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080326).length < 2 ^ (prefixWord ++ tailWord_4080326).sum := by decide
  have hdescent : baseEnd_4080326 < baseStart_4080326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080365 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_4080365 : Nat := 118140960795 + 4080365 * 2 ^ 59
def prefixEnd_4080365 : Nat := 4983230072969 + 3 ^ 40 * 4080365 * 2
def baseEnd_4080365 : Nat := 2095188490783033286872249

theorem tailTrace_4080365 : CollatzResearch.WordTrace tailWord_4080365 prefixEnd_4080365 2095188490783033286872249 := by
  unfold tailWord_4080365
  simp only [CollatzResearch.WordTrace]
  refine ⟨148823137862541950706386549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99215425241694633804257699 148823137862541950706386549)
  ·
    refine ⟨13952169174613307878723739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148823137862541950706386549 13952169174613307878723739)
    ·
      refine ⟨20928253761919961818085609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13952169174613307878723739 20928253761919961818085609)
      ·
        refine ⟨15696190321439971363564207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20928253761919961818085609 15696190321439971363564207)
        ·
          refine ⟨23544285482159957045346311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15696190321439971363564207 23544285482159957045346311)
          ·
            refine ⟨35316428223239935568019467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23544285482159957045346311 35316428223239935568019467)
            ·
              refine ⟨52974642334859903352029201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35316428223239935568019467 52974642334859903352029201)
              ·
                refine ⟨39730981751144927514021901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52974642334859903352029201 39730981751144927514021901)
                ·
                  refine ⟨14899118156679347817758213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39730981751144927514021901 14899118156679347817758213)
                  ·
                    refine ⟨2793584654377377715829665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14899118156679347817758213 2793584654377377715829665)
                    ·
                      refine ⟨2095188490783033286872249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793584654377377715829665 2095188490783033286872249)
                      ·
                        rfl

theorem cell23_4080365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_4080365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080365 prefixEnd_4080365 := by exact prefixLift 4080365
  have htrace : WordTrace (prefixWord ++ tailWord_4080365) baseStart_4080365 baseEnd_4080365 := by
    simpa [prefixWord, tailWord_4080365, baseEnd_4080365] using wordTrace_append hprefix tailTrace_4080365
  have hstable : (prefixWord ++ tailWord_4080365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080365).length < 2 ^ (prefixWord ++ tailWord_4080365).sum := by decide
  have hdescent : baseEnd_4080365 < baseStart_4080365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080371 : List Nat := [1, 1, 1, 2, 2, 3, 1, 5, 7]
def baseStart_4080371 : Nat := 118140960795 + 4080371 * 2 ^ 59
def prefixEnd_4080371 : Nat := 4983230072969 + 3 ^ 40 * 4080371 * 2
def baseEnd_4080371 : Nat := 232799063518551140377469

theorem tailTrace_4080371 : CollatzResearch.WordTrace tailWord_4080371 prefixEnd_4080371 232799063518551140377469 := by
  unfold tailWord_4080371
  simp only [CollatzResearch.WordTrace]
  refine ⟨148823356700520213731104967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99215571133680142487403311 148823356700520213731104967)
  ·
    refine ⟨223235035050780320596657451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148823356700520213731104967 223235035050780320596657451)
    ·
      refine ⟨334852552576170480894986177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 223235035050780320596657451 334852552576170480894986177)
      ·
        refine ⟨251139414432127860671239633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 334852552576170480894986177 251139414432127860671239633)
        ·
          refine ⟨188354560824095895503429725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251139414432127860671239633 188354560824095895503429725)
          ·
            refine ⟨70632960309035960813786147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 188354560824095895503429725 70632960309035960813786147)
            ·
              refine ⟨105949440463553941220679221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70632960309035960813786147 105949440463553941220679221)
              ·
                refine ⟨9932760043458181989438677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105949440463553941220679221 9932760043458181989438677)
                ·
                  refine ⟨232799063518551140377469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9932760043458181989438677 232799063518551140377469)
                  ·
                    rfl

theorem cell23_4080371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 7].length) (baseStart_4080371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080371 prefixEnd_4080371 := by exact prefixLift 4080371
  have htrace : WordTrace (prefixWord ++ tailWord_4080371) baseStart_4080371 baseEnd_4080371 := by
    simpa [prefixWord, tailWord_4080371, baseEnd_4080371] using wordTrace_append hprefix tailTrace_4080371
  have hstable : (prefixWord ++ tailWord_4080371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080371).length < 2 ^ (prefixWord ++ tailWord_4080371).sum := by decide
  have hdescent : baseEnd_4080371 < baseStart_4080371 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080382 : List Nat := [4, 2, 2, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_4080382 : Nat := 118140960795 + 4080382 * 2 ^ 59
def prefixEnd_4080382 : Nat := 4983230072969 + 3 ^ 40 * 4080382 * 2
def baseEnd_4080382 : Nat := 2095197219954159720359671

theorem tailTrace_4080382 : CollatzResearch.WordTrace tailWord_4080382 prefixEnd_4080382 2095197219954159720359671 := by
  unfold tailWord_4080382
  simp only [CollatzResearch.WordTrace]
  refine ⟨18602969737935045326219425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99215838602320241739836933 18602969737935045326219425)
  ·
    refine ⟨13952227303451283994664569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18602969737935045326219425 13952227303451283994664569)
    ·
      refine ⟨10464170477588462995998427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13952227303451283994664569 10464170477588462995998427)
      ·
        refine ⟨15696255716382694493997641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10464170477588462995998427 15696255716382694493997641)
        ·
          refine ⟨11772191787287020870498231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15696255716382694493997641 11772191787287020870498231)
          ·
            refine ⟨17658287680930531305747347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772191787287020870498231 17658287680930531305747347)
            ·
              refine ⟨26487431521395796958621021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17658287680930531305747347 26487431521395796958621021)
              ·
                refine ⟨9932786820523423859482883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26487431521395796958621021 9932786820523423859482883)
                ·
                  refine ⟨14899180230785135789224325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9932786820523423859482883 14899180230785135789224325)
                  ·
                    refine ⟨2793596293272212960479561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14899180230785135789224325 2793596293272212960479561)
                    ·
                      refine ⟨2095197219954159720359671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793596293272212960479561 2095197219954159720359671)
                      ·
                        rfl

theorem cell23_4080382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_4080382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080382 prefixEnd_4080382 := by exact prefixLift 4080382
  have htrace : WordTrace (prefixWord ++ tailWord_4080382) baseStart_4080382 baseEnd_4080382 := by
    simpa [prefixWord, tailWord_4080382, baseEnd_4080382] using wordTrace_append hprefix tailTrace_4080382
  have hstable : (prefixWord ++ tailWord_4080382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080382).length < 2 ^ (prefixWord ++ tailWord_4080382).sum := by decide
  have hdescent : baseEnd_4080382 < baseStart_4080382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080388 : List Nat := [2, 3, 2, 2, 1, 1, 3, 2, 7]
def baseStart_4080388 : Nat := 118140960795 + 4080388 * 2 ^ 59
def prefixEnd_4080388 : Nat := 4983230072969 + 3 ^ 40 * 4080388 * 2
def baseEnd_4080388 : Nat := 232800033426454077431627

theorem tailTrace_4080388 : CollatzResearch.WordTrace tailWord_4080388 prefixEnd_4080388 232800033426454077431627 := by
  unfold tailWord_4080388
  simp only [CollatzResearch.WordTrace]
  refine ⟨74411988370729312817236909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99215984494305750422982545 74411988370729312817236909)
  ·
    refine ⟨27904495639023492306463841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74411988370729312817236909 27904495639023492306463841)
    ·
      refine ⟨20928371729267619229847881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27904495639023492306463841 20928371729267619229847881)
      ·
        refine ⟨15696278796950714422385911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20928371729267619229847881 15696278796950714422385911)
        ·
          refine ⟨23544418195426071633578867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15696278796950714422385911 23544418195426071633578867)
          ·
            refine ⟨35316627293139107450368301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23544418195426071633578867 35316627293139107450368301)
            ·
              refine ⟨13243735234927165293888113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35316627293139107450368301 13243735234927165293888113)
              ·
                refine ⟨9932801426195373970416085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13243735234927165293888113 9932801426195373970416085)
                ·
                  refine ⟨232800033426454077431627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9932801426195373970416085 232800033426454077431627)
                  ·
                    rfl

theorem cell23_4080388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_4080388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080388 prefixEnd_4080388 := by exact prefixLift 4080388
  have htrace : WordTrace (prefixWord ++ tailWord_4080388) baseStart_4080388 baseEnd_4080388 := by
    simpa [prefixWord, tailWord_4080388, baseEnd_4080388] using wordTrace_append hprefix tailTrace_4080388
  have hstable : (prefixWord ++ tailWord_4080388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080388).length < 2 ^ (prefixWord ++ tailWord_4080388).sum := by decide
  have hdescent : baseEnd_4080388 < baseStart_4080388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080398 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4080398 : Nat := 118140960795 + 4080398 * 2 ^ 59
def prefixEnd_4080398 : Nat := 4983230072969 + 3 ^ 40 * 4080398 * 2
def baseEnd_4080398 : Nat := 2095205435644631657759597

theorem tailTrace_4080398 : CollatzResearch.WordTrace tailWord_4080398 prefixEnd_4080398 2095205435644631657759597 := by
  unfold tailWord_4080398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18603042683927799667792231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 99216227647614931561558565 18603042683927799667792231)
  ·
    refine ⟨27904564025891699501688347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18603042683927799667792231 27904564025891699501688347)
    ·
      refine ⟨41856846038837549252532521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27904564025891699501688347 41856846038837549252532521)
      ·
        refine ⟨31392634529128161939399391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41856846038837549252532521 31392634529128161939399391)
        ·
          refine ⟨47088951793692242909099087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31392634529128161939399391 47088951793692242909099087)
          ·
            refine ⟨70633427690538364363648631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47088951793692242909099087 70633427690538364363648631)
            ·
              refine ⟨105950141535807546545472947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70633427690538364363648631 105950141535807546545472947)
              ·
                refine ⟨158925212303711319818209421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105950141535807546545472947 158925212303711319818209421)
                ·
                  refine ⟨59596954613891744931828533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 158925212303711319818209421 59596954613891744931828533)
                  ·
                    refine ⟨5587214495052351087358925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 59596954613891744931828533 5587214495052351087358925)
                    ·
                      refine ⟨2095205435644631657759597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5587214495052351087358925 2095205435644631657759597)
                      ·
                        rfl

theorem cell23_4080398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4080398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080398 prefixEnd_4080398 := by exact prefixLift 4080398
  have htrace : WordTrace (prefixWord ++ tailWord_4080398) baseStart_4080398 baseEnd_4080398 := by
    simpa [prefixWord, tailWord_4080398, baseEnd_4080398] using wordTrace_append hprefix tailTrace_4080398
  have hstable : (prefixWord ++ tailWord_4080398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080398).length < 2 ^ (prefixWord ++ tailWord_4080398).sum := by decide
  have hdescent : baseEnd_4080398 < baseStart_4080398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080405 : List Nat := [1, 3, 2, 1, 2, 2, 4, 3, 5]
def baseStart_4080405 : Nat := 118140960795 + 4080405 * 2 ^ 59
def prefixEnd_4080405 : Nat := 4983230072969 + 3 ^ 40 * 4080405 * 2
def baseEnd_4080405 : Nat := 232801003334357014485785

theorem tailTrace_4080405 : CollatzResearch.WordTrace tailWord_4080405 prefixEnd_4080405 232801003334357014485785 := by
  unfold tailWord_4080405
  simp only [CollatzResearch.WordTrace]
  refine ⟨148824596782397037537842669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99216397854931358358561779 148824596782397037537842669)
  ·
    refine ⟨55809223793398889076691001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148824596782397037537842669 55809223793398889076691001)
    ·
      refine ⟨41856917845049166807518251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55809223793398889076691001 41856917845049166807518251)
      ·
        refine ⟨62785376767573750211277377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41856917845049166807518251 62785376767573750211277377)
        ·
          refine ⟨47089032575680312658458033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62785376767573750211277377 47089032575680312658458033)
          ·
            refine ⟨35316774431760234493843525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47089032575680312658458033 35316774431760234493843525)
            ·
              refine ⟨6621895205955043967595661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35316774431760234493843525 6621895205955043967595661)
              ·
                refine ⟨2483210702233141487848373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6621895205955043967595661 2483210702233141487848373)
                ·
                  refine ⟨232801003334357014485785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2483210702233141487848373 232801003334357014485785)
                  ·
                    rfl

theorem cell23_4080405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 3, 5].length) (baseStart_4080405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080405 prefixEnd_4080405 := by exact prefixLift 4080405
  have htrace : WordTrace (prefixWord ++ tailWord_4080405) baseStart_4080405 baseEnd_4080405 := by
    simpa [prefixWord, tailWord_4080405, baseEnd_4080405] using wordTrace_append hprefix tailTrace_4080405
  have hstable : (prefixWord ++ tailWord_4080405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080405).length < 2 ^ (prefixWord ++ tailWord_4080405).sum := by decide
  have hdescent : baseEnd_4080405 < baseStart_4080405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080431 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 8]
def baseStart_4080431 : Nat := 118140960795 + 4080431 * 2 ^ 59
def prefixEnd_4080431 : Nat := 4983230072969 + 3 ^ 40 * 4080431 * 2
def baseEnd_4080431 : Nat := 698407460168743342882315

theorem tailTrace_4080431 : CollatzResearch.WordTrace tailWord_4080431 prefixEnd_4080431 698407460168743342882315 := by
  unfold tailWord_4080431
  simp only [CollatzResearch.WordTrace]
  refine ⟨148825545080302843978289147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99217030053535229318859431 148825545080302843978289147)
  ·
    refine ⟨223238317620454265967433721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148825545080302843978289147 223238317620454265967433721)
    ·
      refine ⟨167428738215340699475575291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 223238317620454265967433721 167428738215340699475575291)
      ·
        refine ⟨251143107323011049213362937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167428738215340699475575291 251143107323011049213362937)
        ·
          refine ⟨188357330492258286910022203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251143107323011049213362937 188357330492258286910022203)
          ·
            refine ⟨282535995738387430365033305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188357330492258286910022203 282535995738387430365033305)
            ·
              refine ⟨211901996803790572773774979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 282535995738387430365033305 211901996803790572773774979)
              ·
                refine ⟨317852995205685859160662469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211901996803790572773774979 317852995205685859160662469)
                ·
                  refine ⟨59597436601066098592624213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 317852995205685859160662469 59597436601066098592624213)
                  ·
                    refine ⟨698407460168743342882315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 59597436601066098592624213 698407460168743342882315)
                    ·
                      rfl

theorem cell23_4080431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 8].length) (baseStart_4080431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080431 prefixEnd_4080431 := by exact prefixLift 4080431
  have htrace : WordTrace (prefixWord ++ tailWord_4080431) baseStart_4080431 baseEnd_4080431 := by
    simpa [prefixWord, tailWord_4080431, baseEnd_4080431] using wordTrace_append hprefix tailTrace_4080431
  have hstable : (prefixWord ++ tailWord_4080431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080431).length < 2 ^ (prefixWord ++ tailWord_4080431).sum := by decide
  have hdescent : baseEnd_4080431 < baseStart_4080431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080498 : List Nat := [3, 2, 1, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4080498 : Nat := 118140960795 + 4080498 * 2 ^ 59
def prefixEnd_4080498 : Nat := 4983230072969 + 3 ^ 40 * 4080498 * 2
def baseEnd_4080498 : Nat := 2095256783710081266509137

theorem tailTrace_4080498 : CollatzResearch.WordTrace tailWord_4080498 prefixEnd_4080498 2095256783710081266509137 := by
  unfold tailWord_4080498
  simp only [CollatzResearch.WordTrace]
  refine ⟨37206997192765028605244537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 99218659180706742947318765 37206997192765028605244537)
  ·
    refine ⟨27905247894573771453933403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37206997192765028605244537 27905247894573771453933403)
    ·
      refine ⟨41857871841860657180900105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27905247894573771453933403 41857871841860657180900105)
      ·
        refine ⟨31393403881395492885675079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41857871841860657180900105 31393403881395492885675079)
        ·
          refine ⟨47090105822093239328512619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31393403881395492885675079 47090105822093239328512619)
          ·
            refine ⟨70635158733139858992768929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47090105822093239328512619 70635158733139858992768929)
            ·
              refine ⟨52976369049854894244576697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70635158733139858992768929 52976369049854894244576697)
              ·
                refine ⟨39732276787391170683432523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52976369049854894244576697 39732276787391170683432523)
                ·
                  refine ⟨59598415181086756025148785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39732276787391170683432523 59598415181086756025148785)
                  ·
                    refine ⟨44698811385815067018861589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 59598415181086756025148785 44698811385815067018861589)
                    ·
                      refine ⟨2095256783710081266509137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 44698811385815067018861589 2095256783710081266509137)
                      ·
                        rfl

theorem cell23_4080498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4080498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080498 prefixEnd_4080498 := by exact prefixLift 4080498
  have htrace : WordTrace (prefixWord ++ tailWord_4080498) baseStart_4080498 baseEnd_4080498 := by
    simpa [prefixWord, tailWord_4080498, baseEnd_4080498] using wordTrace_append hprefix tailTrace_4080498
  have hstable : (prefixWord ++ tailWord_4080498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080498).length < 2 ^ (prefixWord ++ tailWord_4080498).sum := by decide
  have hdescent : baseEnd_4080498 < baseStart_4080498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080596 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4080596 : Nat := 118140960795 + 4080596 * 2 ^ 59
def prefixEnd_4080596 : Nat := 4983230072969 + 3 ^ 40 * 4080596 * 2
def baseEnd_4080596 : Nat := 2095307104814221883083687

theorem tailTrace_4080596 : CollatzResearch.WordTrace tailWord_4080596 prefixEnd_4080596 2095307104814221883083687 := by
  unfold tailWord_4080596
  simp only [CollatzResearch.WordTrace]
  refine ⟨74415781562352538579022821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 99221042083136718105363761 74415781562352538579022821)
  ·
    refine ⟨13952959042941100983566779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74415781562352538579022821 13952959042941100983566779)
    ·
      refine ⟨20929438564411651475350169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13952959042941100983566779 20929438564411651475350169)
      ·
        refine ⟨15697078923308738606512627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20929438564411651475350169 15697078923308738606512627)
        ·
          refine ⟨23545618384963107909768941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15697078923308738606512627 23545618384963107909768941)
          ·
            refine ⟨8829606894361165466163353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23545618384963107909768941 8829606894361165466163353)
            ·
              refine ⟨6622205170770874099622515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8829606894361165466163353 6622205170770874099622515)
              ·
                refine ⟨9933307756156311149433773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6622205170770874099622515 9933307756156311149433773)
                ·
                  refine ⟨3724990408558616681037665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9933307756156311149433773 3724990408558616681037665)
                  ·
                    refine ⟨2793742806418962510778249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3724990408558616681037665 2793742806418962510778249)
                    ·
                      refine ⟨2095307104814221883083687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793742806418962510778249 2095307104814221883083687)
                      ·
                        rfl

theorem cell23_4080596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4080596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080596 prefixEnd_4080596 := by exact prefixLift 4080596
  have htrace : WordTrace (prefixWord ++ tailWord_4080596) baseStart_4080596 baseEnd_4080596 := by
    simpa [prefixWord, tailWord_4080596, baseEnd_4080596] using wordTrace_append hprefix tailTrace_4080596
  have hstable : (prefixWord ++ tailWord_4080596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080596).length < 2 ^ (prefixWord ++ tailWord_4080596).sum := by decide
  have hdescent : baseEnd_4080596 < baseStart_4080596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080625 : List Nat := [1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 5]
def baseStart_4080625 : Nat := 118140960795 + 4080625 * 2 ^ 59
def prefixEnd_4080625 : Nat := 4983230072969 + 3 ^ 40 * 4080625 * 2
def baseEnd_4080625 : Nat := 2095321995753202269621053

theorem tailTrace_4080625 : CollatzResearch.WordTrace tailWord_4080625 prefixEnd_4080625 2095321995753202269621053 := by
  unfold tailWord_4080625
  simp only [CollatzResearch.WordTrace]
  refine ⟨148832620841600015110851329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 99221747227733343407234219 148832620841600015110851329)
  ·
    refine ⟨111624465631200011333138497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148832620841600015110851329 111624465631200011333138497)
    ·
      refine ⟨83718349223400008499853873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111624465631200011333138497 83718349223400008499853873)
      ·
        refine ⟨62788761917550006374890405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83718349223400008499853873 62788761917550006374890405)
        ·
          refine ⟨11772892859540626195291951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62788761917550006374890405 11772892859540626195291951)
          ·
            refine ⟨17659339289310939292937927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11772892859540626195291951 17659339289310939292937927)
            ·
              refine ⟨26489008933966408939406891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17659339289310939292937927 26489008933966408939406891)
              ·
                refine ⟨39733513400949613409110337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26489008933966408939406891 39733513400949613409110337)
                ·
                  refine ⟨29800135050712210056832753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39733513400949613409110337 29800135050712210056832753)
                  ·
                    refine ⟨22350101288034157542624565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29800135050712210056832753 22350101288034157542624565)
                    ·
                      refine ⟨2095321995753202269621053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22350101288034157542624565 2095321995753202269621053)
                      ·
                        rfl

theorem cell23_4080625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_4080625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080625 prefixEnd_4080625 := by exact prefixLift 4080625
  have htrace : WordTrace (prefixWord ++ tailWord_4080625) baseStart_4080625 baseEnd_4080625 := by
    simpa [prefixWord, tailWord_4080625, baseEnd_4080625] using wordTrace_append hprefix tailTrace_4080625
  have hstable : (prefixWord ++ tailWord_4080625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080625).length < 2 ^ (prefixWord ++ tailWord_4080625).sum := by decide
  have hdescent : baseEnd_4080625 < baseStart_4080625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4080630 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_4080630 : Nat := 118140960795 + 4080630 * 2 ^ 59
def prefixEnd_4080630 : Nat := 4983230072969 + 3 ^ 40 * 4080630 * 2
def baseEnd_4080630 : Nat := 2095324563156474750058531

theorem tailTrace_4080630 : CollatzResearch.WordTrace tailWord_4080630 prefixEnd_4080630 2095324563156474750058531 := by
  unfold tailWord_4080630
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302050200411368810298959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 99221868804387933976522229 9302050200411368810298959)
  ·
    refine ⟨13953075300617053215448439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9302050200411368810298959 13953075300617053215448439)
    ·
      refine ⟨20929612950925579823172659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13953075300617053215448439 20929612950925579823172659)
      ·
        refine ⟨31394419426388369734758989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20929612950925579823172659 31394419426388369734758989)
        ·
          refine ⟨11772907284895638650534621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31394419426388369734758989 11772907284895638650534621)
          ·
            refine ⟨4414840231835864493950483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11772907284895638650534621 4414840231835864493950483)
            ·
              refine ⟨6622260347753796740925725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4414840231835864493950483 6622260347753796740925725)
              ·
                refine ⟨2483347630407673777847147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6622260347753796740925725 2483347630407673777847147)
                ·
                  refine ⟨3725021445611510666770721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2483347630407673777847147 3725021445611510666770721)
                  ·
                    refine ⟨2793766084208633000078041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3725021445611510666770721 2793766084208633000078041)
                    ·
                      refine ⟨2095324563156474750058531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2793766084208633000078041 2095324563156474750058531)
                      ·
                        rfl

theorem cell23_4080630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_4080630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4080630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4080630 prefixEnd_4080630 := by exact prefixLift 4080630
  have htrace : WordTrace (prefixWord ++ tailWord_4080630) baseStart_4080630 baseEnd_4080630 := by
    simpa [prefixWord, tailWord_4080630, baseEnd_4080630] using wordTrace_append hprefix tailTrace_4080630
  have hstable : (prefixWord ++ tailWord_4080630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4080630).length < 2 ^ (prefixWord ++ tailWord_4080630).sum := by decide
  have hdescent : baseEnd_4080630 < baseStart_4080630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4080630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
