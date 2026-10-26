import V185TrunkScan22Chunk303

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2710503 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 3, 4]
def baseStart_2710503 : Nat := 118140960795 + 2710503 * 2 ^ 59
def prefixEnd_2710503 : Nat := 4983230072969 + 3 ^ 40 * 2710503 * 2
def baseEnd_2710503 : Nat := 927860569635809252164753

theorem tailTrace_2710503 : CollatzResearch.WordTrace tailWord_2710503 prefixEnd_2710503 927860569635809252164753 := by
  unfold tailWord_2710503
  simp only [CollatzResearch.WordTrace]
  refine ⟨98860166099318022902800163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65906777399545348601866775 98860166099318022902800163)
  ·
    refine ⟨148290249148977034354200245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98860166099318022902800163 148290249148977034354200245)
    ·
      refine ⟨13902210857716596970706273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148290249148977034354200245 13902210857716596970706273)
      ·
        refine ⟨10426658143287447728029705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13902210857716596970706273 10426658143287447728029705)
        ·
          refine ⟨7819993607465585796022279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10426658143287447728029705 7819993607465585796022279)
          ·
            refine ⟨11729990411198378694033419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7819993607465585796022279 11729990411198378694033419)
            ·
              refine ⟨17594985616797568041050129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11729990411198378694033419 17594985616797568041050129)
              ·
                refine ⟨13196239212598176030787597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17594985616797568041050129 13196239212598176030787597)
                ·
                  refine ⟨4948589704724316011545349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13196239212598176030787597 4948589704724316011545349)
                  ·
                    refine ⟨927860569635809252164753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4948589704724316011545349 927860569635809252164753)
                    ·
                      rfl

theorem cell22_2710503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_2710503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710503 prefixEnd_2710503 := by exact prefixLift 2710503
  have htrace : WordTrace (prefixWord ++ tailWord_2710503) baseStart_2710503 baseEnd_2710503 := by
    simpa [prefixWord, tailWord_2710503, baseEnd_2710503] using wordTrace_append hprefix tailTrace_2710503
  have hstable : (prefixWord ++ tailWord_2710503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710503).length < 2 ^ (prefixWord ++ tailWord_2710503).sum := by decide
  have hdescent : baseEnd_2710503 < baseStart_2710503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710518 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2710518 : Nat := 118140960795 + 2710518 * 2 ^ 59
def prefixEnd_2710518 : Nat := 4983230072969 + 3 ^ 40 * 2710518 * 2
def baseEnd_2710518 : Nat := 309288568147451404346569

theorem tailTrace_2710518 : CollatzResearch.WordTrace tailWord_2710518 prefixEnd_2710518 309288568147451404346569 := by
  unfold tailWord_2710518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178794574641480029037263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65907142129509120309730805 6178794574641480029037263)
  ·
    refine ⟨9268191861962220043555895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6178794574641480029037263 9268191861962220043555895)
    ·
      refine ⟨13902287792943330065333843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268191861962220043555895 13902287792943330065333843)
      ·
        refine ⟨20853431689414995098000765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13902287792943330065333843 20853431689414995098000765)
        ·
          refine ⟨7820036883530623161750287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20853431689414995098000765 7820036883530623161750287)
          ·
            refine ⟨11730055325295934742625431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820036883530623161750287 11730055325295934742625431)
            ·
              refine ⟨17595082987943902113938147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11730055325295934742625431 17595082987943902113938147)
              ·
                refine ⟨26392624481915853170907221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17595082987943902113938147 26392624481915853170907221)
                ·
                  refine ⟨309288568147451404346569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26392624481915853170907221 309288568147451404346569)
                  ·
                    rfl

theorem cell22_2710518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2710518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710518 prefixEnd_2710518 := by exact prefixLift 2710518
  have htrace : WordTrace (prefixWord ++ tailWord_2710518) baseStart_2710518 baseEnd_2710518 := by
    simpa [prefixWord, tailWord_2710518, baseEnd_2710518] using wordTrace_append hprefix tailTrace_2710518
  have hstable : (prefixWord ++ tailWord_2710518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710518).length < 2 ^ (prefixWord ++ tailWord_2710518).sum := by decide
  have hdescent : baseEnd_2710518 < baseStart_2710518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710533 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 4, 3]
def baseStart_2710533 : Nat := 118140960795 + 2710533 * 2 ^ 59
def prefixEnd_2710533 : Nat := 4983230072969 + 3 ^ 40 * 2710533 * 2
def baseEnd_2710533 : Nat := 927870839248899173914661

theorem tailTrace_2710533 : CollatzResearch.WordTrace tailWord_2710533 prefixEnd_2710533 927870839248899173914661 := by
  unfold tailWord_2710533
  simp only [CollatzResearch.WordTrace]
  refine ⟨98861260289209338026392253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65907506859472892017594835 98861260289209338026392253)
  ·
    refine ⟨37072972608453501759897095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98861260289209338026392253 37072972608453501759897095)
    ·
      refine ⟨55609458912680252639845643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37072972608453501759897095 55609458912680252639845643)
      ·
        refine ⟨83414188369020378959768465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55609458912680252639845643 83414188369020378959768465)
        ·
          refine ⟨62560641276765284219826349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83414188369020378959768465 62560641276765284219826349)
          ·
            refine ⟨23460240478786981582434881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62560641276765284219826349 23460240478786981582434881)
            ·
              refine ⟨17595180359090236186826161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23460240478786981582434881 17595180359090236186826161)
              ·
                refine ⟨13196385269317677140119621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17595180359090236186826161 13196385269317677140119621)
                ·
                  refine ⟨2474322237997064463772429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13196385269317677140119621 2474322237997064463772429)
                  ·
                    refine ⟨927870839248899173914661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474322237997064463772429 927870839248899173914661)
                    ·
                      rfl

theorem cell22_2710533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_2710533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710533 prefixEnd_2710533 := by exact prefixLift 2710533
  have htrace : WordTrace (prefixWord ++ tailWord_2710533) baseStart_2710533 baseEnd_2710533 := by
    simpa [prefixWord, tailWord_2710533, baseEnd_2710533] using wordTrace_append hprefix tailTrace_2710533
  have hstable : (prefixWord ++ tailWord_2710533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710533).length < 2 ^ (prefixWord ++ tailWord_2710533).sum := by decide
  have hdescent : baseEnd_2710533 < baseStart_2710533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710535 : List Nat := [1, 1, 4, 3, 1, 1, 4, 3, 4]
def baseStart_2710535 : Nat := 118140960795 + 2710535 * 2 ^ 59
def prefixEnd_2710535 : Nat := 4983230072969 + 3 ^ 40 * 2710535 * 2
def baseEnd_2710535 : Nat := 309290507963257278454885

theorem tailTrace_2710535 : CollatzResearch.WordTrace tailWord_2710535 prefixEnd_2710535 309290507963257278454885 := by
  unfold tailWord_2710535
  simp only [CollatzResearch.WordTrace]
  refine ⟨98861333235202092367965059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65907555490134728245310039 98861333235202092367965059)
  ·
    refine ⟨148291999852803138551947589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98861333235202092367965059 148291999852803138551947589)
    ·
      refine ⟨27804749972400588478490173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148291999852803138551947589 27804749972400588478490173)
      ·
        refine ⟨10426781239650220679433815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27804749972400588478490173 10426781239650220679433815)
        ·
          refine ⟨15640171859475331019150723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10426781239650220679433815 15640171859475331019150723)
          ·
            refine ⟨23460257789212996528726085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15640171859475331019150723 23460257789212996528726085)
            ·
              refine ⟨4398798335477436849136141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23460257789212996528726085 4398798335477436849136141)
              ·
                refine ⟨1649549375804038818426053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4398798335477436849136141 1649549375804038818426053)
                ·
                  refine ⟨309290507963257278454885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1649549375804038818426053 309290507963257278454885)
                  ·
                    rfl

theorem cell22_2710535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 3, 4].length) (baseStart_2710535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710535 prefixEnd_2710535 := by exact prefixLift 2710535
  have htrace : WordTrace (prefixWord ++ tailWord_2710535) baseStart_2710535 baseEnd_2710535 := by
    simpa [prefixWord, tailWord_2710535, baseEnd_2710535] using wordTrace_append hprefix tailTrace_2710535
  have hstable : (prefixWord ++ tailWord_2710535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710535).length < 2 ^ (prefixWord ++ tailWord_2710535).sum := by decide
  have hdescent : baseEnd_2710535 < baseStart_2710535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710567 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 1, 5]
def baseStart_2710567 : Nat := 118140960795 + 2710567 * 2 ^ 59
def prefixEnd_2710567 : Nat := 4983230072969 + 3 ^ 40 * 2710567 * 2
def baseEnd_2710567 : Nat := 927882478143734418564557

theorem tailTrace_2710567 : CollatzResearch.WordTrace tailWord_2710567 prefixEnd_2710567 927882478143734418564557 := by
  unfold tailWord_2710567
  simp only [CollatzResearch.WordTrace]
  refine ⟨98862500371086161833129955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65908333580724107888753303 98862500371086161833129955)
  ·
    refine ⟨148293750556629242749694933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98862500371086161833129955 148293750556629242749694933)
    ·
      refine ⟨3475634778670997876945975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 148293750556629242749694933 3475634778670997876945975)
      ·
        refine ⟨5213452168006496815418963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3475634778670997876945975 5213452168006496815418963)
        ·
          refine ⟨7820178252009745223128445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213452168006496815418963 7820178252009745223128445)
          ·
            refine ⟨2932566844503654458673167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7820178252009745223128445 2932566844503654458673167)
            ·
              refine ⟨4398850266755481688009751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932566844503654458673167 4398850266755481688009751)
              ·
                refine ⟨6598275400133222532014627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4398850266755481688009751 6598275400133222532014627)
                ·
                  refine ⟨9897413100199833798021941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598275400133222532014627 9897413100199833798021941)
                  ·
                    refine ⟨927882478143734418564557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9897413100199833798021941 927882478143734418564557)
                    ·
                      rfl

theorem cell22_2710567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_2710567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710567 prefixEnd_2710567 := by exact prefixLift 2710567
  have htrace : WordTrace (prefixWord ++ tailWord_2710567) baseStart_2710567 baseEnd_2710567 := by
    simpa [prefixWord, tailWord_2710567, baseEnd_2710567] using wordTrace_append hprefix tailTrace_2710567
  have hstable : (prefixWord ++ tailWord_2710567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710567).length < 2 ^ (prefixWord ++ tailWord_2710567).sum := by decide
  have hdescent : baseEnd_2710567 < baseStart_2710567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710580 : List Nat := [2, 5, 1, 2, 1, 2, 1, 8]
def baseStart_2710580 : Nat := 118140960795 + 2710580 * 2 ^ 59
def prefixEnd_2710580 : Nat := 4983230072969 + 3 ^ 40 * 2710580 * 2
def baseEnd_2710580 : Nat := 103098547589934079776613

theorem tailTrace_2710580 : CollatzResearch.WordTrace tailWord_2710580 prefixEnd_2710580 103098547589934079776613 := by
  unfold tailWord_2710580
  simp only [CollatzResearch.WordTrace]
  refine ⟨49431487260019532526676597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65908649680026043368902129 49431487260019532526676597)
  ·
    refine ⟨4634201930626831174375931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49431487260019532526676597 4634201930626831174375931)
    ·
      refine ⟨6951302895940246761563897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4634201930626831174375931 6951302895940246761563897)
      ·
        refine ⟨5213477171955185071172923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6951302895940246761563897 5213477171955185071172923)
        ·
          refine ⟨7820215757932777606759385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213477171955185071172923 7820215757932777606759385)
          ·
            refine ⟨5865161818449583205069539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7820215757932777606759385 5865161818449583205069539)
            ·
              refine ⟨8797742727674374807604309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5865161818449583205069539 8797742727674374807604309)
              ·
                refine ⟨103098547589934079776613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8797742727674374807604309 103098547589934079776613)
                ·
                  rfl

theorem cell22_2710580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 8].length) (baseStart_2710580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710580 prefixEnd_2710580 := by exact prefixLift 2710580
  have htrace : WordTrace (prefixWord ++ tailWord_2710580) baseStart_2710580 baseEnd_2710580 := by
    simpa [prefixWord, tailWord_2710580, baseEnd_2710580] using wordTrace_append hprefix tailTrace_2710580
  have hstable : (prefixWord ++ tailWord_2710580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710580).length < 2 ^ (prefixWord ++ tailWord_2710580).sum := by decide
  have hdescent : baseEnd_2710580 < baseStart_2710580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710612 : List Nat := [2, 4, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_2710612 : Nat := 118140960795 + 2710612 * 2 ^ 59
def prefixEnd_2710612 : Nat := 4983230072969 + 3 ^ 40 * 2710612 * 2
def baseEnd_2710612 : Nat := 927897882563369301189419

theorem tailTrace_2710612 : CollatzResearch.WordTrace tailWord_2710612 prefixEnd_2710612 927897882563369301189419 := by
  unfold tailWord_2710612
  simp only [CollatzResearch.WordTrace]
  refine ⟨49432070827961567259259045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65909427770615423012345393 49432070827961567259259045)
  ·
    refine ⟨9268513280242793861111071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49432070827961567259259045 9268513280242793861111071)
    ·
      refine ⟨13902769920364190791666607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268513280242793861111071 13902769920364190791666607)
      ·
        refine ⟨20854154880546286187499911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13902769920364190791666607 20854154880546286187499911)
        ·
          refine ⟨31281232320819429281249867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20854154880546286187499911 31281232320819429281249867)
          ·
            refine ⟨46921848481229143921874801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31281232320819429281249867 46921848481229143921874801)
            ·
              refine ⟨35191386360921857941406101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46921848481229143921874801 35191386360921857941406101)
              ·
                refine ⟨1649596235668212091003411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35191386360921857941406101 1649596235668212091003411)
                ·
                  refine ⟨2474394353502318136505117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649596235668212091003411 2474394353502318136505117)
                  ·
                    refine ⟨927897882563369301189419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474394353502318136505117 927897882563369301189419)
                    ·
                      rfl

theorem cell22_2710612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_2710612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710612 prefixEnd_2710612 := by exact prefixLift 2710612
  have htrace : WordTrace (prefixWord ++ tailWord_2710612) baseStart_2710612 baseEnd_2710612 := by
    simpa [prefixWord, tailWord_2710612, baseEnd_2710612] using wordTrace_append hprefix tailTrace_2710612
  have hstable : (prefixWord ++ tailWord_2710612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710612).length < 2 ^ (prefixWord ++ tailWord_2710612).sum := by decide
  have hdescent : baseEnd_2710612 < baseStart_2710612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710625 : List Nat := [1, 2, 3, 1, 1, 2, 6, 1, 5]
def baseStart_2710625 : Nat := 118140960795 + 2710625 * 2 ^ 59
def prefixEnd_2710625 : Nat := 4983230072969 + 3 ^ 40 * 2710625 * 2
def baseEnd_2710625 : Nat := 309300777576347200204793

theorem tailTrace_2710625 : CollatzResearch.WordTrace tailWord_2710625 prefixEnd_2710625 309300777576347200204793 := by
  unfold tailWord_2710625
  simp only [CollatzResearch.WordTrace]
  refine ⟨98864615804876037738741329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65909743869917358492494219 98864615804876037738741329)
  ·
    refine ⟨74148461853657028304055997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98864615804876037738741329 74148461853657028304055997)
    ·
      refine ⟨27805673195121385614020999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74148461853657028304055997 27805673195121385614020999)
      ·
        refine ⟨41708509792682078421031499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27805673195121385614020999 41708509792682078421031499)
        ·
          refine ⟨62562764689023117631547249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41708509792682078421031499 62562764689023117631547249)
          ·
            refine ⟨46922073516767338223660437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62562764689023117631547249 46922073516767338223660437)
            ·
              refine ⟨2199472196098468979234083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46922073516767338223660437 2199472196098468979234083)
              ·
                refine ⟨3299208294147703468851125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2199472196098468979234083 3299208294147703468851125)
                ·
                  refine ⟨309300777576347200204793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3299208294147703468851125 309300777576347200204793)
                  ·
                    rfl

theorem cell22_2710625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_2710625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710625 prefixEnd_2710625 := by exact prefixLift 2710625
  have htrace : WordTrace (prefixWord ++ tailWord_2710625) baseStart_2710625 baseEnd_2710625 := by
    simpa [prefixWord, tailWord_2710625, baseEnd_2710625] using wordTrace_append hprefix tailTrace_2710625
  have hstable : (prefixWord ++ tailWord_2710625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710625).length < 2 ^ (prefixWord ++ tailWord_2710625).sum := by decide
  have hdescent : baseEnd_2710625 < baseStart_2710625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710685 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 1, 5]
def baseStart_2710685 : Nat := 118140960795 + 2710685 * 2 ^ 59
def prefixEnd_2710685 : Nat := 4983230072969 + 3 ^ 40 * 2710685 * 2
def baseEnd_2710685 : Nat := 927922871955221444114195

theorem tailTrace_2710685 : CollatzResearch.WordTrace tailWord_2710685 prefixEnd_2710685 927922871955221444114195 := by
  unfold tailWord_2710685
  simp only [CollatzResearch.WordTrace]
  refine ⟨98866804184658667985925509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65911202789772445323950339 98866804184658667985925509)
  ·
    refine ⟨18537525784623500247361033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98866804184658667985925509 18537525784623500247361033)
    ·
      refine ⟨13903144338467625185520775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18537525784623500247361033 13903144338467625185520775)
      ·
        refine ⟨20854716507701437778281163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13903144338467625185520775 20854716507701437778281163)
        ·
          refine ⟨31282074761552156667421745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20854716507701437778281163 31282074761552156667421745)
          ·
            refine ⟨23461556071164117500566309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31282074761552156667421745 23461556071164117500566309)
            ·
              refine ⟨4399041763343272031356183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23461556071164117500566309 4399041763343272031356183)
              ·
                refine ⟨6598562645014908047034275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399041763343272031356183 6598562645014908047034275)
                ·
                  refine ⟨9897843967522362070551413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6598562645014908047034275 9897843967522362070551413)
                  ·
                    refine ⟨927922871955221444114195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9897843967522362070551413 927922871955221444114195)
                    ·
                      rfl

theorem cell22_2710685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_2710685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710685 prefixEnd_2710685 := by exact prefixLift 2710685
  have htrace : WordTrace (prefixWord ++ tailWord_2710685) baseStart_2710685 baseEnd_2710685 := by
    simpa [prefixWord, tailWord_2710685, baseEnd_2710685] using wordTrace_append hprefix tailTrace_2710685
  have hstable : (prefixWord ++ tailWord_2710685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710685).length < 2 ^ (prefixWord ++ tailWord_2710685).sum := by decide
  have hdescent : baseEnd_2710685 < baseStart_2710685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710728 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 1, 8]
def baseStart_2710728 : Nat := 118140960795 + 2710728 * 2 ^ 59
def prefixEnd_2710728 : Nat := 4983230072969 + 3 ^ 40 * 2710728 * 2
def baseEnd_2710728 : Nat := 927937591733983665289063

theorem tailTrace_2710728 : CollatzResearch.WordTrace tailWord_2710728 prefixEnd_2710728 927937591733983665289063 := by
  unfold tailWord_2710728
  simp only [CollatzResearch.WordTrace]
  refine ⟨49434186261751443164870419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65912248349001924219827225 49434186261751443164870419)
  ·
    refine ⟨74151279392627164747305629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49434186261751443164870419 74151279392627164747305629)
    ·
      refine ⟨27806729772235186780239611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74151279392627164747305629 27806729772235186780239611)
      ·
        refine ⟨41710094658352780170359417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27806729772235186780239611 41710094658352780170359417)
        ·
          refine ⟨31282570993764585127769563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41710094658352780170359417 31282570993764585127769563)
          ·
            refine ⟨46923856490646877691654345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31282570993764585127769563 46923856490646877691654345)
            ·
              refine ⟨35192892367985158268740759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46923856490646877691654345 35192892367985158268740759)
              ·
                refine ⟨52789338551977737403111139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35192892367985158268740759 52789338551977737403111139)
                ·
                  refine ⟨79184007827966606104666709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52789338551977737403111139 79184007827966606104666709)
                  ·
                    refine ⟨927937591733983665289063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79184007827966606104666709 927937591733983665289063)
                    ·
                      rfl

theorem cell22_2710728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_2710728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710728 prefixEnd_2710728 := by exact prefixLift 2710728
  have htrace : WordTrace (prefixWord ++ tailWord_2710728) baseStart_2710728 baseEnd_2710728 := by
    simpa [prefixWord, tailWord_2710728, baseEnd_2710728] using wordTrace_append hprefix tailTrace_2710728
  have hstable : (prefixWord ++ tailWord_2710728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710728).length < 2 ^ (prefixWord ++ tailWord_2710728).sum := by decide
  have hdescent : baseEnd_2710728 < baseStart_2710728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710749 : List Nat := [1, 4, 3, 2, 2, 2, 2, 6]
def baseStart_2710749 : Nat := 118140960795 + 2710749 * 2 ^ 59
def prefixEnd_2710749 : Nat := 4983230072969 + 3 ^ 40 * 2710749 * 2
def baseEnd_2710749 : Nat := 103104975607016290057111

theorem tailTrace_2710749 : CollatzResearch.WordTrace tailWord_2710749 prefixEnd_2710749 103104975607016290057111 := by
  unfold tailWord_2710749
  simp only [CollatzResearch.WordTrace]
  refine ⟨98869138456426806916255301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65912758970951204610836867 98869138456426806916255301)
  ·
    refine ⟨18537963460580026296797869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98869138456426806916255301 18537963460580026296797869)
    ·
      refine ⟨6951736297717509861299201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18537963460580026296797869 6951736297717509861299201)
      ·
        refine ⟨5213802223288132395974401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6951736297717509861299201 5213802223288132395974401)
        ·
          refine ⟨3910351667466099296980801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5213802223288132395974401 3910351667466099296980801)
          ·
            refine ⟨2932763750599574472735601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910351667466099296980801 2932763750599574472735601)
            ·
              refine ⟨2199572812949680854551701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932763750599574472735601 2199572812949680854551701)
              ·
                refine ⟨103104975607016290057111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2199572812949680854551701 103104975607016290057111)
                ·
                  rfl

theorem cell22_2710749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 2, 2, 6].length) (baseStart_2710749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710749 prefixEnd_2710749 := by exact prefixLift 2710749
  have htrace : WordTrace (prefixWord ++ tailWord_2710749) baseStart_2710749 baseEnd_2710749 := by
    simpa [prefixWord, tailWord_2710749, baseEnd_2710749] using wordTrace_append hprefix tailTrace_2710749
  have hstable : (prefixWord ++ tailWord_2710749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710749).length < 2 ^ (prefixWord ++ tailWord_2710749).sum := by decide
  have hdescent : baseEnd_2710749 < baseStart_2710749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710764 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 1, 3]
def baseStart_2710764 : Nat := 118140960795 + 2710764 * 2 ^ 59
def prefixEnd_2710764 : Nat := 4983230072969 + 3 ^ 40 * 2710764 * 2
def baseEnd_2710764 : Nat := 927949915269691571388953

theorem tailTrace_2710764 : CollatzResearch.WordTrace tailWord_2710764 prefixEnd_2710764 927949915269691571388953 := by
  unfold tailWord_2710764
  simp only [CollatzResearch.WordTrace]
  refine ⟨49434842775686232239025673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65913123700914976318700897 49434842775686232239025673)
  ·
    refine ⟨37076132081764674179269255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49434842775686232239025673 37076132081764674179269255)
    ·
      refine ⟨55614198122647011268903883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37076132081764674179269255 55614198122647011268903883)
      ·
        refine ⟨83421297183970516903355825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55614198122647011268903883 83421297183970516903355825)
        ·
          refine ⟨62565972887977887677516869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83421297183970516903355825 62565972887977887677516869)
          ·
            refine ⟨11731119916495853939534413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62565972887977887677516869 11731119916495853939534413)
            ·
              refine ⟨4399169968685945227325405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11731119916495853939534413 4399169968685945227325405)
              ·
                refine ⟨1649688738257229460247027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4399169968685945227325405 1649688738257229460247027)
                ·
                  refine ⟨2474533107385844190370541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1649688738257229460247027 2474533107385844190370541)
                  ·
                    refine ⟨927949915269691571388953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474533107385844190370541 927949915269691571388953)
                    ·
                      rfl

theorem cell22_2710764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_2710764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710764 prefixEnd_2710764 := by exact prefixLift 2710764
  have htrace : WordTrace (prefixWord ++ tailWord_2710764) baseStart_2710764 baseEnd_2710764 := by
    simpa [prefixWord, tailWord_2710764, baseEnd_2710764] using wordTrace_append hprefix tailTrace_2710764
  have hstable : (prefixWord ++ tailWord_2710764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710764).length < 2 ^ (prefixWord ++ tailWord_2710764).sum := by decide
  have hdescent : baseEnd_2710764 < baseStart_2710764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710869 : List Nat := [1, 3, 2, 2, 3, 3, 1, 1, 2, 4]
def baseStart_2710869 : Nat := 118140960795 + 2710869 * 2 ^ 59
def prefixEnd_2710869 : Nat := 4983230072969 + 3 ^ 40 * 2710869 * 2
def baseEnd_2710869 : Nat := 927985858915506297513631

theorem tailTrace_2710869 : CollatzResearch.WordTrace tailWord_2710869 prefixEnd_2710869 927985858915506297513631 := by
  unfold tailWord_2710869
  simp only [CollatzResearch.WordTrace]
  refine ⟨98873515215992067410623661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65915676810661378273749107 98873515215992067410623661)
  ·
    refine ⟨37077568205997025278983873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98873515215992067410623661 37077568205997025278983873)
    ·
      refine ⟨27808176154497768959237905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37077568205997025278983873 27808176154497768959237905)
      ·
        refine ⟨20856132115873326719428429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27808176154497768959237905 20856132115873326719428429)
        ·
          refine ⟨7821049543452497519785661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20856132115873326719428429 7821049543452497519785661)
          ·
            refine ⟨2932893578794686569919623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7821049543452497519785661 2932893578794686569919623)
            ·
              refine ⟨4399340368192029854879435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932893578794686569919623 4399340368192029854879435)
              ·
                refine ⟨6599010552288044782319153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4399340368192029854879435 6599010552288044782319153)
                ·
                  refine ⟨4949257914216033586739365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6599010552288044782319153 4949257914216033586739365)
                  ·
                    refine ⟨927985858915506297513631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949257914216033586739365 927985858915506297513631)
                    ·
                      rfl

theorem cell22_2710869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_2710869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710869 prefixEnd_2710869 := by exact prefixLift 2710869
  have htrace : WordTrace (prefixWord ++ tailWord_2710869) baseStart_2710869 baseEnd_2710869 := by
    simpa [prefixWord, tailWord_2710869, baseEnd_2710869] using wordTrace_append hprefix tailTrace_2710869
  have hstable : (prefixWord ++ tailWord_2710869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710869).length < 2 ^ (prefixWord ++ tailWord_2710869).sum := by decide
  have hdescent : baseEnd_2710869 < baseStart_2710869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710888 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 2, 3]
def baseStart_2710888 : Nat := 118140960795 + 2710888 * 2 ^ 59
def prefixEnd_2710888 : Nat := 4983230072969 + 3 ^ 40 * 2710888 * 2
def baseEnd_2710888 : Nat := 927992363003796581288573

theorem tailTrace_2710888 : CollatzResearch.WordTrace tailWord_2710888 prefixEnd_2710888 927992363003796581288573 := by
  unfold tailWord_2710888
  simp only [CollatzResearch.WordTrace]
  refine ⟨49437104101461616827782659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65916138801948822437043545 49437104101461616827782659)
  ·
    refine ⟨74155656152192425241673989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49437104101461616827782659 74155656152192425241673989)
    ·
      refine ⟨13904185528536079732813873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74155656152192425241673989 13904185528536079732813873)
      ·
        refine ⟨10428139146402059799610405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13904185528536079732813873 10428139146402059799610405)
        ·
          refine ⟨1955276089950386212426951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10428139146402059799610405 1955276089950386212426951)
          ·
            refine ⟨2932914134925579318640427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955276089950386212426951 2932914134925579318640427)
            ·
              refine ⟨4399371202388368977960641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2932914134925579318640427 4399371202388368977960641)
              ·
                refine ⟨3299528401791276733470481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4399371202388368977960641 3299528401791276733470481)
                ·
                  refine ⟨2474646301343457550102861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3299528401791276733470481 2474646301343457550102861)
                  ·
                    refine ⟨927992363003796581288573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474646301343457550102861 927992363003796581288573)
                    ·
                      rfl

theorem cell22_2710888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_2710888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710888 prefixEnd_2710888 := by exact prefixLift 2710888
  have htrace : WordTrace (prefixWord ++ tailWord_2710888) baseStart_2710888 baseEnd_2710888 := by
    simpa [prefixWord, tailWord_2710888, baseEnd_2710888] using wordTrace_append hprefix tailTrace_2710888
  have hstable : (prefixWord ++ tailWord_2710888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710888).length < 2 ^ (prefixWord ++ tailWord_2710888).sum := by decide
  have hdescent : baseEnd_2710888 < baseStart_2710888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710895 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 7]
def baseStart_2710895 : Nat := 118140960795 + 2710895 * 2 ^ 59
def prefixEnd_2710895 : Nat := 4983230072969 + 3 ^ 40 * 2710895 * 2
def baseEnd_2710895 : Nat := 309331586415616965454517

theorem tailTrace_2710895 : CollatzResearch.WordTrace tailWord_2710895 prefixEnd_2710895 309331586415616965454517 := by
  unfold tailWord_2710895
  simp only [CollatzResearch.WordTrace]
  refine ⟨98874463513897873851070139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65916309009265249234046759 98874463513897873851070139)
  ·
    refine ⟨148311695270846810776605209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98874463513897873851070139 148311695270846810776605209)
    ·
      refine ⟨111233771453135108082453907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148311695270846810776605209 111233771453135108082453907)
      ·
        refine ⟨166850657179702662123680861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111233771453135108082453907 166850657179702662123680861)
        ·
          refine ⟨62568996442388498296380323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166850657179702662123680861 62568996442388498296380323)
          ·
            refine ⟨93853494663582747444570485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62568996442388498296380323 93853494663582747444570485)
            ·
              refine ⟨8798765124710882572928483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93853494663582747444570485 8798765124710882572928483)
              ·
                refine ⟨13198147687066323859392725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8798765124710882572928483 13198147687066323859392725)
                ·
                  refine ⟨309331586415616965454517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13198147687066323859392725 309331586415616965454517)
                  ·
                    rfl

theorem cell22_2710895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 7].length) (baseStart_2710895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710895 prefixEnd_2710895 := by exact prefixLift 2710895
  have htrace : WordTrace (prefixWord ++ tailWord_2710895) baseStart_2710895 baseEnd_2710895 := by
    simpa [prefixWord, tailWord_2710895, baseEnd_2710895] using wordTrace_append hprefix tailTrace_2710895
  have hstable : (prefixWord ++ tailWord_2710895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710895).length < 2 ^ (prefixWord ++ tailWord_2710895).sum := by decide
  have hdescent : baseEnd_2710895 < baseStart_2710895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2710987 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 2, 4]
def baseStart_2710987 : Nat := 118140960795 + 2710987 * 2 ^ 59
def prefixEnd_2710987 : Nat := 4983230072969 + 3 ^ 40 * 2710987 * 2
def baseEnd_2710987 : Nat := 928026252726993323063269

theorem tailTrace_2710987 : CollatzResearch.WordTrace tailWord_2710987 prefixEnd_2710987 928026252726993323063269 := by
  unfold tailWord_2710987
  simp only [CollatzResearch.WordTrace]
  refine ⟨98877819029564573563419215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65918546019709715708946143 98877819029564573563419215)
  ·
    refine ⟨148316728544346860345128823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98877819029564573563419215 148316728544346860345128823)
    ·
      refine ⟨222475092816520290517693235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148316728544346860345128823 222475092816520290517693235)
      ·
        refine ⟨333712639224780435776539853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222475092816520290517693235 333712639224780435776539853)
        ·
          refine ⟨125142239709292663416202445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 333712639224780435776539853 125142239709292663416202445)
          ·
            refine ⟨46928339890984748781075917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125142239709292663416202445 46928339890984748781075917)
            ·
              refine ⟨17598127459119280792903469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46928339890984748781075917 17598127459119280792903469)
              ·
                refine ⟨6599297797169730297338801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17598127459119280792903469 6599297797169730297338801)
                ·
                  refine ⟨4949473347877297723004101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6599297797169730297338801 4949473347877297723004101)
                  ·
                    refine ⟨928026252726993323063269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4949473347877297723004101 928026252726993323063269)
                    ·
                      rfl

theorem cell22_2710987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_2710987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2710987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2710987 prefixEnd_2710987 := by exact prefixLift 2710987
  have htrace : WordTrace (prefixWord ++ tailWord_2710987) baseStart_2710987 baseEnd_2710987 := by
    simpa [prefixWord, tailWord_2710987, baseEnd_2710987] using wordTrace_append hprefix tailTrace_2710987
  have hstable : (prefixWord ++ tailWord_2710987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2710987).length < 2 ^ (prefixWord ++ tailWord_2710987).sum := by decide
  have hdescent : baseEnd_2710987 < baseStart_2710987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2710987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711034 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_2711034 : Nat := 118140960795 + 2711034 * 2 ^ 59
def prefixEnd_2711034 : Nat := 4983230072969 + 3 ^ 40 * 2711034 * 2
def baseEnd_2711034 : Nat := 928042341787500867138125

theorem tailTrace_2711034 : CollatzResearch.WordTrace tailWord_2711034 prefixEnd_2711034 928042341787500867138125 := by
  unfold tailWord_2711034
  simp only [CollatzResearch.WordTrace]
  refine ⟨24719883315098575147595039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65919688840262867060253437 24719883315098575147595039)
  ·
    refine ⟨37079824972647862721392559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24719883315098575147595039 37079824972647862721392559)
    ·
      refine ⟨55619737458971794082088839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37079824972647862721392559 55619737458971794082088839)
      ·
        refine ⟨83429606188457691123133259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55619737458971794082088839 83429606188457691123133259)
        ·
          refine ⟨125144409282686536684699889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83429606188457691123133259 125144409282686536684699889)
          ·
            refine ⟨93858306962014902513524917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125144409282686536684699889 93858306962014902513524917)
            ·
              refine ⟨8799216277688897110642961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93858306962014902513524917 8799216277688897110642961)
              ·
                refine ⟨6599412208266672832982221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8799216277688897110642961 6599412208266672832982221)
                ·
                  refine ⟨2474779578100002312368333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6599412208266672832982221 2474779578100002312368333)
                  ·
                    refine ⟨928042341787500867138125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2474779578100002312368333 928042341787500867138125)
                    ·
                      rfl

theorem cell22_2711034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_2711034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711034 prefixEnd_2711034 := by exact prefixLift 2711034
  have htrace : WordTrace (prefixWord ++ tailWord_2711034) baseStart_2711034 baseEnd_2711034 := by
    simpa [prefixWord, tailWord_2711034, baseEnd_2711034] using wordTrace_append hprefix tailTrace_2711034
  have hstable : (prefixWord ++ tailWord_2711034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711034).length < 2 ^ (prefixWord ++ tailWord_2711034).sum := by decide
  have hdescent : baseEnd_2711034 < baseStart_2711034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711064 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 7]
def baseStart_2711064 : Nat := 118140960795 + 2711064 * 2 ^ 59
def prefixEnd_2711064 : Nat := 4983230072969 + 3 ^ 40 * 2711064 * 2
def baseEnd_2711064 : Nat := 309350870466863596296011

theorem tailTrace_2711064 : CollatzResearch.WordTrace tailWord_2711064 prefixEnd_2711064 309350870466863596296011 := by
  unfold tailWord_2711064
  simp only [CollatzResearch.WordTrace]
  refine ⟨49440313725142807856986123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65920418300190410475981497 49440313725142807856986123)
  ·
    refine ⟨74160470587714211785479185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49440313725142807856986123 74160470587714211785479185)
    ·
      refine ⟨55620352940785658839109389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74160470587714211785479185 55620352940785658839109389)
      ·
        refine ⟨20857632352794622064666021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55620352940785658839109389 20857632352794622064666021)
        ·
          refine ⟨3910806066148991637124879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20857632352794622064666021 3910806066148991637124879)
          ·
            refine ⟨5866209099223487455687319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3910806066148991637124879 5866209099223487455687319)
            ·
              refine ⟨8799313648835231183530979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5866209099223487455687319 8799313648835231183530979)
              ·
                refine ⟨13198970473252846775296469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8799313648835231183530979 13198970473252846775296469)
                ·
                  refine ⟨309350870466863596296011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13198970473252846775296469 309350870466863596296011)
                  ·
                    rfl

theorem cell22_2711064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 7].length) (baseStart_2711064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711064 prefixEnd_2711064 := by exact prefixLift 2711064
  have htrace : WordTrace (prefixWord ++ tailWord_2711064) baseStart_2711064 baseEnd_2711064 := by
    simpa [prefixWord, tailWord_2711064, baseEnd_2711064] using wordTrace_append hprefix tailTrace_2711064
  have hstable : (prefixWord ++ tailWord_2711064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711064).length < 2 ^ (prefixWord ++ tailWord_2711064).sum := by decide
  have hdescent : baseEnd_2711064 < baseStart_2711064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711154 : List Nat := [3, 2, 1, 2, 3, 1, 2, 8]
def baseStart_2711154 : Nat := 118140960795 + 2711154 * 2 ^ 59
def prefixEnd_2711154 : Nat := 4983230072969 + 3 ^ 40 * 2711154 * 2
def baseEnd_2711154 : Nat := 103120380026651172681973

theorem tailTrace_2711154 : CollatzResearch.WordTrace tailWord_2711154 prefixEnd_2711154 103120380026651172681973 := by
  unfold tailWord_2711154
  simp only [CollatzResearch.WordTrace]
  refine ⟨24720977504989890271187129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65922606679973040723165677 24720977504989890271187129)
  ·
    refine ⟨18540733128742417703390347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24720977504989890271187129 18540733128742417703390347)
    ·
      refine ⟨27811099693113626555085521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18540733128742417703390347 27811099693113626555085521)
      ·
        refine ⟨20858324769835219916314141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27811099693113626555085521 20858324769835219916314141)
        ·
          refine ⟨7821871788688207468617803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20858324769835219916314141 7821871788688207468617803)
          ·
            refine ⟨11732807683032311202926705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7821871788688207468617803 11732807683032311202926705)
            ·
              refine ⟨8799605762274233402195029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11732807683032311202926705 8799605762274233402195029)
              ·
                refine ⟨103120380026651172681973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8799605762274233402195029 103120380026651172681973)
                ·
                  rfl

theorem cell22_2711154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 8].length) (baseStart_2711154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711154 prefixEnd_2711154 := by exact prefixLift 2711154
  have htrace : WordTrace (prefixWord ++ tailWord_2711154) baseStart_2711154 baseEnd_2711154 := by
    simpa [prefixWord, tailWord_2711154, baseEnd_2711154] using wordTrace_append hprefix tailTrace_2711154
  have hstable : (prefixWord ++ tailWord_2711154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711154).length < 2 ^ (prefixWord ++ tailWord_2711154).sum := by decide
  have hdescent : baseEnd_2711154 < baseStart_2711154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711188 : List Nat := [2, 4, 2, 2, 2, 2, 1, 7]
def baseStart_2711188 : Nat := 118140960795 + 2711188 * 2 ^ 59
def prefixEnd_2711188 : Nat := 4983230072969 + 3 ^ 40 * 2711188 * 2
def baseEnd_2711188 : Nat := 103121673237188422087517

theorem tailTrace_2711188 : CollatzResearch.WordTrace tailWord_2711188 prefixEnd_2711188 103121673237188422087517 := by
  unfold tailWord_2711188
  simp only [CollatzResearch.WordTrace]
  refine ⟨49442575050918192445743109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65923433401224256594324145 49442575050918192445743109)
  ·
    refine ⟨9270482822047161083576833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49442575050918192445743109 9270482822047161083576833)
    ·
      refine ⟨6952862116535370812682625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9270482822047161083576833 6952862116535370812682625)
      ·
        refine ⟨5214646587401528109511969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6952862116535370812682625 5214646587401528109511969)
        ·
          refine ⟨3910984940551146082133977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5214646587401528109511969 3910984940551146082133977)
          ·
            refine ⟨2933238705413359561600483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910984940551146082133977 2933238705413359561600483)
            ·
              refine ⟨4399858058120039342400725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933238705413359561600483 4399858058120039342400725)
              ·
                refine ⟨103121673237188422087517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4399858058120039342400725 103121673237188422087517)
                ·
                  rfl

theorem cell22_2711188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 2, 1, 7].length) (baseStart_2711188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711188 prefixEnd_2711188 := by exact prefixLift 2711188
  have htrace : WordTrace (prefixWord ++ tailWord_2711188) baseStart_2711188 baseEnd_2711188 := by
    simpa [prefixWord, tailWord_2711188, baseEnd_2711188] using wordTrace_append hprefix tailTrace_2711188
  have hstable : (prefixWord ++ tailWord_2711188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711188).length < 2 ^ (prefixWord ++ tailWord_2711188).sum := by decide
  have hdescent : baseEnd_2711188 < baseStart_2711188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711276 : List Nat := [2, 2, 1, 1, 2, 2, 3, 2, 4, 3]
def baseStart_2711276 : Nat := 118140960795 + 2711276 * 2 ^ 59
def prefixEnd_2711276 : Nat := 4983230072969 + 3 ^ 40 * 2711276 * 2
def baseEnd_2711276 : Nat := 928125183333092902587383

theorem tailTrace_2711276 : CollatzResearch.WordTrace tailWord_2711276 prefixEnd_2711276 928125183333092902587383 := by
  unfold tailWord_2711276
  simp only [CollatzResearch.WordTrace]
  refine ⟨49444179862758787960344841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65925573150345050613793121 49444179862758787960344841)
  ·
    refine ⟨37083134897069090970258631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49444179862758787960344841 37083134897069090970258631)
    ·
      refine ⟨55624702345603636455387947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37083134897069090970258631 55624702345603636455387947)
      ·
        refine ⟨83437053518405454683081921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55624702345603636455387947 83437053518405454683081921)
        ·
          refine ⟨62577790138804091012311441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83437053518405454683081921 62577790138804091012311441)
          ·
            refine ⟨46933342604103068259233581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62577790138804091012311441 46933342604103068259233581)
            ·
              refine ⟨17600003476538650597212593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46933342604103068259233581 17600003476538650597212593)
              ·
                refine ⟨13200002607403987947909445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17600003476538650597212593 13200002607403987947909445)
                ·
                  refine ⟨2475000488888247740233021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13200002607403987947909445 2475000488888247740233021)
                  ·
                    refine ⟨928125183333092902587383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475000488888247740233021 928125183333092902587383)
                    ·
                      rfl

theorem cell22_2711276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 3].length) (baseStart_2711276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711276 prefixEnd_2711276 := by exact prefixLift 2711276
  have htrace : WordTrace (prefixWord ++ tailWord_2711276) baseStart_2711276 baseEnd_2711276 := by
    simpa [prefixWord, tailWord_2711276, baseEnd_2711276] using wordTrace_append hprefix tailTrace_2711276
  have hstable : (prefixWord ++ tailWord_2711276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711276).length < 2 ^ (prefixWord ++ tailWord_2711276).sum := by decide
  have hdescent : baseEnd_2711276 < baseStart_2711276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711306 : List Nat := [3, 1, 2, 2, 1, 4, 2, 7]
def baseStart_2711306 : Nat := 118140960795 + 2711306 * 2 ^ 59
def prefixEnd_2711306 : Nat := 4983230072969 + 3 ^ 40 * 2711306 * 2
def baseEnd_2711306 : Nat := 103126161438464758259699

theorem tailTrace_2711306 : CollatzResearch.WordTrace tailWord_2711306 prefixEnd_2711306 103126161438464758259699 := by
  unfold tailWord_2711306
  simp only [CollatzResearch.WordTrace]
  refine ⟨24722363478852222761070443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65926302610272594029521181 24722363478852222761070443)
  ·
    refine ⟨37083545218278334141605665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24722363478852222761070443 37083545218278334141605665)
    ·
      refine ⟨27812658913708750606204249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37083545218278334141605665 27812658913708750606204249)
      ·
        refine ⟨20859494185281562954653187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27812658913708750606204249 20859494185281562954653187)
        ·
          refine ⟨31289241277922344431979781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20859494185281562954653187 31289241277922344431979781)
          ·
            refine ⟨5866732739610439580996209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31289241277922344431979781 5866732739610439580996209)
            ·
              refine ⟨4400049554707829685747157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5866732739610439580996209 4400049554707829685747157)
              ·
                refine ⟨103126161438464758259699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4400049554707829685747157 103126161438464758259699)
                ·
                  rfl

theorem cell22_2711306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 7].length) (baseStart_2711306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711306 prefixEnd_2711306 := by exact prefixLift 2711306
  have htrace : WordTrace (prefixWord ++ tailWord_2711306) baseStart_2711306 baseEnd_2711306 := by
    simpa [prefixWord, tailWord_2711306, baseEnd_2711306] using wordTrace_append hprefix tailTrace_2711306
  have hstable : (prefixWord ++ tailWord_2711306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711306).length < 2 ^ (prefixWord ++ tailWord_2711306).sum := by decide
  have hdescent : baseEnd_2711306 < baseStart_2711306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711310 : List Nat := [4, 1, 1, 2, 1, 1, 6, 1, 2, 3]
def baseStart_2711310 : Nat := 118140960795 + 2711310 * 2 ^ 59
def prefixEnd_2711310 : Nat := 4983230072969 + 3 ^ 40 * 2711310 * 2
def baseEnd_2711310 : Nat := 928136822227928147237279

theorem tailTrace_2711310 : CollatzResearch.WordTrace tailWord_2711310 prefixEnd_2711310 928136822227928147237279 := by
  unfold tailWord_2711310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12361199975924299965928423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65926399871596266484951589 12361199975924299965928423)
  ·
    refine ⟨18541799963886449948892635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12361199975924299965928423 18541799963886449948892635)
    ·
      refine ⟨27812699945829674923338953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18541799963886449948892635 27812699945829674923338953)
      ·
        refine ⟨20859524959372256192504215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27812699945829674923338953 20859524959372256192504215)
        ·
          refine ⟨31289287439058384288756323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20859524959372256192504215 31289287439058384288756323)
          ·
            refine ⟨46933931158587576433134485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31289287439058384288756323 46933931158587576433134485)
            ·
              refine ⟨2200028023058792645303179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46933931158587576433134485 2200028023058792645303179)
              ·
                refine ⟨3300042034588188967954769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200028023058792645303179 3300042034588188967954769)
                ·
                  refine ⟨2475031525941141725966077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3300042034588188967954769 2475031525941141725966077)
                  ·
                    refine ⟨928136822227928147237279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475031525941141725966077 928136822227928147237279)
                    ·
                      rfl

theorem cell22_2711310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_2711310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711310 prefixEnd_2711310 := by exact prefixLift 2711310
  have htrace : WordTrace (prefixWord ++ tailWord_2711310) baseStart_2711310 baseEnd_2711310 := by
    simpa [prefixWord, tailWord_2711310, baseEnd_2711310] using wordTrace_append hprefix tailTrace_2711310
  have hstable : (prefixWord ++ tailWord_2711310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711310).length < 2 ^ (prefixWord ++ tailWord_2711310).sum := by decide
  have hdescent : baseEnd_2711310 < baseStart_2711310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711402 : List Nat := [3, 1, 3, 4, 1, 2, 1, 2, 5]
def baseStart_2711402 : Nat := 118140960795 + 2711402 * 2 ^ 59
def prefixEnd_2711402 : Nat := 4983230072969 + 3 ^ 40 * 2711402 * 2
def baseEnd_2711402 : Nat := 309389438569356857978999

theorem tailTrace_2711402 : CollatzResearch.WordTrace tailWord_2711402 prefixEnd_2711402 309389438569356857978999 := by
  unfold tailWord_2711402
  simp only [CollatzResearch.WordTrace]
  refine ⟨24723238830765274859944115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65928636882040732959850973 24723238830765274859944115)
  ·
    refine ⟨37084858246147912289916173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24723238830765274859944115 37084858246147912289916173)
    ·
      refine ⟨13906821842305467108718565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37084858246147912289916173 13906821842305467108718565)
      ·
        refine ⟨2607529095432275082884731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13906821842305467108718565 2607529095432275082884731)
        ·
          refine ⟨3911293643148412624327097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2607529095432275082884731 3911293643148412624327097)
          ·
            refine ⟨2933470232361309468245323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3911293643148412624327097 2933470232361309468245323)
            ·
              refine ⟨4400205348541964202367985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933470232361309468245323 4400205348541964202367985)
              ·
                refine ⟨3300154011406473151775989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4400205348541964202367985 3300154011406473151775989)
                ·
                  refine ⟨309389438569356857978999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3300154011406473151775989 309389438569356857978999)
                  ·
                    rfl

theorem cell22_2711402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_2711402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711402 prefixEnd_2711402 := by exact prefixLift 2711402
  have htrace : WordTrace (prefixWord ++ tailWord_2711402) baseStart_2711402 baseEnd_2711402 := by
    simpa [prefixWord, tailWord_2711402, baseEnd_2711402] using wordTrace_append hprefix tailTrace_2711402
  have hstable : (prefixWord ++ tailWord_2711402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711402).length < 2 ^ (prefixWord ++ tailWord_2711402).sum := by decide
  have hdescent : baseEnd_2711402 < baseStart_2711402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711413 : List Nat := [1, 3, 4, 1, 1, 1, 4, 1, 6]
def baseStart_2711413 : Nat := 118140960795 + 2711413 * 2 ^ 59
def prefixEnd_2711413 : Nat := 4983230072969 + 3 ^ 40 * 2711413 * 2
def baseEnd_2711413 : Nat := 309390693744290070637321

theorem tailTrace_2711413 : CollatzResearch.WordTrace tailWord_2711413 prefixEnd_2711413 309390693744290070637321 := by
  unfold tailWord_2711413
  simp only [CollatzResearch.WordTrace]
  refine ⟨98893356526021248318426893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65928904350680832212284595 98893356526021248318426893)
  ·
    refine ⟨37085008697257968119410085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98893356526021248318426893 37085008697257968119410085)
    ·
      refine ⟨6953439130735869022389391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37085008697257968119410085 6953439130735869022389391)
      ·
        refine ⟨10430158696103803533584087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6953439130735869022389391 10430158696103803533584087)
        ·
          refine ⟨15645238044155705300376131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10430158696103803533584087 15645238044155705300376131)
          ·
            refine ⟨23467857066233557950564197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15645238044155705300376131 23467857066233557950564197)
            ·
              refine ⟨4400223199918792115730787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23467857066233557950564197 4400223199918792115730787)
              ·
                refine ⟨6600334799878188173596181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400223199918792115730787 6600334799878188173596181)
                ·
                  refine ⟨309390693744290070637321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6600334799878188173596181 309390693744290070637321)
                  ·
                    rfl

theorem cell22_2711413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_2711413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711413 prefixEnd_2711413 := by exact prefixLift 2711413
  have htrace : WordTrace (prefixWord ++ tailWord_2711413) baseStart_2711413 baseEnd_2711413 := by
    simpa [prefixWord, tailWord_2711413, baseEnd_2711413] using wordTrace_append hprefix tailTrace_2711413
  have hstable : (prefixWord ++ tailWord_2711413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711413).length < 2 ^ (prefixWord ++ tailWord_2711413).sum := by decide
  have hdescent : baseEnd_2711413 < baseStart_2711413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711428 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2711428 : Nat := 118140960795 + 2711428 * 2 ^ 59
def prefixEnd_2711428 : Nat := 4983230072969 + 3 ^ 40 * 2711428 * 2
def baseEnd_2711428 : Nat := 928177216039415172786917

theorem tailTrace_2711428 : CollatzResearch.WordTrace tailWord_2711428 prefixEnd_2711428 928177216039415172786917 := by
  unfold tailWord_2711428
  simp only [CollatzResearch.WordTrace]
  refine ⟨49446951810483452940111469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65929269080644603920148625 49446951810483452940111469)
  ·
    refine ⟨18542606928931294852541801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49446951810483452940111469 18542606928931294852541801)
    ·
      refine ⟨13906955196698471139406351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18542606928931294852541801 13906955196698471139406351)
      ·
        refine ⟨20860432795047706709109527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13906955196698471139406351 20860432795047706709109527)
        ·
          refine ⟨31290649192571560063664291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20860432795047706709109527 31290649192571560063664291)
          ·
            refine ⟨46935973788857340095496437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31290649192571560063664291 46935973788857340095496437)
            ·
              refine ⟨4400247542705375633952791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46935973788857340095496437 4400247542705375633952791)
              ·
                refine ⟨6600371314058063450929187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400247542705375633952791 6600371314058063450929187)
                ·
                  refine ⟨9900556971087095176393781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6600371314058063450929187 9900556971087095176393781)
                  ·
                    refine ⟨928177216039415172786917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9900556971087095176393781 928177216039415172786917)
                    ·
                      rfl

theorem cell22_2711428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2711428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711428 prefixEnd_2711428 := by exact prefixLift 2711428
  have htrace : WordTrace (prefixWord ++ tailWord_2711428) baseStart_2711428 baseEnd_2711428 := by
    simpa [prefixWord, tailWord_2711428, baseEnd_2711428] using wordTrace_append hprefix tailTrace_2711428
  have hstable : (prefixWord ++ tailWord_2711428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711428).length < 2 ^ (prefixWord ++ tailWord_2711428).sum := by decide
  have hdescent : baseEnd_2711428 < baseStart_2711428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711464 : List Nat := [2, 1, 6, 2, 2, 1, 1, 1, 6]
def baseStart_2711464 : Nat := 118140960795 + 2711464 * 2 ^ 59
def prefixEnd_2711464 : Nat := 4983230072969 + 3 ^ 40 * 2711464 * 2
def baseEnd_2711464 : Nat := 309396513191707692962269

theorem tailTrace_2711464 : CollatzResearch.WordTrace tailWord_2711464 prefixEnd_2711464 309396513191707692962269 := by
  unfold tailWord_2711464
  simp only [CollatzResearch.WordTrace]
  refine ⟨49447608324418242014266723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65930144432557656019022297 49447608324418242014266723)
  ·
    refine ⟨74171412486627363021400085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49447608324418242014266723 74171412486627363021400085)
    ·
      refine ⟨3476784960310657641628129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74171412486627363021400085 3476784960310657641628129)
      ·
        refine ⟨2607588720232993231221097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3476784960310657641628129 2607588720232993231221097)
        ·
          refine ⟨1955691540174744923415823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607588720232993231221097 1955691540174744923415823)
          ·
            refine ⟨2933537310262117385123735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955691540174744923415823 2933537310262117385123735)
            ·
              refine ⟨4400305965393176077685603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933537310262117385123735 4400305965393176077685603)
              ·
                refine ⟨6600458948089764116528405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400305965393176077685603 6600458948089764116528405)
                ·
                  refine ⟨309396513191707692962269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6600458948089764116528405 309396513191707692962269)
                  ·
                    rfl

theorem cell22_2711464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_2711464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711464 prefixEnd_2711464 := by exact prefixLift 2711464
  have htrace : WordTrace (prefixWord ++ tailWord_2711464) baseStart_2711464 baseEnd_2711464 := by
    simpa [prefixWord, tailWord_2711464, baseEnd_2711464] using wordTrace_append hprefix tailTrace_2711464
  have hstable : (prefixWord ++ tailWord_2711464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711464).length < 2 ^ (prefixWord ++ tailWord_2711464).sum := by decide
  have hdescent : baseEnd_2711464 < baseStart_2711464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711471 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 2, 6]
def baseStart_2711471 : Nat := 118140960795 + 2711471 * 2 ^ 59
def prefixEnd_2711471 : Nat := 4983230072969 + 3 ^ 40 * 2711471 * 2
def baseEnd_2711471 : Nat := 928191935818177393961785

theorem tailTrace_2711471 : CollatzResearch.WordTrace tailWord_2711471 prefixEnd_2711471 928191935818177393961785 := by
  unfold tailWord_2711471
  simp only [CollatzResearch.WordTrace]
  refine ⟨98895471959811124224038267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65930314639874082816025511 98895471959811124224038267)
  ·
    refine ⟨148343207939716686336057401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98895471959811124224038267 148343207939716686336057401)
    ·
      refine ⟨111257405954787514752043051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148343207939716686336057401 111257405954787514752043051)
      ·
        refine ⟨166886108932181272128064577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111257405954787514752043051 166886108932181272128064577)
        ·
          refine ⟨125164581699135954096048433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166886108932181272128064577 125164581699135954096048433)
          ·
            refine ⟨93873436274351965572036325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125164581699135954096048433 93873436274351965572036325)
            ·
              refine ⟨17601269301440993544756811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93873436274351965572036325 17601269301440993544756811)
              ·
                refine ⟨26401903952161490317135217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17601269301440993544756811 26401903952161490317135217)
                ·
                  refine ⟨19801427964121117737851413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26401903952161490317135217 19801427964121117737851413)
                  ·
                    refine ⟨928191935818177393961785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19801427964121117737851413 928191935818177393961785)
                    ·
                      rfl

theorem cell22_2711471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 6].length) (baseStart_2711471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711471 prefixEnd_2711471 := by exact prefixLift 2711471
  have htrace : WordTrace (prefixWord ++ tailWord_2711471) baseStart_2711471 baseEnd_2711471 := by
    simpa [prefixWord, tailWord_2711471, baseEnd_2711471] using wordTrace_append hprefix tailTrace_2711471
  have hstable : (prefixWord ++ tailWord_2711471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711471).length < 2 ^ (prefixWord ++ tailWord_2711471).sum := by decide
  have hdescent : baseEnd_2711471 < baseStart_2711471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711531 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 10]
def baseStart_2711531 : Nat := 118140960795 + 2711531 * 2 ^ 59
def prefixEnd_2711531 : Nat := 4983230072969 + 3 ^ 40 * 2711531 * 2
def baseEnd_2711531 : Nat := 309404158348119079153867

theorem tailTrace_2711531 : CollatzResearch.WordTrace tailWord_2711531 prefixEnd_2711531 309404158348119079153867 := by
  unfold tailWord_2711531
  simp only [CollatzResearch.WordTrace]
  refine ⟨98897660339593754471222447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65931773559729169647481631 98897660339593754471222447)
  ·
    refine ⟨148346490509390631706833671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98897660339593754471222447 148346490509390631706833671)
    ·
      refine ⟨222519735764085947560250507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148346490509390631706833671 222519735764085947560250507)
      ·
        refine ⟨333779603646128921340375761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222519735764085947560250507 333779603646128921340375761)
        ·
          refine ⟨250334702734596691005281821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333779603646128921340375761 250334702734596691005281821)
          ·
            refine ⟨93875513525473759126980683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250334702734596691005281821 93875513525473759126980683)
            ·
              refine ⟨140813270288210638690471025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93875513525473759126980683 140813270288210638690471025)
              ·
                refine ⟨105609952716157979017853269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140813270288210638690471025 105609952716157979017853269)
                ·
                  refine ⟨309404158348119079153867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105609952716157979017853269 309404158348119079153867)
                  ·
                    rfl

theorem cell22_2711531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 10].length) (baseStart_2711531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711531 prefixEnd_2711531 := by exact prefixLift 2711531
  have htrace : WordTrace (prefixWord ++ tailWord_2711531) baseStart_2711531 baseEnd_2711531 := by
    simpa [prefixWord, tailWord_2711531, baseEnd_2711531] using wordTrace_append hprefix tailTrace_2711531
  have hstable : (prefixWord ++ tailWord_2711531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711531).length < 2 ^ (prefixWord ++ tailWord_2711531).sum := by decide
  have hdescent : baseEnd_2711531 < baseStart_2711531 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711548 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_2711548 : Nat := 118140960795 + 2711548 * 2 ^ 59
def prefixEnd_2711548 : Nat := 4983230072969 + 3 ^ 40 * 2711548 * 2
def baseEnd_2711548 : Nat := 309406098163924953262183

theorem tailTrace_2711548 : CollatzResearch.WordTrace tailWord_2711548 prefixEnd_2711548 309406098163924953262183 := by
  unfold tailWord_2711548
  simp only [CollatzResearch.WordTrace]
  refine ⟨49449140190266083187295649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65932186920354777583060865 49449140190266083187295649)
  ·
    refine ⟨37086855142699562390471737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49449140190266083187295649 37086855142699562390471737)
    ·
      refine ⟨27815141357024671792853803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37086855142699562390471737 27815141357024671792853803)
      ·
        refine ⟨41722712035537007689280705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27815141357024671792853803 41722712035537007689280705)
        ·
          refine ⟨31292034026652755766960529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41722712035537007689280705 31292034026652755766960529)
          ·
            refine ⟨23469025519989566825220397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31292034026652755766960529 23469025519989566825220397)
            ·
              refine ⟨8800884569996087559457649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23469025519989566825220397 8800884569996087559457649)
              ·
                refine ⟨6600663427497065669593237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8800884569996087559457649 6600663427497065669593237)
                ·
                  refine ⟨309406098163924953262183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6600663427497065669593237 309406098163924953262183)
                  ·
                    rfl

theorem cell22_2711548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_2711548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711548 prefixEnd_2711548 := by exact prefixLift 2711548
  have htrace : WordTrace (prefixWord ++ tailWord_2711548) baseStart_2711548 baseEnd_2711548 := by
    simpa [prefixWord, tailWord_2711548, baseEnd_2711548] using wordTrace_append hprefix tailTrace_2711548
  have hstable : (prefixWord ++ tailWord_2711548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711548).length < 2 ^ (prefixWord ++ tailWord_2711548).sum := by decide
  have hdescent : baseEnd_2711548 < baseStart_2711548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711563 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 1, 5]
def baseStart_2711563 : Nat := 118140960795 + 2711563 * 2 ^ 59
def prefixEnd_2711563 : Nat := 4983230072969 + 3 ^ 40 * 2711563 * 2
def baseEnd_2711563 : Nat := 928223429298319820661503

theorem tailTrace_2711563 : CollatzResearch.WordTrace tailWord_2711563 prefixEnd_2711563 928223429298319820661503 := by
  unfold tailWord_2711563
  simp only [CollatzResearch.WordTrace]
  refine ⟨98898827475477823936387343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65932551650318549290924895 98898827475477823936387343)
  ·
    refine ⟨148348241213216735904581015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98898827475477823936387343 148348241213216735904581015)
    ·
      refine ⟨222522361819825103856871523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148348241213216735904581015 222522361819825103856871523)
      ·
        refine ⟨333783542729737655785307285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222522361819825103856871523 333783542729737655785307285)
        ·
          refine ⟨15646103565456452614936279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 333783542729737655785307285 15646103565456452614936279)
          ·
            refine ⟨23469155348184678922404419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15646103565456452614936279 23469155348184678922404419)
            ·
              refine ⟨35203733022277018383606629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23469155348184678922404419 35203733022277018383606629)
              ·
                refine ⟨6600699941676940946926243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35203733022277018383606629 6600699941676940946926243)
                ·
                  refine ⟨9901049912515411420389365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6600699941676940946926243 9901049912515411420389365)
                  ·
                    refine ⟨928223429298319820661503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901049912515411420389365 928223429298319820661503)
                    ·
                      rfl

theorem cell22_2711563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_2711563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711563 prefixEnd_2711563 := by exact prefixLift 2711563
  have htrace : WordTrace (prefixWord ++ tailWord_2711563) baseStart_2711563 baseEnd_2711563 := by
    simpa [prefixWord, tailWord_2711563, baseEnd_2711563] using wordTrace_append hprefix tailTrace_2711563
  have hstable : (prefixWord ++ tailWord_2711563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711563).length < 2 ^ (prefixWord ++ tailWord_2711563).sum := by decide
  have hdescent : baseEnd_2711563 < baseStart_2711563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711655 : List Nat := [1, 1, 5, 1, 1, 2, 3, 3, 5]
def baseStart_2711655 : Nat := 118140960795 + 2711655 * 2 ^ 59
def prefixEnd_2711655 : Nat := 4983230072969 + 3 ^ 40 * 2711655 * 2
def baseEnd_2711655 : Nat := 309418307592820749120407

theorem tailTrace_2711655 : CollatzResearch.WordTrace tailWord_2711655 prefixEnd_2711655 309418307592820749120407 := by
  unfold tailWord_2711655
  simp only [CollatzResearch.WordTrace]
  refine ⟨98902182991144523648736419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65934788660763015765824279 98902182991144523648736419)
  ·
    refine ⟨148353274486716785473104629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98902182991144523648736419 148353274486716785473104629)
    ·
      refine ⟨13908119483129698638103559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148353274486716785473104629 13908119483129698638103559)
      ·
        refine ⟨20862179224694547957155339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13908119483129698638103559 20862179224694547957155339)
        ·
          refine ⟨31293268837041821935733009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20862179224694547957155339 31293268837041821935733009)
          ·
            refine ⟨23469951627781366451799757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31293268837041821935733009 23469951627781366451799757)
            ·
              refine ⟨8801231860418012419424909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23469951627781366451799757 8801231860418012419424909)
              ·
                refine ⟨3300461947656754657284341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8801231860418012419424909 3300461947656754657284341)
                ·
                  refine ⟨309418307592820749120407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3300461947656754657284341 309418307592820749120407)
                  ·
                    rfl

theorem cell22_2711655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 5].length) (baseStart_2711655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711655 prefixEnd_2711655 := by exact prefixLift 2711655
  have htrace : WordTrace (prefixWord ++ tailWord_2711655) baseStart_2711655 baseEnd_2711655 := by
    simpa [prefixWord, tailWord_2711655, baseEnd_2711655] using wordTrace_append hprefix tailTrace_2711655
  have hstable : (prefixWord ++ tailWord_2711655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711655).length < 2 ^ (prefixWord ++ tailWord_2711655).sum := by decide
  have hdescent : baseEnd_2711655 < baseStart_2711655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711715 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 8, 3]
def baseStart_2711715 : Nat := 118140960795 + 2711715 * 2 ^ 59
def prefixEnd_2711715 : Nat := 4983230072969 + 3 ^ 40 * 2711715 * 2
def baseEnd_2711715 : Nat := 928275462004642090861037

theorem tailTrace_2711715 : CollatzResearch.WordTrace tailWord_2711715 prefixEnd_2711715 928275462004642090861037 := by
  unfold tailWord_2711715
  simp only [CollatzResearch.WordTrace]
  refine ⟨98904371370927153895920599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65936247580618102597280399 98904371370927153895920599)
  ·
    refine ⟨148356557056390730843880899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98904371370927153895920599 148356557056390730843880899)
    ·
      refine ⟨222534835584586096265821349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148356557056390730843880899 222534835584586096265821349)
      ·
        refine ⟨41725281672109893049841503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222534835584586096265821349 41725281672109893049841503)
        ·
          refine ⟨62587922508164839574762255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41725281672109893049841503 62587922508164839574762255)
          ·
            refine ⟨93881883762247259362143383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62587922508164839574762255 93881883762247259362143383)
            ·
              refine ⟨140822825643370889043215075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93881883762247259362143383 140822825643370889043215075)
              ·
                refine ⟨211234238465056333564822613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140822825643370889043215075 211234238465056333564822613)
                ·
                  refine ⟨2475401232012378908962765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 211234238465056333564822613 2475401232012378908962765)
                  ·
                    refine ⟨928275462004642090861037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475401232012378908962765 928275462004642090861037)
                    ·
                      rfl

theorem cell22_2711715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 8, 3].length) (baseStart_2711715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711715 prefixEnd_2711715 := by exact prefixLift 2711715
  have htrace : WordTrace (prefixWord ++ tailWord_2711715) baseStart_2711715 baseEnd_2711715 := by
    simpa [prefixWord, tailWord_2711715, baseEnd_2711715] using wordTrace_append hprefix tailTrace_2711715
  have hstable : (prefixWord ++ tailWord_2711715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711715).length < 2 ^ (prefixWord ++ tailWord_2711715).sum := by decide
  have hdescent : baseEnd_2711715 < baseStart_2711715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711730 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_2711730 : Nat := 118140960795 + 2711730 * 2 ^ 59
def prefixEnd_2711730 : Nat := 4983230072969 + 3 ^ 40 * 2711730 * 2
def baseEnd_2711730 : Nat := 928280596811187051735991

theorem tailTrace_2711730 : CollatzResearch.WordTrace tailWord_2711730 prefixEnd_2711730 928280596811187051735991 := by
  unfold tailWord_2711730
  simp only [CollatzResearch.WordTrace]
  refine ⟨24726229616468202864429161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65936612310581874305144429 24726229616468202864429161)
  ·
    refine ⟨18544672212351152148321871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24726229616468202864429161 18544672212351152148321871)
    ·
      refine ⟨27817008318526728222482807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18544672212351152148321871 27817008318526728222482807)
      ·
        refine ⟨41725512477790092333724211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27817008318526728222482807 41725512477790092333724211)
        ·
          refine ⟨62588268716685138500586317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41725512477790092333724211 62588268716685138500586317)
          ·
            refine ⟨23470600768756926937719869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62588268716685138500586317 23470600768756926937719869)
            ·
              refine ⟨8801475288283847601644951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23470600768756926937719869 8801475288283847601644951)
              ·
                refine ⟨13202212932425771402467427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8801475288283847601644951 13202212932425771402467427)
                ·
                  refine ⟨19803319398638657103701141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13202212932425771402467427 19803319398638657103701141)
                  ·
                    refine ⟨928280596811187051735991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19803319398638657103701141 928280596811187051735991)
                    ·
                      rfl

theorem cell22_2711730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_2711730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711730 prefixEnd_2711730 := by exact prefixLift 2711730
  have htrace : WordTrace (prefixWord ++ tailWord_2711730) baseStart_2711730 baseEnd_2711730 := by
    simpa [prefixWord, tailWord_2711730, baseEnd_2711730] using wordTrace_append hprefix tailTrace_2711730
  have hstable : (prefixWord ++ tailWord_2711730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711730).length < 2 ^ (prefixWord ++ tailWord_2711730).sum := by decide
  have hdescent : baseEnd_2711730 < baseStart_2711730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711766 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2711766 : Nat := 118140960795 + 2711766 * 2 ^ 59
def prefixEnd_2711766 : Nat := 4983230072969 + 3 ^ 40 * 2711766 * 2
def baseEnd_2711766 : Nat := 928292920346894957835881

theorem tailTrace_2711766 : CollatzResearch.WordTrace tailWord_2711766 prefixEnd_2711766 928292920346894957835881 := by
  unfold tailWord_2711766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181639468358899350376697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65937487662494926404018101 6181639468358899350376697)
  ·
    refine ⟨4636229601269174512782523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6181639468358899350376697 4636229601269174512782523)
    ·
      refine ⟨6954344401903761769173785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636229601269174512782523 6954344401903761769173785)
      ·
        refine ⟨5215758301427821326880339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6954344401903761769173785 5215758301427821326880339)
        ·
          refine ⟨7823637452141731990320509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5215758301427821326880339 7823637452141731990320509)
          ·
            refine ⟨2933864044553149496370191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7823637452141731990320509 2933864044553149496370191)
            ·
              refine ⟨4400796066829724244555287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933864044553149496370191 4400796066829724244555287)
              ·
                refine ⟨6601194100244586366832931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4400796066829724244555287 6601194100244586366832931)
                ·
                  refine ⟨9901791150366879550249397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601194100244586366832931 9901791150366879550249397)
                  ·
                    refine ⟨928292920346894957835881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901791150366879550249397 928292920346894957835881)
                    ·
                      rfl

theorem cell22_2711766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2711766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711766 prefixEnd_2711766 := by exact prefixLift 2711766
  have htrace : WordTrace (prefixWord ++ tailWord_2711766) baseStart_2711766 baseEnd_2711766 := by
    simpa [prefixWord, tailWord_2711766, baseEnd_2711766] using wordTrace_append hprefix tailTrace_2711766
  have hstable : (prefixWord ++ tailWord_2711766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711766).length < 2 ^ (prefixWord ++ tailWord_2711766).sum := by decide
  have hdescent : baseEnd_2711766 < baseStart_2711766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711777 : List Nat := [1, 2, 3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_2711777 : Nat := 118140960795 + 2711777 * 2 ^ 59
def prefixEnd_2711777 : Nat := 4983230072969 + 3 ^ 40 * 2711777 * 2
def baseEnd_2711777 : Nat := 928296685871694595810847

theorem tailTrace_2711777 : CollatzResearch.WordTrace tailWord_2711777 prefixEnd_2711777 928296685871694595810847 := by
  unfold tailWord_2711777
  simp only [CollatzResearch.WordTrace]
  refine ⟨98906632696702538484677585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65937755131135025656451723 98906632696702538484677585)
  ·
    refine ⟨74179974522526903863508189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98906632696702538484677585 74179974522526903863508189)
    ·
      refine ⟨27817490445947588948815571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74179974522526903863508189 27817490445947588948815571)
      ·
        refine ⟨41726235668921383423223357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27817490445947588948815571 41726235668921383423223357)
        ·
          refine ⟨15647338375845518783708759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41726235668921383423223357 15647338375845518783708759)
          ·
            refine ⟨23471007563768278175563139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647338375845518783708759 23471007563768278175563139)
            ·
              refine ⟨35206511345652417263344709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23471007563768278175563139 35206511345652417263344709)
              ·
                refine ⟨6601220877309828236877133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35206511345652417263344709 6601220877309828236877133)
                ·
                  refine ⟨2475457828991185588828925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6601220877309828236877133 2475457828991185588828925)
                  ·
                    refine ⟨928296685871694595810847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475457828991185588828925 928296685871694595810847)
                    ·
                      rfl

theorem cell22_2711777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_2711777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711777 prefixEnd_2711777 := by exact prefixLift 2711777
  have htrace : WordTrace (prefixWord ++ tailWord_2711777) baseStart_2711777 baseEnd_2711777 := by
    simpa [prefixWord, tailWord_2711777, baseEnd_2711777] using wordTrace_append hprefix tailTrace_2711777
  have hstable : (prefixWord ++ tailWord_2711777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711777).length < 2 ^ (prefixWord ++ tailWord_2711777).sum := by decide
  have hdescent : baseEnd_2711777 < baseStart_2711777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711805 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 4, 5]
def baseStart_2711805 : Nat := 118140960795 + 2711805 * 2 ^ 59
def prefixEnd_2711805 : Nat := 4983230072969 + 3 ^ 40 * 2711805 * 2
def baseEnd_2711805 : Nat := 928306270843911856110761

theorem tailTrace_2711805 : CollatzResearch.WordTrace tailWord_2711805 prefixEnd_2711805 928306270843911856110761 := by
  unfold tailWord_2711805
  simp only [CollatzResearch.WordTrace]
  refine ⟨98907653940601099266696869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65938435960400732844464579 98907653940601099266696869)
  ·
    refine ⟨18545185113862706112505663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98907653940601099266696869 18545185113862706112505663)
    ·
      refine ⟨27817777670794059168758495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18545185113862706112505663 27817777670794059168758495)
      ·
        refine ⟨41726666506191088753137743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27817777670794059168758495 41726666506191088753137743)
        ·
          refine ⟨62589999759286633129706615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41726666506191088753137743 62589999759286633129706615)
          ·
            refine ⟨93884999638929949694559923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62589999759286633129706615 93884999638929949694559923)
            ·
              refine ⟨140827499458394924541839885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93884999638929949694559923 140827499458394924541839885)
              ·
                refine ⟨52810312296898096703189957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140827499458394924541839885 52810312296898096703189957)
                ·
                  refine ⟨9901933555668393131848117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52810312296898096703189957 9901933555668393131848117)
                  ·
                    refine ⟨928306270843911856110761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9901933555668393131848117 928306270843911856110761)
                    ·
                      rfl

theorem cell22_2711805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_2711805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711805 prefixEnd_2711805 := by exact prefixLift 2711805
  have htrace : WordTrace (prefixWord ++ tailWord_2711805) baseStart_2711805 baseEnd_2711805 := by
    simpa [prefixWord, tailWord_2711805, baseEnd_2711805] using wordTrace_append hprefix tailTrace_2711805
  have hstable : (prefixWord ++ tailWord_2711805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711805).length < 2 ^ (prefixWord ++ tailWord_2711805).sum := by decide
  have hdescent : baseEnd_2711805 < baseStart_2711805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711811 : List Nat := [1, 1, 1, 3, 2, 3, 5, 2, 1, 3]
def baseStart_2711811 : Nat := 118140960795 + 2711811 * 2 ^ 59
def prefixEnd_2711811 : Nat := 4983230072969 + 3 ^ 40 * 2711811 * 2
def baseEnd_2711811 : Nat := 928308324766529840460743

theorem tailTrace_2711811 : CollatzResearch.WordTrace tailWord_2711811 prefixEnd_2711811 928308324766529840460743 := by
  unfold tailWord_2711811
  simp only [CollatzResearch.WordTrace]
  refine ⟨98907872778579362291415287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65938581852386241527610191 98907872778579362291415287)
  ·
    refine ⟨148361809167869043437122931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98907872778579362291415287 148361809167869043437122931)
    ·
      refine ⟨222542713751803565155684397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148361809167869043437122931 222542713751803565155684397)
      ·
        refine ⟨83453517656926336933381649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222542713751803565155684397 83453517656926336933381649)
        ·
          refine ⟨62590138242694752700036237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83453517656926336933381649 62590138242694752700036237)
          ·
            refine ⟨23471301841010532262513589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62590138242694752700036237 23471301841010532262513589)
            ·
              refine ⟨2200434547594737399610649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23471301841010532262513589 2200434547594737399610649)
              ·
                refine ⟨1650325910696053049707987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2200434547594737399610649 1650325910696053049707987)
                ·
                  refine ⟨2475488866044079574561981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650325910696053049707987 2475488866044079574561981)
                  ·
                    refine ⟨928308324766529840460743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475488866044079574561981 928308324766529840460743)
                    ·
                      rfl

theorem cell22_2711811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 2, 1, 3].length) (baseStart_2711811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711811 prefixEnd_2711811 := by exact prefixLift 2711811
  have htrace : WordTrace (prefixWord ++ tailWord_2711811) baseStart_2711811 baseEnd_2711811 := by
    simpa [prefixWord, tailWord_2711811, baseEnd_2711811] using wordTrace_append hprefix tailTrace_2711811
  have hstable : (prefixWord ++ tailWord_2711811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711811).length < 2 ^ (prefixWord ++ tailWord_2711811).sum := by decide
  have hdescent : baseEnd_2711811 < baseStart_2711811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711835 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 6]
def baseStart_2711835 : Nat := 118140960795 + 2711835 * 2 ^ 59
def prefixEnd_2711835 : Nat := 4983230072969 + 3 ^ 40 * 2711835 * 2
def baseEnd_2711835 : Nat := 309438846819000592620223

theorem tailTrace_2711835 : CollatzResearch.WordTrace tailWord_2711835 prefixEnd_2711835 309438846819000592620223 := by
  unfold tailWord_2711835
  simp only [CollatzResearch.WordTrace]
  refine ⟨98908748130492414390288959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65939165420328276260192639 98908748130492414390288959)
  ·
    refine ⟨148363122195738621585433439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98908748130492414390288959 148363122195738621585433439)
    ·
      refine ⟨222544683293607932378150159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148363122195738621585433439 222544683293607932378150159)
      ·
        refine ⟨333817024940411898567225239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222544683293607932378150159 333817024940411898567225239)
        ·
          refine ⟨500725537410617847850837859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333817024940411898567225239 500725537410617847850837859)
          ·
            refine ⟨751088306115926771776256789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500725537410617847850837859 751088306115926771776256789)
            ·
              refine ⟨35207264349184067427012037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 751088306115926771776256789 35207264349184067427012037)
              ·
                refine ⟨6601362065472012642564757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35207264349184067427012037 6601362065472012642564757)
                ·
                  refine ⟨309438846819000592620223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6601362065472012642564757 309438846819000592620223)
                  ·
                    rfl

theorem cell22_2711835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 6].length) (baseStart_2711835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711835 prefixEnd_2711835 := by exact prefixLift 2711835
  have htrace : WordTrace (prefixWord ++ tailWord_2711835) baseStart_2711835 baseEnd_2711835 := by
    simpa [prefixWord, tailWord_2711835, baseEnd_2711835] using wordTrace_append hprefix tailTrace_2711835
  have hstable : (prefixWord ++ tailWord_2711835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711835).length < 2 ^ (prefixWord ++ tailWord_2711835).sum := by decide
  have hdescent : baseEnd_2711835 < baseStart_2711835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2711884 : List Nat := [2, 2, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_2711884 : Nat := 118140960795 + 2711884 * 2 ^ 59
def prefixEnd_2711884 : Nat := 4983230072969 + 3 ^ 40 * 2711884 * 2
def baseEnd_2711884 : Nat := 928333314158381983385519

theorem tailTrace_2711884 : CollatzResearch.WordTrace tailWord_2711884 prefixEnd_2711884 928333314158381983385519 := by
  unfold tailWord_2711884
  simp only [CollatzResearch.WordTrace]
  refine ⟨49455267653657447879411353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65940356871543263839215137 49455267653657447879411353)
  ·
    refine ⟨37091450740243085909558515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49455267653657447879411353 37091450740243085909558515)
    ·
      refine ⟨55637176110364628864337773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37091450740243085909558515 55637176110364628864337773)
      ·
        refine ⟨20863941041386735824126665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55637176110364628864337773 20863941041386735824126665)
        ·
          refine ⟨15647955781040051868094999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20863941041386735824126665 15647955781040051868094999)
          ·
            refine ⟨23471933671560077802142499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15647955781040051868094999 23471933671560077802142499)
            ·
              refine ⟨35207900507340116703213749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23471933671560077802142499 35207900507340116703213749)
              ·
                refine ⟨3300740672563135940926289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35207900507340116703213749 3300740672563135940926289)
                ·
                  refine ⟨2475555504422351955694717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3300740672563135940926289 2475555504422351955694717)
                  ·
                    refine ⟨928333314158381983385519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475555504422351955694717 928333314158381983385519)
                    ·
                      rfl

theorem cell22_2711884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_2711884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2711884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2711884 prefixEnd_2711884 := by exact prefixLift 2711884
  have htrace : WordTrace (prefixWord ++ tailWord_2711884) baseStart_2711884 baseEnd_2711884 := by
    simpa [prefixWord, tailWord_2711884, baseEnd_2711884] using wordTrace_append hprefix tailTrace_2711884
  have hstable : (prefixWord ++ tailWord_2711884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2711884).length < 2 ^ (prefixWord ++ tailWord_2711884).sum := by decide
  have hdescent : baseEnd_2711884 < baseStart_2711884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2711884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712017 : List Nat := [1, 2, 2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2712017 : Nat := 118140960795 + 2712017 * 2 ^ 59
def prefixEnd_2712017 : Nat := 4983230072969 + 3 ^ 40 * 2712017 * 2
def baseEnd_2712017 : Nat := 928378842776413969810111

theorem tailTrace_2712017 : CollatzResearch.WordTrace tailWord_2712017 prefixEnd_2712017 928378842776413969810111 := by
  unfold tailWord_2712017
  simp only [CollatzResearch.WordTrace]
  refine ⟨98915386215833059473414305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65943590810555372982276203 98915386215833059473414305)
  ·
    refine ⟨74186539661874794605060729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98915386215833059473414305 74186539661874794605060729)
    ·
      refine ⟨55639904746406095953795547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74186539661874794605060729 55639904746406095953795547)
      ·
        refine ⟨83459857119609143930693321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55639904746406095953795547 83459857119609143930693321)
        ·
          refine ⟨62594892839706857948019991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83459857119609143930693321 62594892839706857948019991)
          ·
            refine ⟨93892339259560286922029987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62594892839706857948019991 93892339259560286922029987)
            ·
              refine ⟨140838508889340430383044981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93892339259560286922029987 140838508889340430383044981)
              ·
                refine ⟨13203610208375665348410467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 140838508889340430383044981 13203610208375665348410467)
                ·
                  refine ⟨19805415312563498022615701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13203610208375665348410467 19805415312563498022615701)
                  ·
                    refine ⟨928378842776413969810111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19805415312563498022615701 928378842776413969810111)
                    ·
                      rfl

theorem cell22_2712017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2712017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712017 prefixEnd_2712017 := by exact prefixLift 2712017
  have htrace : WordTrace (prefixWord ++ tailWord_2712017) baseStart_2712017 baseEnd_2712017 := by
    simpa [prefixWord, tailWord_2712017, baseEnd_2712017] using wordTrace_append hprefix tailTrace_2712017
  have hstable : (prefixWord ++ tailWord_2712017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712017).length < 2 ^ (prefixWord ++ tailWord_2712017).sum := by decide
  have hdescent : baseEnd_2712017 < baseStart_2712017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712047 : List Nat := [1, 1, 2, 1, 4, 1, 1, 2, 2, 7]
def baseStart_2712047 : Nat := 118140960795 + 2712047 * 2 ^ 59
def prefixEnd_2712047 : Nat := 4983230072969 + 3 ^ 40 * 2712047 * 2
def baseEnd_2712047 : Nat := 928389112389503891560019

theorem tailTrace_2712047 : CollatzResearch.WordTrace tailWord_2712047 prefixEnd_2712047 928389112389503891560019 := by
  unfold tailWord_2712047
  simp only [CollatzResearch.WordTrace]
  refine ⟨98916480405724374597006395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65944320270482916398004263 98916480405724374597006395)
  ·
    refine ⟨148374720608586561895509593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98916480405724374597006395 148374720608586561895509593)
    ·
      refine ⟨111281040456439921421632195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148374720608586561895509593 111281040456439921421632195)
      ·
        refine ⟨166921560684659882132448293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111281040456439921421632195 166921560684659882132448293)
        ·
          refine ⟨31297792628373727899834055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166921560684659882132448293 31297792628373727899834055)
          ·
            refine ⟨46946688942560591849751083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31297792628373727899834055 46946688942560591849751083)
            ·
              refine ⟨70420033413840887774626625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46946688942560591849751083 70420033413840887774626625)
              ·
                refine ⟨52815025060380665830969969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70420033413840887774626625 52815025060380665830969969)
                ·
                  refine ⟨39611268795285499373227477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52815025060380665830969969 39611268795285499373227477)
                  ·
                    refine ⟨928389112389503891560019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39611268795285499373227477 928389112389503891560019)
                    ·
                      rfl

theorem cell22_2712047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 7].length) (baseStart_2712047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712047 prefixEnd_2712047 := by exact prefixLift 2712047
  have htrace : WordTrace (prefixWord ++ tailWord_2712047) baseStart_2712047 baseEnd_2712047 := by
    simpa [prefixWord, tailWord_2712047, baseEnd_2712047] using wordTrace_append hprefix tailTrace_2712047
  have hstable : (prefixWord ++ tailWord_2712047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712047).length < 2 ^ (prefixWord ++ tailWord_2712047).sum := by decide
  have hdescent : baseEnd_2712047 < baseStart_2712047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712053 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2712053 : Nat := 118140960795 + 2712053 * 2 ^ 59
def prefixEnd_2712053 : Nat := 4983230072969 + 3 ^ 40 * 2712053 * 2
def baseEnd_2712053 : Nat := 928391166312121875910001

theorem tailTrace_2712053 : CollatzResearch.WordTrace tailWord_2712053 prefixEnd_2712053 928391166312121875910001 := by
  unfold tailWord_2712053
  simp only [CollatzResearch.WordTrace]
  refine ⟨98916699243702637621724813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65944466162468425081149875 98916699243702637621724813)
  ·
    refine ⟨37093762216388489108146805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98916699243702637621724813 37093762216388489108146805)
    ·
      refine ⟨3477540207786420853888763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37093762216388489108146805 3477540207786420853888763)
      ·
        refine ⟨5216310311679631280833145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477540207786420853888763 5216310311679631280833145)
        ·
          refine ⟨3912232733759723460624859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5216310311679631280833145 3912232733759723460624859)
          ·
            refine ⟨5868349100639585190937289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912232733759723460624859 5868349100639585190937289)
            ·
              refine ⟨4401261825479688893202967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5868349100639585190937289 4401261825479688893202967)
              ·
                refine ⟨6601892738219533339804451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401261825479688893202967 6601892738219533339804451)
                ·
                  refine ⟨9902839107329300009706677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601892738219533339804451 9902839107329300009706677)
                  ·
                    refine ⟨928391166312121875910001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9902839107329300009706677 928391166312121875910001)
                    ·
                      rfl

theorem cell22_2712053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2712053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712053 prefixEnd_2712053 := by exact prefixLift 2712053
  have htrace : WordTrace (prefixWord ++ tailWord_2712053) baseStart_2712053 baseEnd_2712053 := by
    simpa [prefixWord, tailWord_2712053, baseEnd_2712053] using wordTrace_append hprefix tailTrace_2712053
  have hstable : (prefixWord ++ tailWord_2712053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712053).length < 2 ^ (prefixWord ++ tailWord_2712053).sum := by decide
  have hdescent : baseEnd_2712053 < baseStart_2712053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712068 : List Nat := [2, 3, 2, 3, 1, 3, 1, 1, 2, 4]
def baseStart_2712068 : Nat := 118140960795 + 2712068 * 2 ^ 59
def prefixEnd_2712068 : Nat := 4983230072969 + 3 ^ 40 * 2712068 * 2
def baseEnd_2712068 : Nat := 928396301118666836784955

theorem tailTrace_2712068 : CollatzResearch.WordTrace tailWord_2712068 prefixEnd_2712068 928396301118666836784955 := by
  unfold tailWord_2712068
  simp only [CollatzResearch.WordTrace]
  refine ⟨49458623169324147591760429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65944830892432196789013905 49458623169324147591760429)
  ·
    refine ⟨18546983688496555346910161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49458623169324147591760429 18546983688496555346910161)
    ·
      refine ⟨13910237766372416510182621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18546983688496555346910161 13910237766372416510182621)
      ·
        refine ⟨5216339162389656191318483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13910237766372416510182621 5216339162389656191318483)
        ·
          refine ⟨7824508743584484286977725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216339162389656191318483 7824508743584484286977725)
          ·
            refine ⟨2934190778844181607616647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7824508743584484286977725 2934190778844181607616647)
            ·
              refine ⟨4401286168266272411424971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934190778844181607616647 4401286168266272411424971)
              ·
                refine ⟨6601929252399408617137457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4401286168266272411424971 6601929252399408617137457)
                ·
                  refine ⟨4951446939299556462853093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6601929252399408617137457 4951446939299556462853093)
                  ·
                    refine ⟨928396301118666836784955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951446939299556462853093 928396301118666836784955)
                    ·
                      rfl

theorem cell22_2712068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_2712068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712068 prefixEnd_2712068 := by exact prefixLift 2712068
  have htrace : WordTrace (prefixWord ++ tailWord_2712068) baseStart_2712068 baseEnd_2712068 := by
    simpa [prefixWord, tailWord_2712068, baseEnd_2712068] using wordTrace_append hprefix tailTrace_2712068
  have hstable : (prefixWord ++ tailWord_2712068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712068).length < 2 ^ (prefixWord ++ tailWord_2712068).sum := by decide
  have hdescent : baseEnd_2712068 < baseStart_2712068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712070 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_2712070 : Nat := 118140960795 + 2712070 * 2 ^ 59
def prefixEnd_2712070 : Nat := 4983230072969 + 3 ^ 40 * 2712070 * 2
def baseEnd_2712070 : Nat := 928396985759539498234949

theorem tailTrace_2712070 : CollatzResearch.WordTrace tailWord_2712070 prefixEnd_2712070 928396985759539498234949 := by
  unfold tailWord_2712070
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091166227645032797659177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65944879523094033016729109 3091166227645032797659177)
  ·
    refine ⟨2318374670733774598244383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3091166227645032797659177 2318374670733774598244383)
    ·
      refine ⟨3477562006100661897366575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318374670733774598244383 3477562006100661897366575)
      ·
        refine ⟨5216343009150992846049863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3477562006100661897366575 5216343009150992846049863)
        ·
          refine ⟨7824514513726489269074795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5216343009150992846049863 7824514513726489269074795)
          ·
            refine ⟨11736771770589733903612193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7824514513726489269074795 11736771770589733903612193)
            ·
              refine ⟨8802578827942300427709145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11736771770589733903612193 8802578827942300427709145)
              ·
                refine ⟨6601934120956725320781859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8802578827942300427709145 6601934120956725320781859)
                ·
                  refine ⟨9902901181435087981172789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6601934120956725320781859 9902901181435087981172789)
                  ·
                    refine ⟨928396985759539498234949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9902901181435087981172789 928396985759539498234949)
                    ·
                      rfl

theorem cell22_2712070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_2712070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712070 prefixEnd_2712070 := by exact prefixLift 2712070
  have htrace : WordTrace (prefixWord ++ tailWord_2712070) baseStart_2712070 baseEnd_2712070 := by
    simpa [prefixWord, tailWord_2712070, baseEnd_2712070] using wordTrace_append hprefix tailTrace_2712070
  have hstable : (prefixWord ++ tailWord_2712070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712070).length < 2 ^ (prefixWord ++ tailWord_2712070).sum := by decide
  have hdescent : baseEnd_2712070 < baseStart_2712070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712087 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 2, 3]
def baseStart_2712087 : Nat := 118140960795 + 2712087 * 2 ^ 59
def prefixEnd_2712087 : Nat := 4983230072969 + 3 ^ 40 * 2712087 * 2
def baseEnd_2712087 : Nat := 928402805206957120559897

theorem tailTrace_2712087 : CollatzResearch.WordTrace tailWord_2712087 prefixEnd_2712087 928402805206957120559897 := by
  unfold tailWord_2712087
  simp only [CollatzResearch.WordTrace]
  refine ⟨98917939325579461428462515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65945292883719640952308343 98917939325579461428462515)
  ·
    refine ⟨148376908988369192142693773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98917939325579461428462515 148376908988369192142693773)
    ·
      refine ⟨55641340870638447053510165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148376908988369192142693773 55641340870638447053510165)
      ·
        refine ⟨2608187853311177205633289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55641340870638447053510165 2608187853311177205633289)
        ·
          refine ⟨1956140889983382904224967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2608187853311177205633289 1956140889983382904224967)
          ·
            refine ⟨2934211334975074356337451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956140889983382904224967 2934211334975074356337451)
            ·
              refine ⟨4401317002462611534506177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934211334975074356337451 4401317002462611534506177)
              ·
                refine ⟨3300987751846958650879633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401317002462611534506177 3300987751846958650879633)
                ·
                  refine ⟨2475740813885218988159725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3300987751846958650879633 2475740813885218988159725)
                  ·
                    refine ⟨928402805206957120559897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475740813885218988159725 928402805206957120559897)
                    ·
                      rfl

theorem cell22_2712087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 2, 3].length) (baseStart_2712087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712087 prefixEnd_2712087 := by exact prefixLift 2712087
  have htrace : WordTrace (prefixWord ++ tailWord_2712087) baseStart_2712087 baseEnd_2712087 := by
    simpa [prefixWord, tailWord_2712087, baseEnd_2712087] using wordTrace_append hprefix tailTrace_2712087
  have hstable : (prefixWord ++ tailWord_2712087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712087).length < 2 ^ (prefixWord ++ tailWord_2712087).sum := by decide
  have hdescent : baseEnd_2712087 < baseStart_2712087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712162 : List Nat := [3, 3, 2, 3, 1, 2, 2, 1, 5]
def baseStart_2712162 : Nat := 118140960795 + 2712162 * 2 ^ 59
def prefixEnd_2712162 : Nat := 4983230072969 + 3 ^ 40 * 2712162 * 2
def baseEnd_2712162 : Nat := 309476159746560641644889

theorem tailTrace_2712162 : CollatzResearch.WordTrace tailWord_2712162 prefixEnd_2712162 309476159746560641644889 := by
  unfold tailWord_2712162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24730168700076937309360685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65947116533538499491628493 24730168700076937309360685)
  ·
    refine ⟨9273813262528851491010257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24730168700076937309360685 9273813262528851491010257)
    ·
      refine ⟨6955359946896638618257693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9273813262528851491010257 6955359946896638618257693)
      ·
        refine ⟨2608259980086239481846635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6955359946896638618257693 2608259980086239481846635)
        ·
          refine ⟨3912389970129359222769953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608259980086239481846635 3912389970129359222769953)
          ·
            refine ⟨2934292477597019417077465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3912389970129359222769953 2934292477597019417077465)
            ·
              refine ⟨2200719358197764562808099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2934292477597019417077465 2200719358197764562808099)
              ·
                refine ⟨3301079037296646844212149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200719358197764562808099 3301079037296646844212149)
                ·
                  refine ⟨309476159746560641644889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301079037296646844212149 309476159746560641644889)
                  ·
                    rfl

theorem cell22_2712162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_2712162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712162 prefixEnd_2712162 := by exact prefixLift 2712162
  have htrace : WordTrace (prefixWord ++ tailWord_2712162) baseStart_2712162 baseEnd_2712162 := by
    simpa [prefixWord, tailWord_2712162, baseEnd_2712162] using wordTrace_append hprefix tailTrace_2712162
  have hstable : (prefixWord ++ tailWord_2712162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712162).length < 2 ^ (prefixWord ++ tailWord_2712162).sum := by decide
  have hdescent : baseEnd_2712162 < baseStart_2712162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712169 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_2712169 : Nat := 118140960795 + 2712169 * 2 ^ 59
def prefixEnd_2712169 : Nat := 4983230072969 + 3 ^ 40 * 2712169 * 2
def baseEnd_2712169 : Nat := 928430875482736240009645

theorem tailTrace_2712169 : CollatzResearch.WordTrace tailWord_2712169 prefixEnd_2712169 928430875482736240009645 := by
  unfold tailWord_2712169
  simp only [CollatzResearch.WordTrace]
  refine ⟨98920930111282389432947561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65947286740854926288631707 98920930111282389432947561)
  ·
    refine ⟨74190697583461792074710671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98920930111282389432947561 74190697583461792074710671)
    ·
      refine ⟨111286046375192688112066007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74190697583461792074710671 111286046375192688112066007)
      ·
        refine ⟨166929069562789032168099011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111286046375192688112066007 166929069562789032168099011)
        ·
          refine ⟨250393604344183548252148517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166929069562789032168099011 250393604344183548252148517)
          ·
            refine ⟨46948800814534415297277847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250393604344183548252148517 46948800814534415297277847)
            ·
              refine ⟨70423201221801622945916771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46948800814534415297277847 70423201221801622945916771)
              ·
                refine ⟨105634801832702434418875157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70423201221801622945916771 105634801832702434418875157)
                ·
                  refine ⟨4951631335907926613384773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105634801832702434418875157 4951631335907926613384773)
                  ·
                    refine ⟨928430875482736240009645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951631335907926613384773 928430875482736240009645)
                    ·
                      rfl

theorem cell22_2712169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_2712169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712169 prefixEnd_2712169 := by exact prefixLift 2712169
  have htrace : WordTrace (prefixWord ++ tailWord_2712169) baseStart_2712169 baseEnd_2712169 := by
    simpa [prefixWord, tailWord_2712169, baseEnd_2712169] using wordTrace_append hprefix tailTrace_2712169
  have hstable : (prefixWord ++ tailWord_2712169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712169).length < 2 ^ (prefixWord ++ tailWord_2712169).sum := by decide
  have hdescent : baseEnd_2712169 < baseStart_2712169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712229 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 9]
def baseStart_2712229 : Nat := 118140960795 + 2712229 * 2 ^ 59
def prefixEnd_2712229 : Nat := 4983230072969 + 3 ^ 40 * 2712229 * 2
def baseEnd_2712229 : Nat := 309483804902972027836487

theorem tailTrace_2712229 : CollatzResearch.WordTrace tailWord_2712229 prefixEnd_2712229 309483804902972027836487 := by
  unfold tailWord_2712229
  simp only [CollatzResearch.WordTrace]
  refine ⟨98923118491065019680131741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65948745660710013120087827 98923118491065019680131741)
  ·
    refine ⟨37096169434149382380049403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98923118491065019680131741 37096169434149382380049403)
    ·
      refine ⟨55644254151224073570074105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37096169434149382380049403 55644254151224073570074105)
      ·
        refine ⟨41733190613418055177555579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55644254151224073570074105 41733190613418055177555579)
        ·
          refine ⟨62599785920127082766333369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41733190613418055177555579 62599785920127082766333369)
          ·
            refine ⟨46949839440095312074750027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62599785920127082766333369 46949839440095312074750027)
            ·
              refine ⟨70424759160142968112125041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46949839440095312074750027 70424759160142968112125041)
              ·
                refine ⟨52818569370107226084093781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70424759160142968112125041 52818569370107226084093781)
                ·
                  refine ⟨309483804902972027836487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52818569370107226084093781 309483804902972027836487)
                  ·
                    rfl

theorem cell22_2712229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_2712229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712229 prefixEnd_2712229 := by exact prefixLift 2712229
  have htrace : WordTrace (prefixWord ++ tailWord_2712229) baseStart_2712229 baseEnd_2712229 := by
    simpa [prefixWord, tailWord_2712229, baseEnd_2712229] using wordTrace_append hprefix tailTrace_2712229
  have hstable : (prefixWord ++ tailWord_2712229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712229).length < 2 ^ (prefixWord ++ tailWord_2712229).sum := by decide
  have hdescent : baseEnd_2712229 < baseStart_2712229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712250 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_2712250 : Nat := 118140960795 + 2712250 * 2 ^ 59
def prefixEnd_2712250 : Nat := 4983230072969 + 3 ^ 40 * 2712250 * 2
def baseEnd_2712250 : Nat := 928458603438079028734397

theorem tailTrace_2712250 : CollatzResearch.WordTrace tailWord_2712250 prefixEnd_2712250 928458603438079028734397 := by
  unfold tailWord_2712250
  simp only [CollatzResearch.WordTrace]
  refine ⟨24730971105997235066661551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65949256282659293511097469 24730971105997235066661551)
  ·
    refine ⟨37096456658995852599992327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24730971105997235066661551 37096456658995852599992327)
    ·
      refine ⟨55644684988493778899988491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37096456658995852599992327 55644684988493778899988491)
      ·
        refine ⟨83467027482740668349982737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55644684988493778899988491 83467027482740668349982737)
        ·
          refine ⟨62600270612055501262487053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83467027482740668349982737 62600270612055501262487053)
          ·
            refine ⟨23475101479520812973432645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62600270612055501262487053 23475101479520812973432645)
            ·
              refine ⟨4401581527410152432518621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23475101479520812973432645 4401581527410152432518621)
              ·
                refine ⟨1650593072778807162194483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4401581527410152432518621 1650593072778807162194483)
                ·
                  refine ⟨2475889609168210743291725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650593072778807162194483 2475889609168210743291725)
                  ·
                    refine ⟨928458603438079028734397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475889609168210743291725 928458603438079028734397)
                    ·
                      rfl

theorem cell22_2712250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_2712250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712250 prefixEnd_2712250 := by exact prefixLift 2712250
  have htrace : WordTrace (prefixWord ++ tailWord_2712250) baseStart_2712250 baseEnd_2712250 := by
    simpa [prefixWord, tailWord_2712250, baseEnd_2712250] using wordTrace_append hprefix tailTrace_2712250
  have hstable : (prefixWord ++ tailWord_2712250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712250).length < 2 ^ (prefixWord ++ tailWord_2712250).sum := by decide
  have hdescent : baseEnd_2712250 < baseStart_2712250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712293 : List Nat := [1, 3, 1, 4, 1, 2, 1, 4, 1, 4]
def baseStart_2712293 : Nat := 118140960795 + 2712293 * 2 ^ 59
def prefixEnd_2712293 : Nat := 4983230072969 + 3 ^ 40 * 2712293 * 2
def baseEnd_2712293 : Nat := 928473323216841249909265

theorem tailTrace_2712293 : CollatzResearch.WordTrace tailWord_2712293 prefixEnd_2712293 928473323216841249909265 := by
  unfold tailWord_2712293
  simp only [CollatzResearch.WordTrace]
  refine ⟨98925452762833158610461533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65950301841888772406974355 98925452762833158610461533)
  ·
    refine ⟨37097044786062434478923075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98925452762833158610461533 37097044786062434478923075)
    ·
      refine ⟨55645567179093651718384613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37097044786062434478923075 55645567179093651718384613)
      ·
        refine ⟨10433543846080059697197115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55645567179093651718384613 10433543846080059697197115)
        ·
          refine ⟨15650315769120089545795673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10433543846080059697197115 15650315769120089545795673)
          ·
            refine ⟨11737736826840067159346755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15650315769120089545795673 11737736826840067159346755)
            ·
              refine ⟨17606605240260100739020133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11737736826840067159346755 17606605240260100739020133)
              ·
                refine ⟨3301238482548768888566275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17606605240260100739020133 3301238482548768888566275)
                ·
                  refine ⟨4951857723823153332849413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301238482548768888566275 4951857723823153332849413)
                  ·
                    refine ⟨928473323216841249909265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4951857723823153332849413 928473323216841249909265)
                    ·
                      rfl

theorem cell22_2712293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_2712293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712293 prefixEnd_2712293 := by exact prefixLift 2712293
  have htrace : WordTrace (prefixWord ++ tailWord_2712293) baseStart_2712293 baseEnd_2712293 := by
    simpa [prefixWord, tailWord_2712293, baseEnd_2712293] using wordTrace_append hprefix tailTrace_2712293
  have hstable : (prefixWord ++ tailWord_2712293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712293).length < 2 ^ (prefixWord ++ tailWord_2712293).sum := by decide
  have hdescent : baseEnd_2712293 < baseStart_2712293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712323 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 2, 3]
def baseStart_2712323 : Nat := 118140960795 + 2712323 * 2 ^ 59
def prefixEnd_2712323 : Nat := 4983230072969 + 3 ^ 40 * 2712323 * 2
def baseEnd_2712323 : Nat := 928483592829931171659173

theorem tailTrace_2712323 : CollatzResearch.WordTrace tailWord_2712323 prefixEnd_2712323 928483592829931171659173 := by
  unfold tailWord_2712323
  simp only [CollatzResearch.WordTrace]
  refine ⟨98926546952724473734053623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65951031301816315822702415 98926546952724473734053623)
  ·
    refine ⟨148389820429086710601080435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98926546952724473734053623 148389820429086710601080435)
    ·
      refine ⟨222584730643630065901620653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148389820429086710601080435 222584730643630065901620653)
      ·
        refine ⟨83469273991361274713107745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222584730643630065901620653 83469273991361274713107745)
        ·
          refine ⟨62601955493520956034830809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83469273991361274713107745 62601955493520956034830809)
          ·
            refine ⟨46951466620140717026123107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62601955493520956034830809 46951466620140717026123107)
            ·
              refine ⟨70427199930211075539184661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46951466620140717026123107 70427199930211075539184661)
              ·
                refine ⟨3301274996728644165899281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70427199930211075539184661 3301274996728644165899281)
                ·
                  refine ⟨2475956247546483124424461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301274996728644165899281 2475956247546483124424461)
                  ·
                    refine ⟨928483592829931171659173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2475956247546483124424461 928483592829931171659173)
                    ·
                      rfl

theorem cell22_2712323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 2, 3].length) (baseStart_2712323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712323 prefixEnd_2712323 := by exact prefixLift 2712323
  have htrace : WordTrace (prefixWord ++ tailWord_2712323) baseStart_2712323 baseEnd_2712323 := by
    simpa [prefixWord, tailWord_2712323, baseEnd_2712323] using wordTrace_append hprefix tailTrace_2712323
  have hstable : (prefixWord ++ tailWord_2712323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712323).length < 2 ^ (prefixWord ++ tailWord_2712323).sum := by decide
  have hdescent : baseEnd_2712323 < baseStart_2712323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712374 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 2, 3]
def baseStart_2712374 : Nat := 118140960795 + 2712374 * 2 ^ 59
def prefixEnd_2712374 : Nat := 4983230072969 + 3 ^ 40 * 2712374 * 2
def baseEnd_2712374 : Nat := 928501051172184038634017

theorem tailTrace_2712374 : CollatzResearch.WordTrace tailWord_2712374 prefixEnd_2712374 928501051172184038634017 := by
  unfold tailWord_2712374
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183025442221231840260011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65952271383693139629440117 6183025442221231840260011)
  ·
    refine ⟨9274538163331847760390017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6183025442221231840260011 9274538163331847760390017)
    ·
      refine ⟨6955903622498885820292513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9274538163331847760390017 6955903622498885820292513)
      ·
        refine ⟨5216927716874164365219385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6955903622498885820292513 5216927716874164365219385)
        ·
          refine ⟨3912695787655623273914539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5216927716874164365219385 3912695787655623273914539)
          ·
            refine ⟨5869043681483434910871809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3912695787655623273914539 5869043681483434910871809)
            ·
              refine ⟨4401782761112576183153857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5869043681483434910871809 4401782761112576183153857)
              ·
                refine ⟨3301337070834432137365393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4401782761112576183153857 3301337070834432137365393)
                ·
                  refine ⟨2476002803125824103024045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3301337070834432137365393 2476002803125824103024045)
                  ·
                    refine ⟨928501051172184038634017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476002803125824103024045 928501051172184038634017)
                    ·
                      rfl

theorem cell22_2712374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_2712374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712374 prefixEnd_2712374 := by exact prefixLift 2712374
  have htrace : WordTrace (prefixWord ++ tailWord_2712374) baseStart_2712374 baseEnd_2712374 := by
    simpa [prefixWord, tailWord_2712374, baseEnd_2712374] using wordTrace_append hprefix tailTrace_2712374
  have hstable : (prefixWord ++ tailWord_2712374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712374).length < 2 ^ (prefixWord ++ tailWord_2712374).sum := by decide
  have hdescent : baseEnd_2712374 < baseStart_2712374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712473 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_2712473 : Nat := 118140960795 + 2712473 * 2 ^ 59
def prefixEnd_2712473 : Nat := 4983230072969 + 3 ^ 40 * 2712473 * 2
def baseEnd_2712473 : Nat := 928534940895380780408713

theorem tailTrace_2712473 : CollatzResearch.WordTrace tailWord_2712473 prefixEnd_2712473 928534940895380780408713 := by
  unfold tailWord_2712473
  simp only [CollatzResearch.WordTrace]
  refine ⟨98932017902181049352014073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65954678601454032901342715 98932017902181049352014073)
  ·
    refine ⟨74199013426635787014010555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98932017902181049352014073 74199013426635787014010555)
    ·
      refine ⟨111298520139953680521015833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74199013426635787014010555 111298520139953680521015833)
      ·
        refine ⟨83473890104965260390761875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111298520139953680521015833 83473890104965260390761875)
        ·
          refine ⟨125210835157447890586142813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83473890104965260390761875 125210835157447890586142813)
          ·
            refine ⟨46954063184042958969803555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125210835157447890586142813 46954063184042958969803555)
            ·
              refine ⟨70431094776064438454705333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46954063184042958969803555 70431094776064438454705333)
              ·
                refine ⟨6602915135256041105128625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70431094776064438454705333 6602915135256041105128625)
                ·
                  refine ⟨4952186351442030828846469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6602915135256041105128625 4952186351442030828846469)
                  ·
                    refine ⟨928534940895380780408713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952186351442030828846469 928534940895380780408713)
                    ·
                      rfl

theorem cell22_2712473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_2712473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712473 prefixEnd_2712473 := by exact prefixLift 2712473
  have htrace : WordTrace (prefixWord ++ tailWord_2712473) baseStart_2712473 baseEnd_2712473 := by
    simpa [prefixWord, tailWord_2712473, baseEnd_2712473] using wordTrace_append hprefix tailTrace_2712473
  have hstable : (prefixWord ++ tailWord_2712473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712473).length < 2 ^ (prefixWord ++ tailWord_2712473).sum := by decide
  have hdescent : baseEnd_2712473 < baseStart_2712473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712554 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2712554 : Nat := 118140960795 + 2712554 * 2 ^ 59
def prefixEnd_2712554 : Nat := 4983230072969 + 3 ^ 40 * 2712554 * 2
def baseEnd_2712554 : Nat := 928562668850723569133465

theorem tailTrace_2712554 : CollatzResearch.WordTrace tailWord_2712554 prefixEnd_2712554 928562668850723569133465 := by
  unfold tailWord_2712554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24733743053721900046428179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65956648143258400123808477 24733743053721900046428179)
  ·
    refine ⟨37100614580582850069642269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24733743053721900046428179 37100614580582850069642269)
    ·
      refine ⟨13912730467718568776115851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37100614580582850069642269 13912730467718568776115851)
      ·
        refine ⟨20869095701577853164173777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13912730467718568776115851 20869095701577853164173777)
        ·
          refine ⟨15651821776183389873130333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20869095701577853164173777 15651821776183389873130333)
          ·
            refine ⟨5869433166068771202423875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15651821776183389873130333 5869433166068771202423875)
            ·
              refine ⟨8804149749103156803635813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869433166068771202423875 8804149749103156803635813)
              ·
                refine ⟨1650778077956841900681715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8804149749103156803635813 1650778077956841900681715)
                ·
                  refine ⟨2476167116935262851022573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1650778077956841900681715 2476167116935262851022573)
                  ·
                    refine ⟨928562668850723569133465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476167116935262851022573 928562668850723569133465)
                    ·
                      rfl

theorem cell22_2712554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2712554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712554 prefixEnd_2712554 := by exact prefixLift 2712554
  have htrace : WordTrace (prefixWord ++ tailWord_2712554) baseStart_2712554 baseEnd_2712554 := by
    simpa [prefixWord, tailWord_2712554, baseEnd_2712554] using wordTrace_append hprefix tailTrace_2712554
  have hstable : (prefixWord ++ tailWord_2712554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712554).length < 2 ^ (prefixWord ++ tailWord_2712554).sum := by decide
  have hdescent : baseEnd_2712554 < baseStart_2712554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712597 : List Nat := [1, 3, 2, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2712597 : Nat := 118140960795 + 2712597 * 2 ^ 59
def prefixEnd_2712597 : Nat := 4983230072969 + 3 ^ 40 * 2712597 * 2
def baseEnd_2712597 : Nat := 928577388629485790308333

theorem tailTrace_2712597 : CollatzResearch.WordTrace tailWord_2712597 prefixEnd_2712597 928577388629485790308333 := by
  unfold tailWord_2712597
  simp only [CollatzResearch.WordTrace]
  refine ⟨98936540553731818529528045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65957693702487879019685363 98936540553731818529528045)
  ·
    refine ⟨37101202707649431948573017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98936540553731818529528045 37101202707649431948573017)
    ·
      refine ⟨27825902030737073961429763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37101202707649431948573017 27825902030737073961429763)
      ·
        refine ⟨41738853046105610942144645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27825902030737073961429763 41738853046105610942144645)
        ·
          refine ⟨7826034946144802051652121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41738853046105610942144645 7826034946144802051652121)
          ·
            refine ⟨5869526209608601538739091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7826034946144802051652121 5869526209608601538739091)
            ·
              refine ⟨8804289314412902308108637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869526209608601538739091 8804289314412902308108637)
              ·
                refine ⟨3301608492904838365540739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8804289314412902308108637 3301608492904838365540739)
                ·
                  refine ⟨4952412739357257548311109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301608492904838365540739 4952412739357257548311109)
                  ·
                    refine ⟨928577388629485790308333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952412739357257548311109 928577388629485790308333)
                    ·
                      rfl

theorem cell22_2712597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2712597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712597 prefixEnd_2712597 := by exact prefixLift 2712597
  have htrace : WordTrace (prefixWord ++ tailWord_2712597) baseStart_2712597 baseEnd_2712597 := by
    simpa [prefixWord, tailWord_2712597, baseEnd_2712597] using wordTrace_append hprefix tailTrace_2712597
  have hstable : (prefixWord ++ tailWord_2712597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712597).length < 2 ^ (prefixWord ++ tailWord_2712597).sum := by decide
  have hdescent : baseEnd_2712597 < baseStart_2712597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712612 : List Nat := [2, 3, 1, 4, 1, 2, 2, 1, 6]
def baseStart_2712612 : Nat := 118140960795 + 2712612 * 2 ^ 59
def prefixEnd_2712612 : Nat := 4983230072969 + 3 ^ 40 * 2712612 * 2
def baseEnd_2712612 : Nat := 309527507812010250394429

theorem tailTrace_2712612 : CollatzResearch.WordTrace tailWord_2712612 prefixEnd_2712612 309527507812010250394429 := by
  unfold tailWord_2712612
  simp only [CollatzResearch.WordTrace]
  refine ⟨49468543824338738045662045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65958058432451650727549393 49468543824338738045662045)
  ·
    refine ⟨18550703934127026767123267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49468543824338738045662045 18550703934127026767123267)
    ·
      refine ⟨27826055901190540150684901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18550703934127026767123267 27826055901190540150684901)
      ·
        refine ⟨5217385481473226278253419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27826055901190540150684901 5217385481473226278253419)
        ·
          refine ⟨7826078222209839417380129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5217385481473226278253419 7826078222209839417380129)
          ·
            refine ⟨5869558666657379563035097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7826078222209839417380129 5869558666657379563035097)
            ·
              refine ⟨4402168999993034672276323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5869558666657379563035097 4402168999993034672276323)
              ·
                refine ⟨6603253499989552008414485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402168999993034672276323 6603253499989552008414485)
                ·
                  refine ⟨309527507812010250394429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6603253499989552008414485 309527507812010250394429)
                  ·
                    rfl

theorem cell22_2712612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 1, 6].length) (baseStart_2712612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712612 prefixEnd_2712612 := by exact prefixLift 2712612
  have htrace : WordTrace (prefixWord ++ tailWord_2712612) baseStart_2712612 baseEnd_2712612 := by
    simpa [prefixWord, tailWord_2712612, baseEnd_2712612] using wordTrace_append hprefix tailTrace_2712612
  have hstable : (prefixWord ++ tailWord_2712612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712612).length < 2 ^ (prefixWord ++ tailWord_2712612).sum := by decide
  have hdescent : baseEnd_2712612 < baseStart_2712612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712646 : List Nat := [6, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_2712646 : Nat := 118140960795 + 2712646 * 2 ^ 59
def prefixEnd_2712646 : Nat := 4983230072969 + 3 ^ 40 * 2712646 * 2
def baseEnd_2712646 : Nat := 309531387443621998611061

theorem tailTrace_2712646 : CollatzResearch.WordTrace tailWord_2712646 prefixEnd_2712646 309531387443621998611061 := by
  unfold tailWord_2712646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091822741579821871814431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65958885153702866598707861 3091822741579821871814431)
  ·
    refine ⟨4637734112369732807721647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091822741579821871814431 4637734112369732807721647)
    ·
      refine ⟨6956601168554599211582471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637734112369732807721647 6956601168554599211582471)
      ·
        refine ⟨10434901752831898817373707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956601168554599211582471 10434901752831898817373707)
        ·
          refine ⟨15652352629247848226060561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10434901752831898817373707 15652352629247848226060561)
          ·
            refine ⟨11739264471935886169545421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15652352629247848226060561 11739264471935886169545421)
            ·
              refine ⟨4402224176975957313579533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11739264471935886169545421 4402224176975957313579533)
              ·
                refine ⟨1650834066365983992592325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4402224176975957313579533 1650834066365983992592325)
                ·
                  refine ⟨309531387443621998611061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1650834066365983992592325 309531387443621998611061)
                  ·
                    rfl

theorem cell22_2712646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_2712646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712646 prefixEnd_2712646 := by exact prefixLift 2712646
  have htrace : WordTrace (prefixWord ++ tailWord_2712646) baseStart_2712646 baseEnd_2712646 := by
    simpa [prefixWord, tailWord_2712646, baseEnd_2712646] using wordTrace_append hprefix tailTrace_2712646
  have hstable : (prefixWord ++ tailWord_2712646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712646).length < 2 ^ (prefixWord ++ tailWord_2712646).sum := by decide
  have hdescent : baseEnd_2712646 < baseStart_2712646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712732 : List Nat := [2, 2, 3, 2, 1, 2, 1, 2, 3, 4]
def baseStart_2712732 : Nat := 118140960795 + 2712732 * 2 ^ 59
def prefixEnd_2712732 : Nat := 4983230072969 + 3 ^ 40 * 2712732 * 2
def baseEnd_2712732 : Nat := 928623601888390438182919

theorem tailTrace_2712732 : CollatzResearch.WordTrace tailWord_2712732 prefixEnd_2712732 928623601888390438182919 := by
  unfold tailWord_2712732
  simp only [CollatzResearch.WordTrace]
  refine ⟨49470732204121368292846225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65960976272161824390461633 49470732204121368292846225)
  ·
    refine ⟨37103049153091026219634669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49470732204121368292846225 37103049153091026219634669)
    ·
      refine ⟨13913643432409134832363001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37103049153091026219634669 13913643432409134832363001)
      ·
        refine ⟨10435232574306851124272251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13913643432409134832363001 10435232574306851124272251)
        ·
          refine ⟨15652848861460276686408377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10435232574306851124272251 15652848861460276686408377)
          ·
            refine ⟨11739636646095207514806283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15652848861460276686408377 11739636646095207514806283)
            ·
              refine ⟨17609454969142811272209425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11739636646095207514806283 17609454969142811272209425)
              ·
                refine ⟨13207091226857108454157069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17609454969142811272209425 13207091226857108454157069)
                ·
                  refine ⟨4952659210071415670308901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13207091226857108454157069 4952659210071415670308901)
                  ·
                    refine ⟨928623601888390438182919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952659210071415670308901 928623601888390438182919)
                    ·
                      rfl

theorem cell22_2712732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_2712732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712732 prefixEnd_2712732 := by exact prefixLift 2712732
  have htrace : WordTrace (prefixWord ++ tailWord_2712732) baseStart_2712732 baseEnd_2712732 := by
    simpa [prefixWord, tailWord_2712732, baseEnd_2712732] using wordTrace_append hprefix tailTrace_2712732
  have hstable : (prefixWord ++ tailWord_2712732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712732).length < 2 ^ (prefixWord ++ tailWord_2712732).sum := by decide
  have hdescent : baseEnd_2712732 < baseStart_2712732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712734 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2712734 : Nat := 118140960795 + 2712734 * 2 ^ 59
def prefixEnd_2712734 : Nat := 4983230072969 + 3 ^ 40 * 2712734 * 2
def baseEnd_2712734 : Nat := 928624286529263099632913

theorem tailTrace_2712734 : CollatzResearch.WordTrace tailWord_2712734 prefixEnd_2712734 928624286529263099632913 := by
  unfold tailWord_2712734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367692169279436365908157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65961024902823660618176837 12367692169279436365908157)
  ·
    refine ⟨4637884563479788637215559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12367692169279436365908157 4637884563479788637215559)
    ·
      refine ⟨6956826845219682955823339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4637884563479788637215559 6956826845219682955823339)
      ·
        refine ⟨10435240267829524433735009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6956826845219682955823339 10435240267829524433735009)
        ·
          refine ⟨7826430200872143325301257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10435240267829524433735009 7826430200872143325301257)
          ·
            refine ⟨5869822650654107493975943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7826430200872143325301257 5869822650654107493975943)
            ·
              refine ⟨8804733975981161240963915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5869822650654107493975943 8804733975981161240963915)
              ·
                refine ⟨13207100963971741861445873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8804733975981161240963915 13207100963971741861445873)
                ·
                  refine ⟨9905325722978806396084405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13207100963971741861445873 9905325722978806396084405)
                  ·
                    refine ⟨928624286529263099632913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9905325722978806396084405 928624286529263099632913)
                    ·
                      rfl

theorem cell22_2712734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2712734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712734 prefixEnd_2712734 := by exact prefixLift 2712734
  have htrace : WordTrace (prefixWord ++ tailWord_2712734) baseStart_2712734 baseEnd_2712734 := by
    simpa [prefixWord, tailWord_2712734, baseEnd_2712734] using wordTrace_append hprefix tailTrace_2712734
  have hstable : (prefixWord ++ tailWord_2712734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712734).length < 2 ^ (prefixWord ++ tailWord_2712734).sum := by decide
  have hdescent : baseEnd_2712734 < baseStart_2712734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712762 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_2712762 : Nat := 118140960795 + 2712762 * 2 ^ 59
def prefixEnd_2712762 : Nat := 4983230072969 + 3 ^ 40 * 2712762 * 2
def baseEnd_2712762 : Nat := 928633871501480359932827

theorem tailTrace_2712762 : CollatzResearch.WordTrace tailWord_2712762 prefixEnd_2712762 928633871501480359932827 := by
  unfold tailWord_2712762
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735639649533512927321135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65961705732089367806189693 24735639649533512927321135)
  ·
    refine ⟨37103459474300269390981703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24735639649533512927321135 37103459474300269390981703)
    ·
      refine ⟨55655189211450404086472555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37103459474300269390981703 55655189211450404086472555)
      ·
        refine ⟨83482783817175606129708833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55655189211450404086472555 83482783817175606129708833)
        ·
          refine ⟨62612087862881704597281625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83482783817175606129708833 62612087862881704597281625)
          ·
            refine ⟨46959065897161278447961219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62612087862881704597281625 46959065897161278447961219)
            ·
              refine ⟨70438598845741917671941829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46959065897161278447961219 70438598845741917671941829)
              ·
                refine ⟨13207237283576609563489093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70438598845741917671941829 13207237283576609563489093)
                ·
                  refine ⟨2476356990670614293154205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13207237283576609563489093 2476356990670614293154205)
                  ·
                    refine ⟨928633871501480359932827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476356990670614293154205 928633871501480359932827)
                    ·
                      rfl

theorem cell22_2712762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_2712762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712762 prefixEnd_2712762 := by exact prefixLift 2712762
  have htrace : WordTrace (prefixWord ++ tailWord_2712762) baseStart_2712762 baseEnd_2712762 := by
    simpa [prefixWord, tailWord_2712762, baseEnd_2712762] using wordTrace_append hprefix tailTrace_2712762
  have hstable : (prefixWord ++ tailWord_2712762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712762).length < 2 ^ (prefixWord ++ tailWord_2712762).sum := by decide
  have hdescent : baseEnd_2712762 < baseStart_2712762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712764 : List Nat := [2, 2, 2, 3, 2, 1, 1, 5, 4]
def baseStart_2712764 : Nat := 118140960795 + 2712764 * 2 ^ 59
def prefixEnd_2712764 : Nat := 4983230072969 + 3 ^ 40 * 2712764 * 2
def baseEnd_2712764 : Nat := 309544852047451007127607

theorem tailTrace_2712764 : CollatzResearch.WordTrace tailWord_2712764 prefixEnd_2712764 309544852047451007127607 := by
  unfold tailWord_2712764
  simp only [CollatzResearch.WordTrace]
  refine ⟨49471315772063403025428673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65961754362751204033904897 49471315772063403025428673)
  ·
    refine ⟨37103486829047552269071505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49471315772063403025428673 37103486829047552269071505)
    ·
      refine ⟨27827615121785664201803629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37103486829047552269071505 27827615121785664201803629)
      ·
        refine ⟨10435355670669624075676361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27827615121785664201803629 10435355670669624075676361)
        ·
          refine ⟨7826516753002218056757271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10435355670669624075676361 7826516753002218056757271)
          ·
            refine ⟨11739775129503327085135907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7826516753002218056757271 11739775129503327085135907)
            ·
              refine ⟨17609662694254990627703861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11739775129503327085135907 17609662694254990627703861)
              ·
                refine ⟨1650905877586405371347237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17609662694254990627703861 1650905877586405371347237)
                ·
                  refine ⟨309544852047451007127607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1650905877586405371347237 309544852047451007127607)
                  ·
                    rfl

theorem cell22_2712764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 5, 4].length) (baseStart_2712764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712764 prefixEnd_2712764 := by exact prefixLift 2712764
  have htrace : WordTrace (prefixWord ++ tailWord_2712764) baseStart_2712764 baseEnd_2712764 := by
    simpa [prefixWord, tailWord_2712764, baseEnd_2712764] using wordTrace_append hprefix tailTrace_2712764
  have hstable : (prefixWord ++ tailWord_2712764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712764).length < 2 ^ (prefixWord ++ tailWord_2712764).sum := by decide
  have hdescent : baseEnd_2712764 < baseStart_2712764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712766 : List Nat := [4, 2, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_2712766 : Nat := 118140960795 + 2712766 * 2 ^ 59
def prefixEnd_2712766 : Nat := 4983230072969 + 3 ^ 40 * 2712766 * 2
def baseEnd_2712766 : Nat := 928635240783225682832815

theorem tailTrace_2712766 : CollatzResearch.WordTrace tailWord_2712766 prefixEnd_2712766 928635240783225682832815 := by
  unfold tailWord_2712766
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367838061264945049053769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65961802993413040261620101 12367838061264945049053769)
  ·
    refine ⟨9275878545948708786790327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12367838061264945049053769 9275878545948708786790327)
    ·
      refine ⟨13913817818923063180185491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9275878545948708786790327 13913817818923063180185491)
      ·
        refine ⟨20870726728384594770278237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13913817818923063180185491 20870726728384594770278237)
        ·
          refine ⟨7826522523144223038854339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20870726728384594770278237 7826522523144223038854339)
          ·
            refine ⟨11739783784716334558281509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7826522523144223038854339 11739783784716334558281509)
            ·
              refine ⟨2201209459634312729677783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11739783784716334558281509 2201209459634312729677783)
              ·
                refine ⟨3301814189451469094516675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201209459634312729677783 3301814189451469094516675)
                ·
                  refine ⟨4952721284177203641775013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3301814189451469094516675 4952721284177203641775013)
                  ·
                    refine ⟨928635240783225682832815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4952721284177203641775013 928635240783225682832815)
                    ·
                      rfl

theorem cell22_2712766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_2712766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712766 prefixEnd_2712766 := by exact prefixLift 2712766
  have htrace : WordTrace (prefixWord ++ tailWord_2712766) baseStart_2712766 baseEnd_2712766 := by
    simpa [prefixWord, tailWord_2712766, baseEnd_2712766] using wordTrace_append hprefix tailTrace_2712766
  have hstable : (prefixWord ++ tailWord_2712766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712766).length < 2 ^ (prefixWord ++ tailWord_2712766).sum := by decide
  have hdescent : baseEnd_2712766 < baseStart_2712766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712770 : List Nat := [3, 5, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2712770 : Nat := 118140960795 + 2712770 * 2 ^ 59
def prefixEnd_2712770 : Nat := 4983230072969 + 3 ^ 40 * 2712770 * 2
def baseEnd_2712770 : Nat := 309545536688323668577601

theorem tailTrace_2712770 : CollatzResearch.WordTrace tailWord_2712770 prefixEnd_2712770 309545536688323668577601 := by
  unfold tailWord_2712770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24735712595526267268893941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65961900254736712717050509 24735712595526267268893941)
  ·
    refine ⟨2318973055830587556458807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24735712595526267268893941 2318973055830587556458807)
    ·
      refine ⟨3478459583745881334688211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2318973055830587556458807 3478459583745881334688211)
      ·
        refine ⟨5217689375618822002032317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3478459583745881334688211 5217689375618822002032317)
        ·
          refine ⟨1956633515857058250762119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5217689375618822002032317 1956633515857058250762119)
          ·
            refine ⟨2934950273785587376143179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956633515857058250762119 2934950273785587376143179)
            ·
              refine ⟨4402425410678381064214769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2934950273785587376143179 4402425410678381064214769)
              ·
                refine ⟨3301819058008785798161077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4402425410678381064214769 3301819058008785798161077)
                ·
                  refine ⟨309545536688323668577601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301819058008785798161077 309545536688323668577601)
                  ·
                    rfl

theorem cell22_2712770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2712770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712770 prefixEnd_2712770 := by exact prefixLift 2712770
  have htrace : WordTrace (prefixWord ++ tailWord_2712770) baseStart_2712770 baseEnd_2712770 := by
    simpa [prefixWord, tailWord_2712770, baseEnd_2712770] using wordTrace_append hprefix tailTrace_2712770
  have hstable : (prefixWord ++ tailWord_2712770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712770).length < 2 ^ (prefixWord ++ tailWord_2712770).sum := by decide
  have hdescent : baseEnd_2712770 < baseStart_2712770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712822 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_2712822 : Nat := 118140960795 + 2712822 * 2 ^ 59
def prefixEnd_2712822 : Nat := 4983230072969 + 3 ^ 40 * 2712822 * 2
def baseEnd_2712822 : Nat := 928654410727660203432643

theorem tailTrace_2712822 : CollatzResearch.WordTrace tailWord_2712822 prefixEnd_2712822 928654410727660203432643 := by
  unfold tailWord_2712822
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184046686119792622279295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65963164651944454637645813 6184046686119792622279295)
  ·
    refine ⟨9276070029179688933418943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6184046686119792622279295 9276070029179688933418943)
    ·
      refine ⟨13914105043769533400128415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9276070029179688933418943 13914105043769533400128415)
      ·
        refine ⟨20871157565654300100192623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13914105043769533400128415 20871157565654300100192623)
        ·
          refine ⟨31306736348481450150288935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20871157565654300100192623 31306736348481450150288935)
          ·
            refine ⟨46960104522722175225433403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31306736348481450150288935 46960104522722175225433403)
            ·
              refine ⟨70440156784083262838150105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46960104522722175225433403 70440156784083262838150105)
              ·
                refine ⟨52830117588062447128612579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70440156784083262838150105 52830117588062447128612579)
                ·
                  refine ⟨79245176382093670692918869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52830117588062447128612579 79245176382093670692918869)
                  ·
                    refine ⟨928654410727660203432643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79245176382093670692918869 928654410727660203432643)
                    ·
                      rfl

theorem cell22_2712822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_2712822 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712822 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712822 prefixEnd_2712822 := by exact prefixLift 2712822
  have htrace : WordTrace (prefixWord ++ tailWord_2712822) baseStart_2712822 baseEnd_2712822 := by
    simpa [prefixWord, tailWord_2712822, baseEnd_2712822] using wordTrace_append hprefix tailTrace_2712822
  have hstable : (prefixWord ++ tailWord_2712822).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712822).length < 2 ^ (prefixWord ++ tailWord_2712822).sum := by decide
  have hdescent : baseEnd_2712822 < baseStart_2712822 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712837 : List Nat := [1, 3, 1, 1, 2, 1, 4, 4, 5]
def baseStart_2712837 : Nat := 118140960795 + 2712837 * 2 ^ 59
def prefixEnd_2712837 : Nat := 4983230072969 + 3 ^ 40 * 2712837 * 2
def baseEnd_2712837 : Nat := 309553181844735054769199

theorem tailTrace_2712837 : CollatzResearch.WordTrace tailWord_2712837 prefixEnd_2712837 309553181844735054769199 := by
  unfold tailWord_2712837
  simp only [CollatzResearch.WordTrace]
  refine ⟨98945294072862339518264765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65963529381908226345509843 98945294072862339518264765)
  ·
    refine ⟨37104485277323377319349287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98945294072862339518264765 37104485277323377319349287)
    ·
      refine ⟨55656727915985065979023931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37104485277323377319349287 55656727915985065979023931)
      ·
        refine ⟨83485091873977598968535897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55656727915985065979023931 83485091873977598968535897)
        ·
          refine ⟨62613818905483199226401923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83485091873977598968535897 62613818905483199226401923)
          ·
            refine ⟨93920728358224798839602885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62613818905483199226401923 93920728358224798839602885)
            ·
              refine ⟨17610136567167149782425541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93920728358224798839602885 17610136567167149782425541)
              ·
                refine ⟨3301900606343840584204789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17610136567167149782425541 3301900606343840584204789)
                ·
                  refine ⟨309553181844735054769199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3301900606343840584204789 309553181844735054769199)
                  ·
                    rfl

theorem cell22_2712837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_2712837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712837 prefixEnd_2712837 := by exact prefixLift 2712837
  have htrace : WordTrace (prefixWord ++ tailWord_2712837) baseStart_2712837 baseEnd_2712837 := by
    simpa [prefixWord, tailWord_2712837, baseEnd_2712837] using wordTrace_append hprefix tailTrace_2712837
  have hstable : (prefixWord ++ tailWord_2712837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712837).length < 2 ^ (prefixWord ++ tailWord_2712837).sum := by decide
  have hdescent : baseEnd_2712837 < baseStart_2712837 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712912 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 1, 6]
def baseStart_2712912 : Nat := 118140960795 + 2712912 * 2 ^ 59
def prefixEnd_2712912 : Nat := 4983230072969 + 3 ^ 40 * 2712912 * 2
def baseEnd_2712912 : Nat := 928685219566929968682367

theorem tailTrace_2712912 : CollatzResearch.WordTrace tailWord_2712912 prefixEnd_2712912 928685219566929968682367 := by
  unfold tailWord_2712912
  simp only [CollatzResearch.WordTrace]
  refine ⟨49474014773795313663622495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65965353031727084884829993 49474014773795313663622495)
  ·
    refine ⟨74211022160692970495433743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49474014773795313663622495 74211022160692970495433743)
    ·
      refine ⟨111316533241039455743150615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74211022160692970495433743 111316533241039455743150615)
      ·
        refine ⟨166974799861559183614725923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111316533241039455743150615 166974799861559183614725923)
        ·
          refine ⟨250462199792338775422088885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166974799861559183614725923 250462199792338775422088885)
          ·
            refine ⟨23480831230531760195820833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 250462199792338775422088885 23480831230531760195820833)
            ·
              refine ⟨17610623422898820146865625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23480831230531760195820833 17610623422898820146865625)
              ·
                refine ⟨13207967567174115110149219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17610623422898820146865625 13207967567174115110149219)
                ·
                  refine ⟨19811951350761172665223829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13207967567174115110149219 19811951350761172665223829)
                  ·
                    refine ⟨928685219566929968682367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19811951350761172665223829 928685219566929968682367)
                    ·
                      rfl

theorem cell22_2712912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 6].length) (baseStart_2712912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712912 prefixEnd_2712912 := by exact prefixLift 2712912
  have htrace : WordTrace (prefixWord ++ tailWord_2712912) baseStart_2712912 baseEnd_2712912 := by
    simpa [prefixWord, tailWord_2712912, baseEnd_2712912] using wordTrace_append hprefix tailTrace_2712912
  have hstable : (prefixWord ++ tailWord_2712912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712912).length < 2 ^ (prefixWord ++ tailWord_2712912).sum := by decide
  have hdescent : baseEnd_2712912 < baseStart_2712912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712914 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_2712914 : Nat := 118140960795 + 2712914 * 2 ^ 59
def prefixEnd_2712914 : Nat := 4983230072969 + 3 ^ 40 * 2712914 * 2
def baseEnd_2712914 : Nat := 928685904207802630132361

theorem tailTrace_2712914 : CollatzResearch.WordTrace tailWord_2712914 prefixEnd_2712914 928685904207802630132361 := by
  unfold tailWord_2712914
  simp only [CollatzResearch.WordTrace]
  refine ⟨24737025623395845417204449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65965401662388921112545197 24737025623395845417204449)
  ·
    refine ⟨18552769217546884062903337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24737025623395845417204449 18552769217546884062903337)
    ·
      refine ⟨13914576913160163047177503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18552769217546884062903337 13914576913160163047177503)
      ·
        refine ⟨20871865369740244570766255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13914576913160163047177503 20871865369740244570766255)
        ·
          refine ⟨31307798054610366856149383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20871865369740244570766255 31307798054610366856149383)
          ·
            refine ⟨46961697081915550284224075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31307798054610366856149383 46961697081915550284224075)
            ·
              refine ⟨70442545622873325426336113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46961697081915550284224075 70442545622873325426336113)
              ·
                refine ⟨52831909217154994069752085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70442545622873325426336113 52831909217154994069752085)
                ·
                  refine ⟨2476495744554140347019629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52831909217154994069752085 2476495744554140347019629)
                  ·
                    refine ⟨928685904207802630132361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476495744554140347019629 928685904207802630132361)
                    ·
                      rfl

theorem cell22_2712914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_2712914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712914 prefixEnd_2712914 := by exact prefixLift 2712914
  have htrace : WordTrace (prefixWord ++ tailWord_2712914) baseStart_2712914 baseEnd_2712914 := by
    simpa [prefixWord, tailWord_2712914, baseEnd_2712914] using wordTrace_append hprefix tailTrace_2712914
  have hstable : (prefixWord ++ tailWord_2712914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712914).length < 2 ^ (prefixWord ++ tailWord_2712914).sum := by decide
  have hdescent : baseEnd_2712914 < baseStart_2712914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712935 : List Nat := [1, 1, 5, 1, 5, 1, 2, 1, 1, 4]
def baseStart_2712935 : Nat := 118140960795 + 2712935 * 2 ^ 59
def prefixEnd_2712935 : Nat := 4983230072969 + 3 ^ 40 * 2712935 * 2
def baseEnd_2712935 : Nat := 928693092936965575357297

theorem tailTrace_2712935 : CollatzResearch.WordTrace tailWord_2712935 prefixEnd_2712935 928693092936965575357297 := by
  unfold tailWord_2712935
  simp only [CollatzResearch.WordTrace]
  refine ⟨98948868426507302255332259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65965912284338201503554839 98948868426507302255332259)
  ·
    refine ⟨148423302639760953382998389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98948868426507302255332259 148423302639760953382998389)
    ·
      refine ⟨13914684622477589379656099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148423302639760953382998389 13914684622477589379656099)
      ·
        refine ⟨20872026933716384069484149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13914684622477589379656099 20872026933716384069484149)
        ·
          refine ⟨1956752525035911006514139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20872026933716384069484149 1956752525035911006514139)
          ·
            refine ⟨2935128787553866509771209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1956752525035911006514139 2935128787553866509771209)
            ·
              refine ⟨2201346590665399882328407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2935128787553866509771209 2201346590665399882328407)
              ·
                refine ⟨3302019885998099823492611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2201346590665399882328407 3302019885998099823492611)
                ·
                  refine ⟨4953029828997149735238917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302019885998099823492611 4953029828997149735238917)
                  ·
                    refine ⟨928693092936965575357297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953029828997149735238917 928693092936965575357297)
                    ·
                      rfl

theorem cell22_2712935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_2712935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712935 prefixEnd_2712935 := by exact prefixLift 2712935
  have htrace : WordTrace (prefixWord ++ tailWord_2712935) baseStart_2712935 baseEnd_2712935 := by
    simpa [prefixWord, tailWord_2712935, baseEnd_2712935] using wordTrace_append hprefix tailTrace_2712935
  have hstable : (prefixWord ++ tailWord_2712935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712935).length < 2 ^ (prefixWord ++ tailWord_2712935).sum := by decide
  have hdescent : baseEnd_2712935 < baseStart_2712935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2712989 : List Nat := [1, 4, 2, 1, 3, 1, 1, 2, 7]
def baseStart_2712989 : Nat := 118140960795 + 2712989 * 2 ^ 59
def prefixEnd_2712989 : Nat := 4983230072969 + 3 ^ 40 * 2712989 * 2
def baseEnd_2712989 : Nat := 309570526080175811502377

theorem tailTrace_2712989 : CollatzResearch.WordTrace tailWord_2712989 prefixEnd_2712989 309570526080175811502377 := by
  unfold tailWord_2712989
  simp only [CollatzResearch.WordTrace]
  refine ⟨98950837968311669477798021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65967225312207779651865347 98950837968311669477798021)
  ·
    refine ⟨18553282119058438027087129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98950837968311669477798021 18553282119058438027087129)
    ·
      refine ⟨13914961589293828520315347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18553282119058438027087129 13914961589293828520315347)
      ·
        refine ⟨20872442383940742780473021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13914961589293828520315347 20872442383940742780473021)
        ·
          refine ⟨7827165893977778542677383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20872442383940742780473021 7827165893977778542677383)
          ·
            refine ⟨11740748840966667814016075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7827165893977778542677383 11740748840966667814016075)
            ·
              refine ⟨17611123261450001721024113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11740748840966667814016075 17611123261450001721024113)
              ·
                refine ⟨13208342446087501290768085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17611123261450001721024113 13208342446087501290768085)
                ·
                  refine ⟨309570526080175811502377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13208342446087501290768085 309570526080175811502377)
                  ·
                    rfl

theorem cell22_2712989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_2712989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2712989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2712989 prefixEnd_2712989 := by exact prefixLift 2712989
  have htrace : WordTrace (prefixWord ++ tailWord_2712989) baseStart_2712989 baseEnd_2712989 := by
    simpa [prefixWord, tailWord_2712989, baseEnd_2712989] using wordTrace_append hprefix tailTrace_2712989
  have hstable : (prefixWord ++ tailWord_2712989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2712989).length < 2 ^ (prefixWord ++ tailWord_2712989).sum := by decide
  have hdescent : baseEnd_2712989 < baseStart_2712989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2712989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713036 : List Nat := [2, 2, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_2713036 : Nat := 118140960795 + 2713036 * 2 ^ 59
def prefixEnd_2713036 : Nat := 4983230072969 + 3 ^ 40 * 2713036 * 2
def baseEnd_2713036 : Nat := 928727667301034978581987

theorem tailTrace_2713036 : CollatzResearch.WordTrace tailWord_2713036 prefixEnd_2713036 928727667301034978581987 := by
  unfold tailWord_2713036
  simp only [CollatzResearch.WordTrace]
  refine ⟨49476276099570698252379481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65968368132760931003172641 49476276099570698252379481)
  ·
    refine ⟨37107207074678023689284611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49476276099570698252379481 37107207074678023689284611)
    ·
      refine ⟨55660810612017035533926917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37107207074678023689284611 55660810612017035533926917)
      ·
        refine ⟨10436401989753194162611297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55660810612017035533926917 10436401989753194162611297)
        ·
          refine ⟨7827301492314895621958473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10436401989753194162611297 7827301492314895621958473)
          ·
            refine ⟨5870476119236171716468855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7827301492314895621958473 5870476119236171716468855)
            ·
              refine ⟨8805714178854257574703283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5870476119236171716468855 8805714178854257574703283)
              ·
                refine ⟨13208571268281386362054925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8805714178854257574703283 13208571268281386362054925)
                ·
                  refine ⟨4953214225605519885770597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13208571268281386362054925 4953214225605519885770597)
                  ·
                    refine ⟨928727667301034978581987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953214225605519885770597 928727667301034978581987)
                    ·
                      rfl

theorem cell22_2713036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_2713036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713036 prefixEnd_2713036 := by exact prefixLift 2713036
  have htrace : WordTrace (prefixWord ++ tailWord_2713036) baseStart_2713036 baseEnd_2713036 := by
    simpa [prefixWord, tailWord_2713036, baseEnd_2713036] using wordTrace_append hprefix tailTrace_2713036
  have hstable : (prefixWord ++ tailWord_2713036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713036).length < 2 ^ (prefixWord ++ tailWord_2713036).sum := by decide
  have hdescent : baseEnd_2713036 < baseStart_2713036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713049 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_2713049 : Nat := 118140960795 + 2713049 * 2 ^ 59
def prefixEnd_2713049 : Nat := 4983230072969 + 3 ^ 40 * 2713049 * 2
def baseEnd_2713049 : Nat := 928732117466707278006947

theorem tailTrace_2713049 : CollatzResearch.WordTrace tailWord_2713049 prefixEnd_2713049 928732117466707278006947 := by
  unfold tailWord_2713049
  simp only [CollatzResearch.WordTrace]
  refine ⟨98953026348094299724982201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65968684232062866483321467 98953026348094299724982201)
  ·
    refine ⟨74214769761070724793736651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98953026348094299724982201 74214769761070724793736651)
    ·
      refine ⟨111322154641606087190604977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74214769761070724793736651 111322154641606087190604977)
      ·
        refine ⟨83491615981204565392953733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111322154641606087190604977 83491615981204565392953733)
        ·
          refine ⟨15654677996475856011178825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83491615981204565392953733 15654677996475856011178825)
          ·
            refine ⟨11741008497356892008384119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15654677996475856011178825 11741008497356892008384119)
            ·
              refine ⟨17611512746035338012576179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11741008497356892008384119 17611512746035338012576179)
              ·
                refine ⟨26417269119053007018864269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17611512746035338012576179 26417269119053007018864269)
                ·
                  refine ⟨9906475919644877632074101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26417269119053007018864269 9906475919644877632074101)
                  ·
                    refine ⟨928732117466707278006947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9906475919644877632074101 928732117466707278006947)
                    ·
                      rfl

theorem cell22_2713049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_2713049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713049 prefixEnd_2713049 := by exact prefixLift 2713049
  have htrace : WordTrace (prefixWord ++ tailWord_2713049) baseStart_2713049 baseEnd_2713049 := by
    simpa [prefixWord, tailWord_2713049, baseEnd_2713049] using wordTrace_append hprefix tailTrace_2713049
  have hstable : (prefixWord ++ tailWord_2713049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713049).length < 2 ^ (prefixWord ++ tailWord_2713049).sum := by decide
  have hdescent : baseEnd_2713049 < baseStart_2713049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713098 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_2713098 : Nat := 118140960795 + 2713098 * 2 ^ 59
def prefixEnd_2713098 : Nat := 4983230072969 + 3 ^ 40 * 2713098 * 2
def baseEnd_2713098 : Nat := 928748891168087483531797

theorem tailTrace_2713098 : CollatzResearch.WordTrace tailWord_2713098 prefixEnd_2713098 928748891168087483531797 := by
  unfold tailWord_2713098
  simp only [CollatzResearch.WordTrace]
  refine ⟨24738703381229195273378987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65969875683277854062343965 24738703381229195273378987)
  ·
    refine ⟨37108055071843792910068481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24738703381229195273378987 37108055071843792910068481)
    ·
      refine ⟨27831041303882844682551361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37108055071843792910068481 27831041303882844682551361)
      ·
        refine ⟨20873280977912133511913521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27831041303882844682551361 20873280977912133511913521)
        ·
          refine ⟨15654960733434100133935141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20873280977912133511913521 15654960733434100133935141)
          ·
            refine ⟨2935305137518893775112839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15654960733434100133935141 2935305137518893775112839)
            ·
              refine ⟨4402957706278340662669259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935305137518893775112839 4402957706278340662669259)
              ·
                refine ⟨6604436559417510994003889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4402957706278340662669259 6604436559417510994003889)
                ·
                  refine ⟨4953327419563133245502917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6604436559417510994003889 4953327419563133245502917)
                  ·
                    refine ⟨928748891168087483531797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953327419563133245502917 928748891168087483531797)
                    ·
                      rfl

theorem cell22_2713098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_2713098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713098 prefixEnd_2713098 := by exact prefixLift 2713098
  have htrace : WordTrace (prefixWord ++ tailWord_2713098) baseStart_2713098 baseEnd_2713098 := by
    simpa [prefixWord, tailWord_2713098, baseEnd_2713098] using wordTrace_append hprefix tailTrace_2713098
  have hstable : (prefixWord ++ tailWord_2713098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713098).length < 2 ^ (prefixWord ++ tailWord_2713098).sum := by decide
  have hdescent : baseEnd_2713098 < baseStart_2713098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713205 : List Nat := [1, 3, 4, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2713205 : Nat := 118140960795 + 2713205 * 2 ^ 59
def prefixEnd_2713205 : Nat := 4983230072969 + 3 ^ 40 * 2713205 * 2
def baseEnd_2713205 : Nat := 928785519454774871106469

theorem tailTrace_2713205 : CollatzResearch.WordTrace tailWord_2713205 prefixEnd_2713205 928785519454774871106469 := by
  unfold tailWord_2713205
  simp only [CollatzResearch.WordTrace]
  refine ⟨98958716135529138367661069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65972477423686092245107379 98958716135529138367661069)
  ·
    refine ⟨37109518550823426887872901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98958716135529138367661069 37109518550823426887872901)
    ·
      refine ⟨6958034728279392541476169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37109518550823426887872901 6958034728279392541476169)
      ·
        refine ⟨5218526046209544406107127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6958034728279392541476169 5218526046209544406107127)
        ·
          refine ⟨7827789069314316609160691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218526046209544406107127 7827789069314316609160691)
          ·
            refine ⟨11741683603971474913741037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7827789069314316609160691 11741683603971474913741037)
            ·
              refine ⟨4403131351489303092652889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11741683603971474913741037 4403131351489303092652889)
              ·
                refine ⟨3302348513616977319489667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4403131351489303092652889 3302348513616977319489667)
                ·
                  refine ⟨4953522770425465979234501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302348513616977319489667 4953522770425465979234501)
                  ·
                    refine ⟨928785519454774871106469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953522770425465979234501 928785519454774871106469)
                    ·
                      rfl

theorem cell22_2713205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2713205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713205 prefixEnd_2713205 := by exact prefixLift 2713205
  have htrace : WordTrace (prefixWord ++ tailWord_2713205) baseStart_2713205 baseEnd_2713205 := by
    simpa [prefixWord, tailWord_2713205, baseEnd_2713205] using wordTrace_append hprefix tailTrace_2713205
  have hstable : (prefixWord ++ tailWord_2713205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713205).length < 2 ^ (prefixWord ++ tailWord_2713205).sum := by decide
  have hdescent : baseEnd_2713205 < baseStart_2713205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713248 : List Nat := [2, 1, 1, 4, 3, 3, 1, 7]
def baseStart_2713248 : Nat := 118140960795 + 2713248 * 2 ^ 59
def prefixEnd_2713248 : Nat := 4983230072969 + 3 ^ 40 * 2713248 * 2
def baseEnd_2713248 : Nat := 103200026581504121364593

theorem tailTrace_2713248 : CollatzResearch.WordTrace tailWord_2713248 prefixEnd_2713248 103200026581504121364593 := by
  unfold tailWord_2713248
  simp only [CollatzResearch.WordTrace]
  refine ⟨49480142237186678355738199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65973522982915571140984265 49480142237186678355738199)
  ·
    refine ⟨74220213355780017533607299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49480142237186678355738199 74220213355780017533607299)
    ·
      refine ⟨111330320033670026300410949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74220213355780017533607299 111330320033670026300410949)
      ·
        refine ⟨20874435006313129931327053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111330320033670026300410949 20874435006313129931327053)
        ·
          refine ⟨7827913127367423724247645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20874435006313129931327053 7827913127367423724247645)
          ·
            refine ⟨2935467422762783896592867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7827913127367423724247645 2935467422762783896592867)
            ·
              refine ⟨4403201134144175844889301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935467422762783896592867 4403201134144175844889301)
              ·
                refine ⟨103200026581504121364593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4403201134144175844889301 103200026581504121364593)
                ·
                  rfl

theorem cell22_2713248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 7].length) (baseStart_2713248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713248 prefixEnd_2713248 := by exact prefixLift 2713248
  have htrace : WordTrace (prefixWord ++ tailWord_2713248) baseStart_2713248 baseEnd_2713248 := by
    simpa [prefixWord, tailWord_2713248, baseEnd_2713248] using wordTrace_append hprefix tailTrace_2713248
  have hstable : (prefixWord ++ tailWord_2713248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713248).length < 2 ^ (prefixWord ++ tailWord_2713248).sum := by decide
  have hdescent : baseEnd_2713248 < baseStart_2713248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713263 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 3, 3]
def baseStart_2713263 : Nat := 118140960795 + 2713263 * 2 ^ 59
def prefixEnd_2713263 : Nat := 4983230072969 + 3 ^ 40 * 2713263 * 2
def baseEnd_2713263 : Nat := 928805374040082053156291

theorem tailTrace_2713263 : CollatzResearch.WordTrace tailWord_2713263 prefixEnd_2713263 928805374040082053156291 := by
  unfold tailWord_2713263
  simp only [CollatzResearch.WordTrace]
  refine ⟨98960831569319014273272443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65973887712879342848848295 98960831569319014273272443)
  ·
    refine ⟨148441247353978521409908665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98960831569319014273272443 148441247353978521409908665)
    ·
      refine ⟨111330935515483891057431499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148441247353978521409908665 111330935515483891057431499)
      ·
        refine ⟨166996403273225836586147249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111330935515483891057431499 166996403273225836586147249)
        ·
          refine ⟨125247302454919377439610437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166996403273225836586147249 125247302454919377439610437)
          ·
            refine ⟨23483869210297383269926957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125247302454919377439610437 23483869210297383269926957)
            ·
              refine ⟨8806450953861518726222609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23483869210297383269926957 8806450953861518726222609)
              ·
                refine ⟨6604838215396139044666957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8806450953861518726222609 6604838215396139044666957)
                ·
                  refine ⟨2476814330773552141750109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6604838215396139044666957 2476814330773552141750109)
                  ·
                    refine ⟨928805374040082053156291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476814330773552141750109 928805374040082053156291)
                    ·
                      rfl

theorem cell22_2713263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 3].length) (baseStart_2713263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713263 prefixEnd_2713263 := by exact prefixLift 2713263
  have htrace : WordTrace (prefixWord ++ tailWord_2713263) baseStart_2713263 baseEnd_2713263 := by
    simpa [prefixWord, tailWord_2713263, baseEnd_2713263] using wordTrace_append hprefix tailTrace_2713263
  have hstable : (prefixWord ++ tailWord_2713263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713263).length < 2 ^ (prefixWord ++ tailWord_2713263).sum := by decide
  have hdescent : baseEnd_2713263 < baseStart_2713263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713282 : List Nat := [3, 5, 1, 2, 1, 1, 9]
def baseStart_2713282 : Nat := 118140960795 + 2713282 * 2 ^ 59
def prefixEnd_2713282 : Nat := 4983230072969 + 3 ^ 40 * 2713282 * 2
def baseEnd_2713282 : Nat := 34400439930680456923379

theorem tailTrace_2713282 : CollatzResearch.WordTrace tailWord_2713282 prefixEnd_2713282 34400439930680456923379 := by
  unfold tailWord_2713282
  simp only [CollatzResearch.WordTrace]
  refine ⟨24740381139062545129553525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65974349704166787012142733 24740381139062545129553525)
  ·
    refine ⟨2319410731787113605895643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24740381139062545129553525 2319410731787113605895643)
    ·
      refine ⟨3479116097680670408843465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2319410731787113605895643 3479116097680670408843465)
      ·
        refine ⟨2609337073260502806632599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3479116097680670408843465 2609337073260502806632599)
        ·
          refine ⟨3914005609890754209948899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609337073260502806632599 3914005609890754209948899)
          ·
            refine ⟨5871008414836131314923349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914005609890754209948899 5871008414836131314923349)
            ·
              refine ⟨34400439930680456923379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5871008414836131314923349 34400439930680456923379)
              ·
                rfl

theorem cell22_2713282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 9].length) (baseStart_2713282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713282 prefixEnd_2713282 := by exact prefixLift 2713282
  have htrace : WordTrace (prefixWord ++ tailWord_2713282) baseStart_2713282 baseEnd_2713282 := by
    simpa [prefixWord, tailWord_2713282, baseEnd_2713282] using wordTrace_append hprefix tailTrace_2713282
  have hstable : (prefixWord ++ tailWord_2713282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713282).length < 2 ^ (prefixWord ++ tailWord_2713282).sum := by decide
  have hdescent : baseEnd_2713282 < baseStart_2713282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713286 : List Nat := [6, 1, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2713286 : Nat := 118140960795 + 2713286 * 2 ^ 59
def prefixEnd_2713286 : Nat := 4983230072969 + 3 ^ 40 * 2713286 * 2
def baseEnd_2713286 : Nat := 928813247410117659831221

theorem tailTrace_2713286 : CollatzResearch.WordTrace tailWord_2713286 prefixEnd_2713286 928813247410117659831221 := by
  unfold tailWord_2713286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3092552201507365287542491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 65974446965490459467573141 3092552201507365287542491)
  ·
    refine ⟨4638828302261047931313737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3092552201507365287542491 4638828302261047931313737)
    ·
      refine ⟨3479121226695785948485303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638828302261047931313737 3479121226695785948485303)
      ·
        refine ⟨5218681840043678922727955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479121226695785948485303 5218681840043678922727955)
        ·
          refine ⟨7828022760065518384091933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5218681840043678922727955 7828022760065518384091933)
          ·
            refine ⟨2935508535024569394034475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7828022760065518384091933 2935508535024569394034475)
            ·
              refine ⟨4403262802536854091051713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2935508535024569394034475 4403262802536854091051713)
              ·
                refine ⟨3302447101902640568288785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4403262802536854091051713 3302447101902640568288785)
                ·
                  refine ⟨2476835326426980426216589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3302447101902640568288785 2476835326426980426216589)
                  ·
                    refine ⟨928813247410117659831221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2476835326426980426216589 928813247410117659831221)
                    ·
                      rfl

theorem cell22_2713286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2713286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713286 prefixEnd_2713286 := by exact prefixLift 2713286
  have htrace : WordTrace (prefixWord ++ tailWord_2713286) baseStart_2713286 baseEnd_2713286 := by
    simpa [prefixWord, tailWord_2713286, baseEnd_2713286] using wordTrace_append hprefix tailTrace_2713286
  have hstable : (prefixWord ++ tailWord_2713286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713286).length < 2 ^ (prefixWord ++ tailWord_2713286).sum := by decide
  have hdescent : baseEnd_2713286 < baseStart_2713286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713323 : List Nat := [1, 1, 1, 1, 2, 4, 3, 4, 1, 4]
def baseStart_2713323 : Nat := 118140960795 + 2713323 * 2 ^ 59
def prefixEnd_2713323 : Nat := 4983230072969 + 3 ^ 40 * 2713323 * 2
def baseEnd_2713323 : Nat := 928825913266261896656107

theorem tailTrace_2713323 : CollatzResearch.WordTrace tailWord_2713323 prefixEnd_2713323 928825913266261896656107 := by
  unfold tailWord_2713323
  simp only [CollatzResearch.WordTrace]
  refine ⟨98963019949101644520456623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65975346632734429680304415 98963019949101644520456623)
  ·
    refine ⟨148444529923652466780684935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98963019949101644520456623 148444529923652466780684935)
    ·
      refine ⟨222666794885478700171027403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148444529923652466780684935 222666794885478700171027403)
      ·
        refine ⟨334000192328218050256541105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222666794885478700171027403 334000192328218050256541105)
        ·
          refine ⟨250500144246163537692405829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334000192328218050256541105 250500144246163537692405829)
          ·
            refine ⟨46968777046155663317326093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250500144246163537692405829 46968777046155663317326093)
            ·
              refine ⟨17613291392308373743997285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46968777046155663317326093 17613291392308373743997285)
              ·
                refine ⟨3302492136057820076999491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17613291392308373743997285 3302492136057820076999491)
                ·
                  refine ⟨4953738204086730115499237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302492136057820076999491 4953738204086730115499237)
                  ·
                    refine ⟨928825913266261896656107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953738204086730115499237 928825913266261896656107)
                    ·
                      rfl

theorem cell22_2713323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 4].length) (baseStart_2713323 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713323 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713323 prefixEnd_2713323 := by exact prefixLift 2713323
  have htrace : WordTrace (prefixWord ++ tailWord_2713323) baseStart_2713323 baseEnd_2713323 := by
    simpa [prefixWord, tailWord_2713323, baseEnd_2713323] using wordTrace_append hprefix tailTrace_2713323
  have hstable : (prefixWord ++ tailWord_2713323).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713323).length < 2 ^ (prefixWord ++ tailWord_2713323).sum := by decide
  have hdescent : baseEnd_2713323 < baseStart_2713323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713374 : List Nat := [4, 3, 2, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2713374 : Nat := 118140960795 + 2713374 * 2 ^ 59
def prefixEnd_2713374 : Nat := 4983230072969 + 3 ^ 40 * 2713374 * 2
def baseEnd_2713374 : Nat := 928843371608514763630951

theorem tailTrace_2713374 : CollatzResearch.WordTrace tailWord_2713374 prefixEnd_2713374 928843371608514763630951 := by
  unfold tailWord_2713374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12370610008989610028820397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65976586714611253487042117 12370610008989610028820397)
  ·
    refine ⟨4638978753371103760807649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12370610008989610028820397 4638978753371103760807649)
    ·
      refine ⟨3479234065028327820605737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638978753371103760807649 3479234065028327820605737)
      ·
        refine ⟨2609425548771245865454303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3479234065028327820605737 2609425548771245865454303)
        ·
          refine ⟨3914138323156868798181455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2609425548771245865454303 3914138323156868798181455)
          ·
            refine ⟨5871207484735303197272183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914138323156868798181455 5871207484735303197272183)
            ·
              refine ⟨8806811227102954795908275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871207484735303197272183 8806811227102954795908275)
              ·
                refine ⟨13210216840654432193862413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8806811227102954795908275 13210216840654432193862413)
                ·
                  refine ⟨4953831315245412072698405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13210216840654432193862413 4953831315245412072698405)
                  ·
                    refine ⟨928843371608514763630951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4953831315245412072698405 928843371608514763630951)
                    ·
                      rfl

theorem cell22_2713374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2713374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713374 prefixEnd_2713374 := by exact prefixLift 2713374
  have htrace : WordTrace (prefixWord ++ tailWord_2713374) baseStart_2713374 baseEnd_2713374 := by
    simpa [prefixWord, tailWord_2713374, baseEnd_2713374] using wordTrace_append hprefix tailTrace_2713374
  have hstable : (prefixWord ++ tailWord_2713374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713374).length < 2 ^ (prefixWord ++ tailWord_2713374).sum := by decide
  have hdescent : baseEnd_2713374 < baseStart_2713374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713462 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_2713462 : Nat := 118140960795 + 2713462 * 2 ^ 59
def prefixEnd_2713462 : Nat := 4983230072969 + 3 ^ 40 * 2713462 * 2
def baseEnd_2713462 : Nat := 309624498602303955810227

theorem tailTrace_2713462 : CollatzResearch.WordTrace tailWord_2713462 prefixEnd_2713462 309624498602303955810227 := by
  unfold tailWord_2713462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6185505605974879453735415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 65978726463732047506511093 6185505605974879453735415)
  ·
    refine ⟨9278258408962319180603123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6185505605974879453735415 9278258408962319180603123)
    ·
      refine ⟨13917387613443478770904685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9278258408962319180603123 13917387613443478770904685)
      ·
        refine ⟨5219020355041304539089257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13917387613443478770904685 5219020355041304539089257)
        ·
          refine ⟨3914265266280978404316943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219020355041304539089257 3914265266280978404316943)
          ·
            refine ⟨5871397899421467606475415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914265266280978404316943 5871397899421467606475415)
            ·
              refine ⟨8807096849132201409713123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5871397899421467606475415 8807096849132201409713123)
              ·
                refine ⟨13210645273698302114569685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8807096849132201409713123 13210645273698302114569685)
                ·
                  refine ⟨309624498602303955810227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13210645273698302114569685 309624498602303955810227)
                  ·
                    rfl

theorem cell22_2713462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_2713462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713462 prefixEnd_2713462 := by exact prefixLift 2713462
  have htrace : WordTrace (prefixWord ++ tailWord_2713462) baseStart_2713462 baseEnd_2713462 := by
    simpa [prefixWord, tailWord_2713462, baseEnd_2713462] using wordTrace_append hprefix tailTrace_2713462
  have hstable : (prefixWord ++ tailWord_2713462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713462).length < 2 ^ (prefixWord ++ tailWord_2713462).sum := by decide
  have hdescent : baseEnd_2713462 < baseStart_2713462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713492 : List Nat := [2, 4, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_2713492 : Nat := 118140960795 + 2713492 * 2 ^ 59
def prefixEnd_2713492 : Nat := 4983230072969 + 3 ^ 40 * 2713492 * 2
def baseEnd_2713492 : Nat := 928883765420001789180589

theorem tailTrace_2713492 : CollatzResearch.WordTrace tailWord_2713492 prefixEnd_2713492 928883765420001789180589 := by
  unfold tailWord_2713492
  simp only [CollatzResearch.WordTrace]
  refine ⟨49484591942744693191679365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65979455923659590922239153 49484591942744693191679365)
  ·
    refine ⟨9278360989264629973439881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49484591942744693191679365 9278360989264629973439881)
    ·
      refine ⟨6958770741948472480079911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9278360989264629973439881 6958770741948472480079911)
      ·
        refine ⟨10438156112922708720119867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6958770741948472480079911 10438156112922708720119867)
        ·
          refine ⟨15657234169384063080179801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10438156112922708720119867 15657234169384063080179801)
          ·
            refine ⟨11742925627038047310134851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15657234169384063080179801 11742925627038047310134851)
            ·
              refine ⟨17614388440557070965202277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11742925627038047310134851 17614388440557070965202277)
              ·
                refine ⟨3302697832604450805975427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17614388440557070965202277 3302697832604450805975427)
                ·
                  refine ⟨4954046748906676208963141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3302697832604450805975427 4954046748906676208963141)
                  ·
                    refine ⟨928883765420001789180589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954046748906676208963141 928883765420001789180589)
                    ·
                      rfl

theorem cell22_2713492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_2713492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713492 prefixEnd_2713492 := by exact prefixLift 2713492
  have htrace : WordTrace (prefixWord ++ tailWord_2713492) baseStart_2713492 baseEnd_2713492 := by
    simpa [prefixWord, tailWord_2713492, baseEnd_2713492] using wordTrace_append hprefix tailTrace_2713492
  have hstable : (prefixWord ++ tailWord_2713492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713492).length < 2 ^ (prefixWord ++ tailWord_2713492).sum := by decide
  have hdescent : baseEnd_2713492 < baseStart_2713492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713554 : List Nat := [3, 2, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_2713554 : Nat := 118140960795 + 2713554 * 2 ^ 59
def prefixEnd_2713554 : Nat := 4983230072969 + 3 ^ 40 * 2713554 * 2
def baseEnd_2713554 : Nat := 928904989287054294130399

theorem tailTrace_2713554 : CollatzResearch.WordTrace tailWord_2713554 prefixEnd_2713554 928904989287054294130399 := by
  unfold tailWord_2713554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24742861302816192743028929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65980963474176513981410477 24742861302816192743028929)
  ·
    refine ⟨18557145977112144557271697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24742861302816192743028929 18557145977112144557271697)
    ·
      refine ⟨13917859482834108417953773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18557145977112144557271697 13917859482834108417953773)
      ·
        refine ⟨5219197306062790656732665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13917859482834108417953773 5219197306062790656732665)
        ·
          refine ⟨3914397979547092992549499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5219197306062790656732665 3914397979547092992549499)
          ·
            refine ⟨5871596969320639488824249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914397979547092992549499 5871596969320639488824249)
            ·
              refine ⟨4403697726990479616618187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5871596969320639488824249 4403697726990479616618187)
              ·
                refine ⟨6605546590485719424927281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4403697726990479616618187 6605546590485719424927281)
                ·
                  refine ⟨4954159942864289568695461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6605546590485719424927281 4954159942864289568695461)
                  ·
                    refine ⟨928904989287054294130399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954159942864289568695461 928904989287054294130399)
                    ·
                      rfl

theorem cell22_2713554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_2713554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713554 prefixEnd_2713554 := by exact prefixLift 2713554
  have htrace : WordTrace (prefixWord ++ tailWord_2713554) baseStart_2713554 baseEnd_2713554 := by
    simpa [prefixWord, tailWord_2713554, baseEnd_2713554] using wordTrace_append hprefix tailTrace_2713554
  have hstable : (prefixWord ++ tailWord_2713554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713554).length < 2 ^ (prefixWord ++ tailWord_2713554).sum := by decide
  have hdescent : baseEnd_2713554 < baseStart_2713554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713642 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_2713642 : Nat := 118140960795 + 2713642 * 2 ^ 59
def prefixEnd_2713642 : Nat := 4983230072969 + 3 ^ 40 * 2713642 * 2
def baseEnd_2713642 : Nat := 309645037828483799310043

theorem tailTrace_2713642 : CollatzResearch.WordTrace tailWord_2713642 prefixEnd_2713642 309645037828483799310043 := by
  unfold tailWord_2713642
  simp only [CollatzResearch.WordTrace]
  refine ⟨24743663708736490500329795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65983103223297308000879453 24743663708736490500329795)
  ·
    refine ⟨37115495563104735750494693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24743663708736490500329795 37115495563104735750494693)
    ·
      refine ⟨6959155418082137953217755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37115495563104735750494693 6959155418082137953217755)
      ·
        refine ⟨10438733127123206929826633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6959155418082137953217755 10438733127123206929826633)
        ·
          refine ⟨7829049845342405197369975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10438733127123206929826633 7829049845342405197369975)
          ·
            refine ⟨11743574768013607796054963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829049845342405197369975 11743574768013607796054963)
            ·
              refine ⟨17615362152020411694082445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11743574768013607796054963 17615362152020411694082445)
              ·
                refine ⟨6605760807007654385280917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17615362152020411694082445 6605760807007654385280917)
                ·
                  refine ⟨309645037828483799310043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6605760807007654385280917 309645037828483799310043)
                  ·
                    rfl

theorem cell22_2713642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_2713642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713642 prefixEnd_2713642 := by exact prefixLift 2713642
  have htrace : WordTrace (prefixWord ++ tailWord_2713642) baseStart_2713642 baseEnd_2713642 := by
    simpa [prefixWord, tailWord_2713642, baseEnd_2713642] using wordTrace_append hprefix tailTrace_2713642
  have hstable : (prefixWord ++ tailWord_2713642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713642).length < 2 ^ (prefixWord ++ tailWord_2713642).sum := by decide
  have hdescent : baseEnd_2713642 < baseStart_2713642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713655 : List Nat := [1, 1, 3, 1, 2, 2, 3, 2, 1, 6]
def baseStart_2713655 : Nat := 118140960795 + 2713655 * 2 ^ 59
def prefixEnd_2713655 : Nat := 4983230072969 + 3 ^ 40 * 2713655 * 2
def baseEnd_2713655 : Nat := 928939563651123697355089

theorem tailTrace_2713655 : CollatzResearch.WordTrace tailWord_2713655 prefixEnd_2713655 928939563651123697355089 := by
  unfold tailWord_2713655
  simp only [CollatzResearch.WordTrace]
  refine ⟨98975128983898865221542419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65983419322599243481028279 98975128983898865221542419)
  ·
    refine ⟨148462693475848297832313629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98975128983898865221542419 148462693475848297832313629)
    ·
      refine ⟨55673510053443111687117611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148462693475848297832313629 55673510053443111687117611)
      ·
        refine ⟨83510265080164667530676417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55673510053443111687117611 83510265080164667530676417)
        ·
          refine ⟨62632698810123500648007313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83510265080164667530676417 62632698810123500648007313)
          ·
            refine ⟨46974524107592625486005485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62632698810123500648007313 46974524107592625486005485)
            ·
              refine ⟨17615446540347234557252057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46974524107592625486005485 17615446540347234557252057)
              ·
                refine ⟨13211584905260425917939043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17615446540347234557252057 13211584905260425917939043)
                ·
                  refine ⟨19817377357890638876908565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13211584905260425917939043 19817377357890638876908565)
                  ·
                    refine ⟨928939563651123697355089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19817377357890638876908565 928939563651123697355089)
                    ·
                      rfl

theorem cell22_2713655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 6].length) (baseStart_2713655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713655 prefixEnd_2713655 := by exact prefixLift 2713655
  have htrace : WordTrace (prefixWord ++ tailWord_2713655) baseStart_2713655 baseEnd_2713655 := by
    simpa [prefixWord, tailWord_2713655, baseEnd_2713655] using wordTrace_append hprefix tailTrace_2713655
  have hstable : (prefixWord ++ tailWord_2713655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713655).length < 2 ^ (prefixWord ++ tailWord_2713655).sum := by decide
  have hdescent : baseEnd_2713655 < baseStart_2713655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713693 : List Nat := [1, 4, 4, 1, 1, 2, 3, 2, 4]
def baseStart_2713693 : Nat := 118140960795 + 2713693 * 2 ^ 59
def prefixEnd_2713693 : Nat := 4983230072969 + 3 ^ 40 * 2713693 * 2
def baseEnd_2713693 : Nat := 309650857275901421634991

theorem tailTrace_2713693 : CollatzResearch.WordTrace tailWord_2713693 prefixEnd_2713693 309650857275901421634991 := by
  unfold tailWord_2713693
  simp only [CollatzResearch.WordTrace]
  refine ⟨98976514957761197711425733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65984343305174131807617155 98976514957761197711425733)
  ·
    refine ⟨18558096554580224570892325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 98976514957761197711425733 18558096554580224570892325)
    ·
      refine ⟨3479643103983792107042311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18558096554580224570892325 3479643103983792107042311)
      ·
        refine ⟨5219464655975688160563467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3479643103983792107042311 5219464655975688160563467)
        ·
          refine ⟨7829196983963532240845201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5219464655975688160563467 7829196983963532240845201)
          ·
            refine ⟨5871897737972649180633901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7829196983963532240845201 5871897737972649180633901)
            ·
              refine ⟨2201961651739743442737713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5871897737972649180633901 2201961651739743442737713)
              ·
                refine ⟨1651471238804807582053285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2201961651739743442737713 1651471238804807582053285)
                ·
                  refine ⟨309650857275901421634991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651471238804807582053285 309650857275901421634991)
                  ·
                    rfl

theorem cell22_2713693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_2713693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713693 prefixEnd_2713693 := by exact prefixLift 2713693
  have htrace : WordTrace (prefixWord ++ tailWord_2713693) baseStart_2713693 baseEnd_2713693 := by
    simpa [prefixWord, tailWord_2713693, baseEnd_2713693] using wordTrace_append hprefix tailTrace_2713693
  have hstable : (prefixWord ++ tailWord_2713693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713693).length < 2 ^ (prefixWord ++ tailWord_2713693).sum := by decide
  have hdescent : baseEnd_2713693 < baseStart_2713693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713764 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 2, 5]
def baseStart_2713764 : Nat := 118140960795 + 2713764 * 2 ^ 59
def prefixEnd_2713764 : Nat := 4983230072969 + 3 ^ 40 * 2713764 * 2
def baseEnd_2713764 : Nat := 928976876578683746379755

theorem tailTrace_2713764 : CollatzResearch.WordTrace tailWord_2713764 prefixEnd_2713764 928976876578683746379755 := by
  unfold tailWord_2713764
  simp only [CollatzResearch.WordTrace]
  refine ⟨49489552270251988418630173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65986069693669317891506897 49489552270251988418630173)
  ·
    refine ⟨18558582101344495656986315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49489552270251988418630173 18558582101344495656986315)
    ·
      refine ⟨27837873152016743485479473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18558582101344495656986315 27837873152016743485479473)
      ·
        refine ⟨20878404864012557614109605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27837873152016743485479473 20878404864012557614109605)
        ·
          refine ⟨3914700912002354552645551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20878404864012557614109605 3914700912002354552645551)
          ·
            refine ⟨5872051368003531828968327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3914700912002354552645551 5872051368003531828968327)
            ·
              refine ⟨8808077052005297743452491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872051368003531828968327 8808077052005297743452491)
              ·
                refine ⟨13212115578007946615178737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8808077052005297743452491 13212115578007946615178737)
                ·
                  refine ⟨9909086683505959961384053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13212115578007946615178737 9909086683505959961384053)
                  ·
                    refine ⟨928976876578683746379755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9909086683505959961384053 928976876578683746379755)
                    ·
                      rfl

theorem cell22_2713764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_2713764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713764 prefixEnd_2713764 := by exact prefixLift 2713764
  have htrace : WordTrace (prefixWord ++ tailWord_2713764) baseStart_2713764 baseEnd_2713764 := by
    simpa [prefixWord, tailWord_2713764, baseEnd_2713764] using wordTrace_append hprefix tailTrace_2713764
  have hstable : (prefixWord ++ tailWord_2713764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713764).length < 2 ^ (prefixWord ++ tailWord_2713764).sum := by decide
  have hdescent : baseEnd_2713764 < baseStart_2713764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713796 : List Nat := [2, 3, 3, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2713796 : Nat := 118140960795 + 2713796 * 2 ^ 59
def prefixEnd_2713796 : Nat := 4983230072969 + 3 ^ 40 * 2713796 * 2
def baseEnd_2713796 : Nat := 928987830832646329579657

theorem tailTrace_2713796 : CollatzResearch.WordTrace tailWord_2713796 prefixEnd_2713796 928987830832646329579657 := by
  unfold tailWord_2713796
  simp only [CollatzResearch.WordTrace]
  refine ⟨49490135838194023151212621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65986847784258697534950161 49490135838194023151212621)
  ·
    refine ⟨18558800939322758681704733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49490135838194023151212621 18558800939322758681704733)
    ·
      refine ⟨6959550352246034505639275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18558800939322758681704733 6959550352246034505639275)
      ·
        refine ⟨10439325528369051758458913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6959550352246034505639275 10439325528369051758458913)
        ·
          refine ⟨7829494146276788818844185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10439325528369051758458913 7829494146276788818844185)
          ·
            refine ⟨5872120609707591614133139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7829494146276788818844185 5872120609707591614133139)
            ·
              refine ⟨8808180914561387421199709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872120609707591614133139 8808180914561387421199709)
              ·
                refine ⟨3303067842960520282949891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8808180914561387421199709 3303067842960520282949891)
                ·
                  refine ⟨4954601764440780424424837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303067842960520282949891 4954601764440780424424837)
                  ·
                    refine ⟨928987830832646329579657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954601764440780424424837 928987830832646329579657)
                    ·
                      rfl

theorem cell22_2713796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2713796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713796 prefixEnd_2713796 := by exact prefixLift 2713796
  have htrace : WordTrace (prefixWord ++ tailWord_2713796) baseStart_2713796 baseEnd_2713796 := by
    simpa [prefixWord, tailWord_2713796, baseEnd_2713796] using wordTrace_append hprefix tailTrace_2713796
  have hstable : (prefixWord ++ tailWord_2713796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713796).length < 2 ^ (prefixWord ++ tailWord_2713796).sum := by decide
  have hdescent : baseEnd_2713796 < baseStart_2713796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713807 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 4, 4]
def baseStart_2713807 : Nat := 118140960795 + 2713807 * 2 ^ 59
def prefixEnd_2713807 : Nat := 4983230072969 + 3 ^ 40 * 2713807 * 2
def baseEnd_2713807 : Nat := 928991596357445967554623

theorem tailTrace_2713807 : CollatzResearch.WordTrace tailWord_2713807 prefixEnd_2713807 928991596357445967554623 := by
  unfold tailWord_2713807
  simp only [CollatzResearch.WordTrace]
  refine ⟨98980672879348195181075675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65987115252898796787383783 98980672879348195181075675)
  ·
    refine ⟨148471009319022292771613513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98980672879348195181075675 148471009319022292771613513)
    ·
      refine ⟨111353256989266719578710135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148471009319022292771613513 111353256989266719578710135)
      ·
        refine ⟨167029885483900079368065203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111353256989266719578710135 167029885483900079368065203)
        ·
          refine ⟨250544828225850119052097805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167029885483900079368065203 250544828225850119052097805)
          ·
            refine ⟨93954310584693794644536677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250544828225850119052097805 93954310584693794644536677)
            ·
              refine ⟨17616433234630086495850627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93954310584693794644536677 17616433234630086495850627)
              ·
                refine ⟨26424649851945129743775941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17616433234630086495850627 26424649851945129743775941)
                ·
                  refine ⟨4954621847239711826957989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26424649851945129743775941 4954621847239711826957989)
                  ·
                    refine ⟨928991596357445967554623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954621847239711826957989 928991596357445967554623)
                    ·
                      rfl

theorem cell22_2713807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_2713807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713807 prefixEnd_2713807 := by exact prefixLift 2713807
  have htrace : WordTrace (prefixWord ++ tailWord_2713807) baseStart_2713807 baseEnd_2713807 := by
    simpa [prefixWord, tailWord_2713807, baseEnd_2713807] using wordTrace_append hprefix tailTrace_2713807
  have hstable : (prefixWord ++ tailWord_2713807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713807).length < 2 ^ (prefixWord ++ tailWord_2713807).sum := by decide
  have hdescent : baseEnd_2713807 < baseStart_2713807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713839 : List Nat := [1, 1, 2, 1, 6, 1, 4, 6]
def baseStart_2713839 : Nat := 118140960795 + 2713839 * 2 ^ 59
def prefixEnd_2713839 : Nat := 4983230072969 + 3 ^ 40 * 2713839 * 2
def baseEnd_2713839 : Nat := 103222505623489838972725

theorem tailTrace_2713839 : CollatzResearch.WordTrace tailWord_2713839 prefixEnd_2713839 103222505623489838972725 := by
  unfold tailWord_2713839
  simp only [CollatzResearch.WordTrace]
  refine ⟨98981840015232264646240571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65987893343488176430827047 98981840015232264646240571)
  ·
    refine ⟨148472760022848396969360857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98981840015232264646240571 148472760022848396969360857)
    ·
      refine ⟨111354570017136297727020643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148472760022848396969360857 111354570017136297727020643)
      ·
        refine ⟨167031855025704446590530965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111354570017136297727020643 167031855025704446590530965)
        ·
          refine ⟨7829618204329895933931139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 167031855025704446590530965 7829618204329895933931139)
          ·
            refine ⟨11744427306494843900896709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7829618204329895933931139 11744427306494843900896709)
            ·
              refine ⟨2202080119967783231418133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11744427306494843900896709 2202080119967783231418133)
              ·
                refine ⟨103222505623489838972725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2202080119967783231418133 103222505623489838972725)
                ·
                  rfl

theorem cell22_2713839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 6].length) (baseStart_2713839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713839 prefixEnd_2713839 := by exact prefixLift 2713839
  have htrace : WordTrace (prefixWord ++ tailWord_2713839) baseStart_2713839 baseEnd_2713839 := by
    simpa [prefixWord, tailWord_2713839, baseEnd_2713839] using wordTrace_append hprefix tailTrace_2713839
  have hstable : (prefixWord ++ tailWord_2713839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713839).length < 2 ^ (prefixWord ++ tailWord_2713839).sum := by decide
  have hdescent : baseEnd_2713839 < baseStart_2713839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713867 : List Nat := [1, 1, 1, 1, 5, 2, 1, 3, 7]
def baseStart_2713867 : Nat := 118140960795 + 2713867 * 2 ^ 59
def prefixEnd_2713867 : Nat := 4983230072969 + 3 ^ 40 * 2713867 * 2
def baseEnd_2713867 : Nat := 309670711861208603684813

theorem tailTrace_2713867 : CollatzResearch.WordTrace tailWord_2713867 prefixEnd_2713867 309670711861208603684813 := by
  unfold tailWord_2713867
  simp only [CollatzResearch.WordTrace]
  refine ⟨98982861259130825428259855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65988574172753883618839903 98982861259130825428259855)
  ·
    refine ⟨148474291888696238142389783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98982861259130825428259855 148474291888696238142389783)
    ·
      refine ⟨222711437833044357213584675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148474291888696238142389783 222711437833044357213584675)
      ·
        refine ⟨334067156749566535820377013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222711437833044357213584675 334067156749566535820377013)
        ·
          refine ⟨31318795945271862733160345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334067156749566535820377013 31318795945271862733160345)
          ·
            refine ⟨23489096958953897049870259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31318795945271862733160345 23489096958953897049870259)
            ·
              refine ⟨35233645438430845574805389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23489096958953897049870259 35233645438430845574805389)
              ·
                refine ⟨13212617039411567090552021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35233645438430845574805389 13212617039411567090552021)
                ·
                  refine ⟨309670711861208603684813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13212617039411567090552021 309670711861208603684813)
                  ·
                    rfl

theorem cell22_2713867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_2713867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713867 prefixEnd_2713867 := by exact prefixLift 2713867
  have htrace : WordTrace (prefixWord ++ tailWord_2713867) baseStart_2713867 baseEnd_2713867 := by
    simpa [prefixWord, tailWord_2713867, baseEnd_2713867] using wordTrace_append hprefix tailTrace_2713867
  have hstable : (prefixWord ++ tailWord_2713867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713867).length < 2 ^ (prefixWord ++ tailWord_2713867).sum := by decide
  have hdescent : baseEnd_2713867 < baseStart_2713867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2713871 : List Nat := [1, 1, 2, 1, 1, 1, 3, 8, 1, 3]
def baseStart_2713871 : Nat := 118140960795 + 2713871 * 2 ^ 59
def prefixEnd_2713871 : Nat := 4983230072969 + 3 ^ 40 * 2713871 * 2
def baseEnd_2713871 : Nat := 929013504865371133954427

theorem tailTrace_2713871 : CollatzResearch.WordTrace tailWord_2713871 prefixEnd_2713871 929013504865371133954427 := by
  unfold tailWord_2713871
  simp only [CollatzResearch.WordTrace]
  refine ⟨98983007151116334111405467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65988671434077556074270311 98983007151116334111405467)
  ·
    refine ⟨148474510726674501167108201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98983007151116334111405467 148474510726674501167108201)
    ·
      refine ⟨111355883045005875875331151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148474510726674501167108201 111355883045005875875331151)
      ·
        refine ⟨167033824567508813812996727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111355883045005875875331151 167033824567508813812996727)
        ·
          refine ⟨250550736851263220719495091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167033824567508813812996727 250550736851263220719495091)
          ·
            refine ⟨375826105276894831079242637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250550736851263220719495091 375826105276894831079242637)
            ·
              refine ⟨140934789478835561654715989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 375826105276894831079242637 140934789478835561654715989)
              ·
                refine ⟨1651579564205104238141203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 140934789478835561654715989 1651579564205104238141203)
                ·
                  refine ⟨2477369346307656357211805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651579564205104238141203 2477369346307656357211805)
                  ·
                    refine ⟨929013504865371133954427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477369346307656357211805 929013504865371133954427)
                    ·
                      rfl

theorem cell22_2713871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 1, 3].length) (baseStart_2713871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2713871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2713871 prefixEnd_2713871 := by exact prefixLift 2713871
  have htrace : WordTrace (prefixWord ++ tailWord_2713871) baseStart_2713871 baseEnd_2713871 := by
    simpa [prefixWord, tailWord_2713871, baseEnd_2713871] using wordTrace_append hprefix tailTrace_2713871
  have hstable : (prefixWord ++ tailWord_2713871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2713871).length < 2 ^ (prefixWord ++ tailWord_2713871).sum := by decide
  have hdescent : baseEnd_2713871 < baseStart_2713871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2713871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714008 : List Nat := [2, 1, 2, 5, 1, 3, 2, 6]
def baseStart_2714008 : Nat := 118140960795 + 2714008 * 2 ^ 59
def prefixEnd_2714008 : Nat := 4983230072969 + 3 ^ 40 * 2714008 * 2
def baseEnd_2714008 : Nat := 103228933640572049253223

theorem tailTrace_2714008 : CollatzResearch.WordTrace tailWord_2714008 prefixEnd_2714008 103228933640572049253223 := by
  unfold tailWord_2714008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49494001975810003254571339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65992002634413337672761785 49494001975810003254571339)
  ·
    refine ⟨74241002963715004881857009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49494001975810003254571339 74241002963715004881857009)
    ·
      refine ⟨55680752222786253661392757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74241002963715004881857009 55680752222786253661392757)
      ·
        refine ⟨5220070520886211280755571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55680752222786253661392757 5220070520886211280755571)
        ·
          refine ⟨7830105781329316921133357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220070520886211280755571 7830105781329316921133357)
          ·
            refine ⟨2936289667998493845425009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7830105781329316921133357 2936289667998493845425009)
            ·
              refine ⟨2202217250998870384068757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936289667998493845425009 2202217250998870384068757)
              ·
                refine ⟨103228933640572049253223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2202217250998870384068757 103228933640572049253223)
                ·
                  rfl

theorem cell22_2714008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_2714008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714008 prefixEnd_2714008 := by exact prefixLift 2714008
  have htrace : WordTrace (prefixWord ++ tailWord_2714008) baseStart_2714008 baseEnd_2714008 := by
    simpa [prefixWord, tailWord_2714008, baseEnd_2714008] using wordTrace_append hprefix tailTrace_2714008
  have hstable : (prefixWord ++ tailWord_2714008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714008).length < 2 ^ (prefixWord ++ tailWord_2714008).sum := by decide
  have hdescent : baseEnd_2714008 < baseStart_2714008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714019 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 7]
def baseStart_2714019 : Nat := 118140960795 + 2714019 * 2 ^ 59
def prefixEnd_2714019 : Nat := 4983230072969 + 3 ^ 40 * 2714019 * 2
def baseEnd_2714019 : Nat := 309688056096649360417991

theorem tailTrace_2714019 : CollatzResearch.WordTrace tailWord_2714019 prefixEnd_2714019 309688056096649360417991 := by
  unfold tailWord_2714019
  simp only [CollatzResearch.WordTrace]
  refine ⟨98988405154580155387793111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65992270103053436925195407 98988405154580155387793111)
  ·
    refine ⟨148482607731870233081689667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98988405154580155387793111 148482607731870233081689667)
    ·
      refine ⟨222723911597805349622534501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148482607731870233081689667 222723911597805349622534501)
      ·
        refine ⟨41760733424588503054225219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222723911597805349622534501 41760733424588503054225219)
        ·
          refine ⟨62641100136882754581337829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41760733424588503054225219 62641100136882754581337829)
          ·
            refine ⟨11745206275665516484000843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62641100136882754581337829 11745206275665516484000843)
            ·
              refine ⟨17617809413498274726001265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11745206275665516484000843 17617809413498274726001265)
              ·
                refine ⟨13213357060123706044500949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17617809413498274726001265 13213357060123706044500949)
                ·
                  refine ⟨309688056096649360417991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13213357060123706044500949 309688056096649360417991)
                  ·
                    rfl

theorem cell22_2714019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 7].length) (baseStart_2714019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714019 prefixEnd_2714019 := by exact prefixLift 2714019
  have htrace : WordTrace (prefixWord ++ tailWord_2714019) baseStart_2714019 baseEnd_2714019 := by
    simpa [prefixWord, tailWord_2714019, baseEnd_2714019] using wordTrace_append hprefix tailTrace_2714019
  have hstable : (prefixWord ++ tailWord_2714019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714019).length < 2 ^ (prefixWord ++ tailWord_2714019).sum := by decide
  have hdescent : baseEnd_2714019 < baseStart_2714019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714113 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2714113 : Nat := 118140960795 + 2714113 * 2 ^ 59
def prefixEnd_2714113 : Nat := 4983230072969 + 3 ^ 40 * 2714113 * 2
def baseEnd_2714113 : Nat := 929096346410963169403685

theorem tailTrace_2714113 : CollatzResearch.WordTrace tailWord_2714113 prefixEnd_2714113 929096346410963169403685 := by
  unfold tailWord_2714113
  simp only [CollatzResearch.WordTrace]
  refine ⟨98991833616239609441714993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65994555744159739627809995 98991833616239609441714993)
  ·
    refine ⟨74243875212179707081286245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98991833616239609441714993 74243875212179707081286245)
    ·
      refine ⟨13920726602283695077741171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74243875212179707081286245 13920726602283695077741171)
      ·
        refine ⟨20881089903425542616611757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13920726602283695077741171 20881089903425542616611757)
        ·
          refine ⟨7830408713784578481229409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20881089903425542616611757 7830408713784578481229409)
          ·
            refine ⟨5872806535338433860922057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7830408713784578481229409 5872806535338433860922057)
            ·
              refine ⟨4404604901503825395691543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872806535338433860922057 4404604901503825395691543)
              ·
                refine ⟨6606907352255738093537315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404604901503825395691543 6606907352255738093537315)
                ·
                  refine ⟨9910361028383607140305973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6606907352255738093537315 9910361028383607140305973)
                  ·
                    refine ⟨929096346410963169403685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9910361028383607140305973 929096346410963169403685)
                    ·
                      rfl

theorem cell22_2714113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2714113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714113 prefixEnd_2714113 := by exact prefixLift 2714113
  have htrace : WordTrace (prefixWord ++ tailWord_2714113) baseStart_2714113 baseEnd_2714113 := by
    simpa [prefixWord, tailWord_2714113, baseEnd_2714113] using wordTrace_append hprefix tailTrace_2714113
  have hstable : (prefixWord ++ tailWord_2714113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714113).length < 2 ^ (prefixWord ++ tailWord_2714113).sum := by decide
  have hdescent : baseEnd_2714113 < baseStart_2714113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714132 : List Nat := [2, 4, 3, 1, 1, 2, 2, 3, 4]
def baseStart_2714132 : Nat := 118140960795 + 2714132 * 2 ^ 59
def prefixEnd_2714132 : Nat := 4983230072969 + 3 ^ 40 * 2714132 * 2
def baseEnd_2714132 : Nat := 309700950166417817726209

theorem tailTrace_2714132 : CollatzResearch.WordTrace tailWord_2714132 prefixEnd_2714132 309700950166417817726209 := by
  unfold tailWord_2714132
  simp only [CollatzResearch.WordTrace]
  refine ⟨49496263301585387843328325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65995017735447183791104433 49496263301585387843328325)
  ·
    refine ⟨9280549369047260220624061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49496263301585387843328325 9280549369047260220624061)
    ·
      refine ⟨3480206013392722582734023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9280549369047260220624061 3480206013392722582734023)
      ·
        refine ⟨5220309020089083874101035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480206013392722582734023 5220309020089083874101035)
        ·
          refine ⟨7830463530133625811151553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220309020089083874101035 7830463530133625811151553)
          ·
            refine ⟨5872847647600219358363665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7830463530133625811151553 5872847647600219358363665)
            ·
              refine ⟨4404635735700164518772749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872847647600219358363665 4404635735700164518772749)
              ·
                refine ⟨1651738400887561694539781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4404635735700164518772749 1651738400887561694539781)
                ·
                  refine ⟨309700950166417817726209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651738400887561694539781 309700950166417817726209)
                  ·
                    rfl

theorem cell22_2714132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_2714132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714132 prefixEnd_2714132 := by exact prefixLift 2714132
  have htrace : WordTrace (prefixWord ++ tailWord_2714132) baseStart_2714132 baseEnd_2714132 := by
    simpa [prefixWord, tailWord_2714132, baseEnd_2714132] using wordTrace_append hprefix tailTrace_2714132
  have hstable : (prefixWord ++ tailWord_2714132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714132).length < 2 ^ (prefixWord ++ tailWord_2714132).sum := by decide
  have hdescent : baseEnd_2714132 < baseStart_2714132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714164 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_2714164 : Nat := 118140960795 + 2714164 * 2 ^ 59
def prefixEnd_2714164 : Nat := 4983230072969 + 3 ^ 40 * 2714164 * 2
def baseEnd_2714164 : Nat := 929113804753216036378529

theorem tailTrace_2714164 : CollatzResearch.WordTrace tailWord_2714164 prefixEnd_2714164 929113804753216036378529 := by
  unfold tailWord_2714164
  simp only [CollatzResearch.WordTrace]
  refine ⟨49496846869527422575910773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 65995795826036563434547697 49496846869527422575910773)
  ·
    refine ⟨4640329394018195866491635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49496846869527422575910773 4640329394018195866491635)
    ·
      refine ⟨6960494091027293799737453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640329394018195866491635 6960494091027293799737453)
      ·
        refine ⟨2610185284135235174901545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6960494091027293799737453 2610185284135235174901545)
        ·
          refine ⟨1957638963101426381176159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2610185284135235174901545 1957638963101426381176159)
          ·
            refine ⟨2936458444652139571764239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957638963101426381176159 2936458444652139571764239)
            ·
              refine ⟨4404687666978209357646359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936458444652139571764239 4404687666978209357646359)
              ·
                refine ⟨6607031500467314036469539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404687666978209357646359 6607031500467314036469539)
                ·
                  refine ⟨9910547250700971054704309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6607031500467314036469539 9910547250700971054704309)
                  ·
                    refine ⟨929113804753216036378529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9910547250700971054704309 929113804753216036378529)
                    ·
                      rfl

theorem cell22_2714164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_2714164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714164 prefixEnd_2714164 := by exact prefixLift 2714164
  have htrace : WordTrace (prefixWord ++ tailWord_2714164) baseStart_2714164 baseEnd_2714164 := by
    simpa [prefixWord, tailWord_2714164, baseEnd_2714164] using wordTrace_append hprefix tailTrace_2714164
  have hstable : (prefixWord ++ tailWord_2714164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714164).length < 2 ^ (prefixWord ++ tailWord_2714164).sum := by decide
  have hdescent : baseEnd_2714164 < baseStart_2714164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714201 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_2714201 : Nat := 118140960795 + 2714201 * 2 ^ 59
def prefixEnd_2714201 : Nat := 4983230072969 + 3 ^ 40 * 2714201 * 2
def baseEnd_2714201 : Nat := 929126470609360273203415

theorem tailTrace_2714201 : CollatzResearch.WordTrace tailWord_2714201 prefixEnd_2714201 929126470609360273203415 := by
  unfold tailWord_2714201
  simp only [CollatzResearch.WordTrace]
  refine ⟨98995043239920800470918457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65996695493280533647278971 98995043239920800470918457)
  ·
    refine ⟨74246282429940600353188843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98995043239920800470918457 74246282429940600353188843)
    ·
      refine ⟨111369423644910900529783265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74246282429940600353188843 111369423644910900529783265)
      ·
        refine ⟨83527067733683175397337449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111369423644910900529783265 83527067733683175397337449)
        ·
          refine ⟨62645300800262381548003087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83527067733683175397337449 62645300800262381548003087)
          ·
            refine ⟨93967951200393572322004631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62645300800262381548003087 93967951200393572322004631)
            ·
              refine ⟨140951926800590358483006947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93967951200393572322004631 140951926800590358483006947)
              ·
                refine ⟨211427890200885537724510421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140951926800590358483006947 211427890200885537724510421)
                ·
                  refine ⟨4955341176583254790418213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 211427890200885537724510421 4955341176583254790418213)
                  ·
                    refine ⟨929126470609360273203415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955341176583254790418213 929126470609360273203415)
                    ·
                      rfl

theorem cell22_2714201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_2714201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714201 prefixEnd_2714201 := by exact prefixLift 2714201
  have htrace : WordTrace (prefixWord ++ tailWord_2714201) baseStart_2714201 baseEnd_2714201 := by
    simpa [prefixWord, tailWord_2714201, baseEnd_2714201] using wordTrace_append hprefix tailTrace_2714201
  have hstable : (prefixWord ++ tailWord_2714201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714201).length < 2 ^ (prefixWord ++ tailWord_2714201).sum := by decide
  have hdescent : baseEnd_2714201 < baseStart_2714201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714218 : List Nat := [3, 1, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2714218 : Nat := 118140960795 + 2714218 * 2 ^ 59
def prefixEnd_2714218 : Nat := 4983230072969 + 3 ^ 40 * 2714218 * 2
def baseEnd_2714218 : Nat := 929132290056777895528363

theorem tailTrace_2714218 : CollatzResearch.WordTrace tailWord_2714218 prefixEnd_2714218 929132290056777895528363 := by
  unfold tailWord_2714218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24748915820214803093571827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 65997108853906141582858205 24748915820214803093571827)
  ·
    refine ⟨37123373730322204640357741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24748915820214803093571827 37123373730322204640357741)
    ·
      refine ⟨13921265148870826740134153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37123373730322204640357741 13921265148870826740134153)
      ·
        refine ⟨10440948861653120055100615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13921265148870826740134153 10440948861653120055100615)
        ·
          refine ⟨15661423292479680082650923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10440948861653120055100615 15661423292479680082650923)
          ·
            refine ⟨23492134938719520123976385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15661423292479680082650923 23492134938719520123976385)
            ·
              refine ⟨17619101204039640092982289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23492134938719520123976385 17619101204039640092982289)
              ·
                refine ⟨13214325903029730069736717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17619101204039640092982289 13214325903029730069736717)
                ·
                  refine ⟨4955372213636148776151269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13214325903029730069736717 4955372213636148776151269)
                  ·
                    refine ⟨929132290056777895528363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955372213636148776151269 929132290056777895528363)
                    ·
                      rfl

theorem cell22_2714218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2714218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714218 prefixEnd_2714218 := by exact prefixLift 2714218
  have htrace : WordTrace (prefixWord ++ tailWord_2714218) baseStart_2714218 baseEnd_2714218 := by
    simpa [prefixWord, tailWord_2714218, baseEnd_2714218] using wordTrace_append hprefix tailTrace_2714218
  have hstable : (prefixWord ++ tailWord_2714218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714218).length < 2 ^ (prefixWord ++ tailWord_2714218).sum := by decide
  have hdescent : baseEnd_2714218 < baseStart_2714218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714222 : List Nat := [4, 1, 2, 2, 2, 3, 2, 1, 5]
def baseStart_2714222 : Nat := 118140960795 + 2714222 * 2 ^ 59
def prefixEnd_2714222 : Nat := 4983230072969 + 3 ^ 40 * 2714222 * 2
def baseEnd_2714222 : Nat := 309711219779507739476117

theorem tailTrace_2714222 : CollatzResearch.WordTrace tailWord_2714222 prefixEnd_2714222 309711219779507739476117 := by
  unfold tailWord_2714222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12374476146605590132179115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 65997206115229814038288613 12374476146605590132179115)
  ·
    refine ⟨18561714219908385198268673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12374476146605590132179115 18561714219908385198268673)
    ·
      refine ⟨13921285664931288898701505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18561714219908385198268673 13921285664931288898701505)
      ·
        refine ⟨10440964248698466674026129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13921285664931288898701505 10440964248698466674026129)
        ·
          refine ⟨7830723186523850005519597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10440964248698466674026129 7830723186523850005519597)
          ·
            refine ⟨2936521194946443752069849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7830723186523850005519597 2936521194946443752069849)
            ·
              refine ⟨2202390896209832814052387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2936521194946443752069849 2202390896209832814052387)
              ·
                refine ⟨3303586344314749221078581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2202390896209832814052387 3303586344314749221078581)
                ·
                  refine ⟨309711219779507739476117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3303586344314749221078581 309711219779507739476117)
                  ·
                    rfl

theorem cell22_2714222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_2714222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714222 prefixEnd_2714222 := by exact prefixLift 2714222
  have htrace : WordTrace (prefixWord ++ tailWord_2714222) baseStart_2714222 baseEnd_2714222 := by
    simpa [prefixWord, tailWord_2714222, baseEnd_2714222] using wordTrace_append hprefix tailTrace_2714222
  have hstable : (prefixWord ++ tailWord_2714222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714222).length < 2 ^ (prefixWord ++ tailWord_2714222).sum := by decide
  have hdescent : baseEnd_2714222 < baseStart_2714222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714263 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 2, 4]
def baseStart_2714263 : Nat := 118140960795 + 2714263 * 2 ^ 59
def prefixEnd_2714263 : Nat := 4983230072969 + 3 ^ 40 * 2714263 * 2
def baseEnd_2714263 : Nat := 929147694476412778153225

theorem tailTrace_2714263 : CollatzResearch.WordTrace tailWord_2714263 prefixEnd_2714263 929147694476412778153225 := by
  unfold tailWord_2714263
  simp only [CollatzResearch.WordTrace]
  refine ⟨98997304565696185059675443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65998203043797456706450295 98997304565696185059675443)
  ·
    refine ⟨148495956848544277589513165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98997304565696185059675443 148495956848544277589513165)
    ·
      refine ⟨55685983818204104096067437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148495956848544277589513165 55685983818204104096067437)
      ·
        refine ⟨20882243931826539036025289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55685983818204104096067437 20882243931826539036025289)
        ·
          refine ⟨15661682948869904277018967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20882243931826539036025289 15661682948869904277018967)
          ·
            refine ⟨23492524423304856415528451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15661682948869904277018967 23492524423304856415528451)
            ·
              refine ⟨35238786634957284623292677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23492524423304856415528451 35238786634957284623292677)
              ·
                refine ⟨6607272494054490866867377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35238786634957284623292677 6607272494054490866867377)
                ·
                  refine ⟨4955454370540868150150533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607272494054490866867377 4955454370540868150150533)
                  ·
                    refine ⟨929147694476412778153225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955454370540868150150533 929147694476412778153225)
                    ·
                      rfl

theorem cell22_2714263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_2714263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714263 prefixEnd_2714263 := by exact prefixLift 2714263
  have htrace : WordTrace (prefixWord ++ tailWord_2714263) baseStart_2714263 baseEnd_2714263 := by
    simpa [prefixWord, tailWord_2714263, baseEnd_2714263] using wordTrace_append hprefix tailTrace_2714263
  have hstable : (prefixWord ++ tailWord_2714263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714263).length < 2 ^ (prefixWord ++ tailWord_2714263).sum := by decide
  have hdescent : baseEnd_2714263 < baseStart_2714263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714265 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_2714265 : Nat := 118140960795 + 2714265 * 2 ^ 59
def prefixEnd_2714265 : Nat := 4983230072969 + 3 ^ 40 * 2714265 * 2
def baseEnd_2714265 : Nat := 929148379117285439603219

theorem tailTrace_2714265 : CollatzResearch.WordTrace tailWord_2714265 prefixEnd_2714265 929148379117285439603219 := by
  unfold tailWord_2714265
  simp only [CollatzResearch.WordTrace]
  refine ⟨98997377511688939401248249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65998251674459292934165499 98997377511688939401248249)
  ·
    refine ⟨74248033133766704550936187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98997377511688939401248249 74248033133766704550936187)
    ·
      refine ⟨111372049700650056826404281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74248033133766704550936187 111372049700650056826404281)
      ·
        refine ⟨83529037275487542619803211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111372049700650056826404281 83529037275487542619803211)
        ·
          refine ⟨125293555913231313929704817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83529037275487542619803211 125293555913231313929704817)
          ·
            refine ⟨93970166934923485447278613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125293555913231313929704817 93970166934923485447278613)
            ·
              refine ⟨4404851575074538380341185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 93970166934923485447278613 4404851575074538380341185)
              ·
                refine ⟨3303638681305903785255889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4404851575074538380341185 3303638681305903785255889)
                ·
                  refine ⟨2477729010979427838941917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3303638681305903785255889 2477729010979427838941917)
                  ·
                    refine ⟨929148379117285439603219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477729010979427838941917 929148379117285439603219)
                    ·
                      rfl

theorem cell22_2714265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_2714265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714265 prefixEnd_2714265 := by exact prefixLift 2714265
  have htrace : WordTrace (prefixWord ++ tailWord_2714265) baseStart_2714265 baseEnd_2714265 := by
    simpa [prefixWord, tailWord_2714265, baseEnd_2714265] using wordTrace_append hprefix tailTrace_2714265
  have hstable : (prefixWord ++ tailWord_2714265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714265).length < 2 ^ (prefixWord ++ tailWord_2714265).sum := by decide
  have hdescent : baseEnd_2714265 < baseStart_2714265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714295 : List Nat := [1, 1, 3, 1, 6, 1, 3, 6]
def baseStart_2714295 : Nat := 118140960795 + 2714295 * 2 ^ 59
def prefixEnd_2714295 : Nat := 4983230072969 + 3 ^ 40 * 2714295 * 2
def baseEnd_2714295 : Nat := 103239849858930595705903

theorem tailTrace_2714295 : CollatzResearch.WordTrace tailWord_2714295 prefixEnd_2714295 103239849858930595705903 := by
  unfold tailWord_2714295
  simp only [CollatzResearch.WordTrace]
  refine ⟨98998471701580254524840339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65998981134386836349893559 98998471701580254524840339)
  ·
    refine ⟨148497707552370381787260509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98998471701580254524840339 148497707552370381787260509)
    ·
      refine ⟨55686640332138893170222691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148497707552370381787260509 55686640332138893170222691)
      ·
        refine ⟨83529960498208339755334037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55686640332138893170222691 83529960498208339755334037)
        ·
          refine ⟨3915466898353515926031283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 83529960498208339755334037 3915466898353515926031283)
          ·
            refine ⟨5873200347530273889046925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915466898353515926031283 5873200347530273889046925)
            ·
              refine ⟨2202450130323852708392597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5873200347530273889046925 2202450130323852708392597)
              ·
                refine ⟨103239849858930595705903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2202450130323852708392597 103239849858930595705903)
                ·
                  rfl

theorem cell22_2714295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 3, 6].length) (baseStart_2714295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714295 prefixEnd_2714295 := by exact prefixLift 2714295
  have htrace : WordTrace (prefixWord ++ tailWord_2714295) baseStart_2714295 baseEnd_2714295 := by
    simpa [prefixWord, tailWord_2714295, baseEnd_2714295] using wordTrace_append hprefix tailTrace_2714295
  have hstable : (prefixWord ++ tailWord_2714295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714295).length < 2 ^ (prefixWord ++ tailWord_2714295).sum := by decide
  have hdescent : baseEnd_2714295 < baseStart_2714295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714327 : List Nat := [1, 1, 3, 2, 1, 4, 2, 4, 1, 3]
def baseStart_2714327 : Nat := 118140960795 + 2714327 * 2 ^ 59
def prefixEnd_2714327 : Nat := 4983230072969 + 3 ^ 40 * 2714327 * 2
def baseEnd_2714327 : Nat := 929169602984337944553029

theorem tailTrace_2714327 : CollatzResearch.WordTrace tailWord_2714327 prefixEnd_2714327 929169602984337944553029 := by
  unfold tailWord_2714327
  simp only [CollatzResearch.WordTrace]
  refine ⟨98999638837464323990005235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 65999759224976215993336823 98999638837464323990005235)
  ·
    refine ⟨148499458256196485985007853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98999638837464323990005235 148499458256196485985007853)
    ·
      refine ⟨55687296846073682244377945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148499458256196485985007853 55687296846073682244377945)
      ·
        refine ⟨41765472634555261683283459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55687296846073682244377945 41765472634555261683283459)
        ·
          refine ⟨62648208951832892524925189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41765472634555261683283459 62648208951832892524925189)
          ·
            refine ⟨11746539178468667348423473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62648208951832892524925189 11746539178468667348423473)
            ·
              refine ⟨8809904383851500511317605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11746539178468667348423473 8809904383851500511317605)
              ·
                refine ⟨1651857071972156345872051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8809904383851500511317605 1651857071972156345872051)
                ·
                  refine ⟨2477785607958234518808077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1651857071972156345872051 2477785607958234518808077)
                  ·
                    refine ⟨929169602984337944553029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477785607958234518808077 929169602984337944553029)
                    ·
                      rfl

theorem cell22_2714327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 1, 3].length) (baseStart_2714327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714327 prefixEnd_2714327 := by exact prefixLift 2714327
  have htrace : WordTrace (prefixWord ++ tailWord_2714327) baseStart_2714327 baseEnd_2714327 := by
    simpa [prefixWord, tailWord_2714327, baseEnd_2714327] using wordTrace_append hprefix tailTrace_2714327
  have hstable : (prefixWord ++ tailWord_2714327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714327).length < 2 ^ (prefixWord ++ tailWord_2714327).sum := by decide
  have hdescent : baseEnd_2714327 < baseStart_2714327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714385 : List Nat := [1, 2, 2, 1, 1, 3, 2, 6, 4]
def baseStart_2714385 : Nat := 118140960795 + 2714385 * 2 ^ 59
def prefixEnd_2714385 : Nat := 4983230072969 + 3 ^ 40 * 2714385 * 2
def baseEnd_2714385 : Nat := 309729819189881708867617

theorem tailTrace_2714385 : CollatzResearch.WordTrace tailWord_2714385 prefixEnd_2714385 309729819189881708867617 := by
  unfold tailWord_2714385
  simp only [CollatzResearch.WordTrace]
  refine ⟨99001754271254199895616609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66001169514169466597077739 99001754271254199895616609)
  ·
    refine ⟨74251315703440649921712457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99001754271254199895616609 74251315703440649921712457)
    ·
      refine ⟨55688486777580487441284343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74251315703440649921712457 55688486777580487441284343)
      ·
        refine ⟨83532730166370731161926515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55688486777580487441284343 83532730166370731161926515)
        ·
          refine ⟨125299095249556096742889773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83532730166370731161926515 125299095249556096742889773)
          ·
            refine ⟨46987160718583536278583665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125299095249556096742889773 46987160718583536278583665)
            ·
              refine ⟨35240370538937652208937749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46987160718583536278583665 35240370538937652208937749)
              ·
                refine ⟨1651892369012702447293957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35240370538937652208937749 1651892369012702447293957)
                ·
                  refine ⟨309729819189881708867617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651892369012702447293957 309729819189881708867617)
                  ·
                    rfl

theorem cell22_2714385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 6, 4].length) (baseStart_2714385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714385 prefixEnd_2714385 := by exact prefixLift 2714385
  have htrace : WordTrace (prefixWord ++ tailWord_2714385) baseStart_2714385 baseEnd_2714385 := by
    simpa [prefixWord, tailWord_2714385, baseEnd_2714385] using wordTrace_append hprefix tailTrace_2714385
  have hstable : (prefixWord ++ tailWord_2714385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714385).length < 2 ^ (prefixWord ++ tailWord_2714385).sum := by decide
  have hdescent : baseEnd_2714385 < baseStart_2714385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714404 : List Nat := [2, 3, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_2714404 : Nat := 118140960795 + 2714404 * 2 ^ 59
def prefixEnd_2714404 : Nat := 4983230072969 + 3 ^ 40 * 2714404 * 2
def baseEnd_2714404 : Nat := 929195961657935410377793

theorem tailTrace_2714404 : CollatzResearch.WordTrace tailWord_2714404 prefixEnd_2714404 929195961657935410377793 := by
  unfold tailWord_2714404
  simp only [CollatzResearch.WordTrace]
  refine ⟨49501223629092683070279133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66001631505456910760372177 49501223629092683070279133)
  ·
    refine ⟨18562958860909756151354675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49501223629092683070279133 18562958860909756151354675)
    ·
      refine ⟨27844438291364634227032013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18562958860909756151354675 27844438291364634227032013)
      ·
        refine ⟨10441664359261737835137005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27844438291364634227032013 10441664359261737835137005)
        ·
          refine ⟨3915624134723151688176377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10441664359261737835137005 3915624134723151688176377)
          ·
            refine ⟨2936718101042363766132283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3915624134723151688176377 2936718101042363766132283)
            ·
              refine ⟨4405077151563545649198425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936718101042363766132283 4405077151563545649198425)
              ·
                refine ⟨3303807863672659236898819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4405077151563545649198425 3303807863672659236898819)
                ·
                  refine ⟨4955711795508988855348229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303807863672659236898819 4955711795508988855348229)
                  ·
                    refine ⟨929195961657935410377793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955711795508988855348229 929195961657935410377793)
                    ·
                      rfl

theorem cell22_2714404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_2714404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714404 prefixEnd_2714404 := by exact prefixLift 2714404
  have htrace : WordTrace (prefixWord ++ tailWord_2714404) baseStart_2714404 baseEnd_2714404 := by
    simpa [prefixWord, tailWord_2714404, baseEnd_2714404] using wordTrace_append hprefix tailTrace_2714404
  have hstable : (prefixWord ++ tailWord_2714404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714404).length < 2 ^ (prefixWord ++ tailWord_2714404).sum := by decide
  have hdescent : baseEnd_2714404 < baseStart_2714404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714430 : List Nat := [4, 2, 1, 2, 3, 10]
def baseStart_2714430 : Nat := 118140960795 + 2714430 * 2 ^ 59
def prefixEnd_2714430 : Nat := 4983230072969 + 3 ^ 40 * 2714430 * 2
def baseEnd_2714430 : Nat := 11471664962830617397873

theorem tailTrace_2714430 : CollatzResearch.WordTrace tailWord_2714430 prefixEnd_2714430 11471664962830617397873 := by
  unfold tailWord_2714430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12375424444511396572625593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66002263704060781720669829 12375424444511396572625593)
  ·
    refine ⟨9281568333383547429469195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12375424444511396572625593 9281568333383547429469195)
    ·
      refine ⟨13922352500075321144203793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9281568333383547429469195 13922352500075321144203793)
      ·
        refine ⟨10441764375056490858152845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13922352500075321144203793 10441764375056490858152845)
        ·
          refine ⟨3915661640646184071807317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10441764375056490858152845 3915661640646184071807317)
          ·
            refine ⟨11471664962830617397873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3915661640646184071807317 11471664962830617397873)
            ·
              rfl

theorem cell22_2714430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 10].length) (baseStart_2714430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714430 prefixEnd_2714430 := by exact prefixLift 2714430
  have htrace : WordTrace (prefixWord ++ tailWord_2714430) baseStart_2714430 baseEnd_2714430 := by
    simpa [prefixWord, tailWord_2714430, baseEnd_2714430] using wordTrace_append hprefix tailTrace_2714430
  have hstable : (prefixWord ++ tailWord_2714430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714430).length < 2 ^ (prefixWord ++ tailWord_2714430).sum := by decide
  have hdescent : baseEnd_2714430 < baseStart_2714430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714436 : List Nat := [2, 3, 4, 2, 1, 1, 1, 4, 4]
def baseStart_2714436 : Nat := 118140960795 + 2714436 * 2 ^ 59
def prefixEnd_2714436 : Nat := 4983230072969 + 3 ^ 40 * 2714436 * 2
def baseEnd_2714436 : Nat := 309735638637299331192565

theorem tailTrace_2714436 : CollatzResearch.WordTrace tailWord_2714436 prefixEnd_2714436 309735638637299331192565 := by
  unfold tailWord_2714436
  simp only [CollatzResearch.WordTrace]
  refine ⟨49501807197034717802861581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66002409596046290403815441 49501807197034717802861581)
  ·
    refine ⟨18563177698888019176073093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49501807197034717802861581 18563177698888019176073093)
    ·
      refine ⟨3480595818541503595513705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18563177698888019176073093 3480595818541503595513705)
      ·
        refine ⟨2610446863906127696635279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3480595818541503595513705 2610446863906127696635279)
        ·
          refine ⟨3915670295859191544952919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610446863906127696635279 3915670295859191544952919)
          ·
            refine ⟨5873505443788787317429379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915670295859191544952919 5873505443788787317429379)
            ·
              refine ⟨8810258165683180976144069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873505443788787317429379 8810258165683180976144069)
              ·
                refine ⟨1651923406065596433027013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8810258165683180976144069 1651923406065596433027013)
                ·
                  refine ⟨309735638637299331192565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651923406065596433027013 309735638637299331192565)
                  ·
                    rfl

theorem cell22_2714436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 4].length) (baseStart_2714436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714436 prefixEnd_2714436 := by exact prefixLift 2714436
  have htrace : WordTrace (prefixWord ++ tailWord_2714436) baseStart_2714436 baseEnd_2714436 := by
    simpa [prefixWord, tailWord_2714436, baseEnd_2714436] using wordTrace_append hprefix tailTrace_2714436
  have hstable : (prefixWord ++ tailWord_2714436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714436).length < 2 ^ (prefixWord ++ tailWord_2714436).sum := by decide
  have hdescent : baseEnd_2714436 < baseStart_2714436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714466 : List Nat := [3, 3, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2714466 : Nat := 118140960795 + 2714466 * 2 ^ 59
def prefixEnd_2714466 : Nat := 4983230072969 + 3 ^ 40 * 2714466 * 2
def baseEnd_2714466 : Nat := 929217185524987915327603

theorem tailTrace_2714466 : CollatzResearch.WordTrace tailWord_2714466 prefixEnd_2714466 929217185524987915327603 := by
  unfold tailWord_2714466
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751177145990187682328813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66003139055973833819543501 24751177145990187682328813)
  ·
    refine ⟨9281691429746320380873305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24751177145990187682328813 9281691429746320380873305)
    ·
      refine ⟨6961268572309740285654979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9281691429746320380873305 6961268572309740285654979)
      ·
        refine ⟨10441902858464610428482469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961268572309740285654979 10441902858464610428482469)
        ·
          refine ⟨1957856785962114455340463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10441902858464610428482469 1957856785962114455340463)
          ·
            refine ⟨2936785178943171683010695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1957856785962114455340463 2936785178943171683010695)
            ·
              refine ⟨4405177768414757524516043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2936785178943171683010695 4405177768414757524516043)
              ·
                refine ⟨6607766652622136286774065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405177768414757524516043 6607766652622136286774065)
                ·
                  refine ⟨4955824989466602215080549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607766652622136286774065 4955824989466602215080549)
                  ·
                    refine ⟨929217185524987915327603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955824989466602215080549 929217185524987915327603)
                    ·
                      rfl

theorem cell22_2714466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2714466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714466 prefixEnd_2714466 := by exact prefixLift 2714466
  have htrace : WordTrace (prefixWord ++ tailWord_2714466) baseStart_2714466 baseEnd_2714466 := by
    simpa [prefixWord, tailWord_2714466, baseEnd_2714466] using wordTrace_append hprefix tailTrace_2714466
  have hstable : (prefixWord ++ tailWord_2714466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714466).length < 2 ^ (prefixWord ++ tailWord_2714466).sum := by decide
  have hdescent : baseEnd_2714466 < baseStart_2714466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714552 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 4, 3]
def baseStart_2714552 : Nat := 118140960795 + 2714552 * 2 ^ 59
def prefixEnd_2714552 : Nat := 4983230072969 + 3 ^ 40 * 2714552 * 2
def baseEnd_2714552 : Nat := 929246625082512357677339

theorem tailTrace_2714552 : CollatzResearch.WordTrace tailWord_2714552 prefixEnd_2714552 929246625082512357677339 := by
  unfold tailWord_2714552
  simp only [CollatzResearch.WordTrace]
  refine ⟨49503922630824593708472955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66005230174432791611297273 49503922630824593708472955)
  ·
    refine ⟨74255883946236890562709433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49503922630824593708472955 74255883946236890562709433)
    ·
      refine ⟨55691912959677667922032075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74255883946236890562709433 55691912959677667922032075)
      ·
        refine ⟨83537869439516501883048113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55691912959677667922032075 83537869439516501883048113)
        ·
          refine ⟨62653402079637376412286085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83537869439516501883048113 62653402079637376412286085)
          ·
            refine ⟨11747512889932008077303641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62653402079637376412286085 11747512889932008077303641)
            ·
              refine ⟨8810634667449006057977731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11747512889932008077303641 8810634667449006057977731)
              ·
                refine ⟨13215952001173509086966597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810634667449006057977731 13215952001173509086966597)
                ·
                  refine ⟨2477991000220032953806237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13215952001173509086966597 2477991000220032953806237)
                  ·
                    refine ⟨929246625082512357677339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2477991000220032953806237 929246625082512357677339)
                    ·
                      rfl

theorem cell22_2714552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 4, 3].length) (baseStart_2714552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714552 prefixEnd_2714552 := by exact prefixLift 2714552
  have htrace : WordTrace (prefixWord ++ tailWord_2714552) baseStart_2714552 baseEnd_2714552 := by
    simpa [prefixWord, tailWord_2714552, baseEnd_2714552] using wordTrace_append hprefix tailTrace_2714552
  have hstable : (prefixWord ++ tailWord_2714552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714552).length < 2 ^ (prefixWord ++ tailWord_2714552).sum := by decide
  have hdescent : baseEnd_2714552 < baseStart_2714552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714554 : List Nat := [3, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_2714554 : Nat := 118140960795 + 2714554 * 2 ^ 59
def prefixEnd_2714554 : Nat := 4983230072969 + 3 ^ 40 * 2714554 * 2
def baseEnd_2714554 : Nat := 309749103241128339709111

theorem tailTrace_2714554 : CollatzResearch.WordTrace tailWord_2714554 prefixEnd_2714554 309749103241128339709111 := by
  unfold tailWord_2714554
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751979551910485439629679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66005278805094627839012477 24751979551910485439629679)
  ·
    refine ⟨37127969327865728159444519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24751979551910485439629679 37127969327865728159444519)
    ·
      refine ⟨55691953991798592239166779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37127969327865728159444519 55691953991798592239166779)
      ·
        refine ⟨83537930987697888358750169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55691953991798592239166779 83537930987697888358750169)
        ·
          refine ⟨62653448240773416269062627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83537930987697888358750169 62653448240773416269062627)
          ·
            refine ⟨93980172361160124403593941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62653448240773416269062627 93980172361160124403593941)
            ·
              refine ⟨2202660289714690415709233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93980172361160124403593941 2202660289714690415709233)
              ·
                refine ⟨1651995217286017811781925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2202660289714690415709233 1651995217286017811781925)
                ·
                  refine ⟨309749103241128339709111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1651995217286017811781925 309749103241128339709111)
                  ·
                    rfl

theorem cell22_2714554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_2714554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714554 prefixEnd_2714554 := by exact prefixLift 2714554
  have htrace : WordTrace (prefixWord ++ tailWord_2714554) baseStart_2714554 baseEnd_2714554 := by
    simpa [prefixWord, tailWord_2714554, baseEnd_2714554] using wordTrace_append hprefix tailTrace_2714554
  have hstable : (prefixWord ++ tailWord_2714554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714554).length < 2 ^ (prefixWord ++ tailWord_2714554).sum := by decide
  have hdescent : baseEnd_2714554 < baseStart_2714554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714573 : List Nat := [1, 6, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2714573 : Nat := 118140960795 + 2714573 * 2 ^ 59
def prefixEnd_2714573 : Nat := 4983230072969 + 3 ^ 40 * 2714573 * 2
def baseEnd_2714573 : Nat := 929253813811675302902275

theorem tailTrace_2714573 : CollatzResearch.WordTrace tailWord_2714573 prefixEnd_2714573 929253813811675302902275 := by
  unfold tailWord_2714573
  simp only [CollatzResearch.WordTrace]
  refine ⟨99008611194573108003460373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66005740796382072002306915 99008611194573108003460373)
  ·
    refine ⟨4641028649745614437662205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99008611194573108003460373 4641028649745614437662205)
    ·
      refine ⟨1740385743654605414123327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4641028649745614437662205 1740385743654605414123327)
      ·
        refine ⟨2610578615481908121184991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1740385743654605414123327 2610578615481908121184991)
        ·
          refine ⟨3915867923222862181777487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2610578615481908121184991 3915867923222862181777487)
          ·
            refine ⟨5873801884834293272666231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915867923222862181777487 5873801884834293272666231)
            ·
              refine ⟨8810702827251439908999347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873801884834293272666231 8810702827251439908999347)
              ·
                refine ⟨13216054240877159863499021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810702827251439908999347 13216054240877159863499021)
                ·
                  refine ⟨4956020340328934948812133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13216054240877159863499021 4956020340328934948812133)
                  ·
                    refine ⟨929253813811675302902275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956020340328934948812133 929253813811675302902275)
                    ·
                      rfl

theorem cell22_2714573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2714573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714573 prefixEnd_2714573 := by exact prefixLift 2714573
  have htrace : WordTrace (prefixWord ++ tailWord_2714573) baseStart_2714573 baseEnd_2714573 := by
    simpa [prefixWord, tailWord_2714573, baseEnd_2714573] using wordTrace_append hprefix tailTrace_2714573
  have hstable : (prefixWord ++ tailWord_2714573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714573).length < 2 ^ (prefixWord ++ tailWord_2714573).sum := by decide
  have hdescent : baseEnd_2714573 < baseStart_2714573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714672 : List Nat := [2, 1, 1, 1, 2, 4, 4, 1, 6]
def baseStart_2714672 : Nat := 118140960795 + 2714672 * 2 ^ 59
def prefixEnd_2714672 : Nat := 4983230072969 + 3 ^ 40 * 2714672 * 2
def baseEnd_2714672 : Nat := 309762567844957348225657

theorem tailTrace_2714672 : CollatzResearch.WordTrace tailWord_2714672 prefixEnd_2714672 309762567844957348225657 := by
  unfold tailWord_2714672
  simp only [CollatzResearch.WordTrace]
  refine ⟨49506111010607223955657135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66008148014142965274209513 49506111010607223955657135)
  ·
    refine ⟨74259166515910835933485703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49506111010607223955657135 74259166515910835933485703)
    ·
      refine ⟨111388749773866253900228555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74259166515910835933485703 111388749773866253900228555)
      ·
        refine ⟨167083124660799380850342833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111388749773866253900228555 167083124660799380850342833)
        ·
          refine ⟨125312343495599535637757125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167083124660799380850342833 125312343495599535637757125)
          ·
            refine ⟨23496064405424912932079461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125312343495599535637757125 23496064405424912932079461)
            ·
              refine ⟨4405512076017171174764899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23496064405424912932079461 4405512076017171174764899)
              ·
                refine ⟨6608268114025756762147349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405512076017171174764899 6608268114025756762147349)
                ·
                  refine ⟨309762567844957348225657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6608268114025756762147349 309762567844957348225657)
                  ·
                    rfl

theorem cell22_2714672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 1, 6].length) (baseStart_2714672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714672 prefixEnd_2714672 := by exact prefixLift 2714672
  have htrace : WordTrace (prefixWord ++ tailWord_2714672) baseStart_2714672 baseEnd_2714672 := by
    simpa [prefixWord, tailWord_2714672, baseEnd_2714672] using wordTrace_append hprefix tailTrace_2714672
  have hstable : (prefixWord ++ tailWord_2714672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714672).length < 2 ^ (prefixWord ++ tailWord_2714672).sum := by decide
  have hdescent : baseEnd_2714672 < baseStart_2714672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714702 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 1, 6]
def baseStart_2714702 : Nat := 118140960795 + 2714702 * 2 ^ 59
def prefixEnd_2714702 : Nat := 4983230072969 + 3 ^ 40 * 2714702 * 2
def baseEnd_2714702 : Nat := 929297973147961966426879

theorem tailTrace_2714702 : CollatzResearch.WordTrace tailWord_2714702 prefixEnd_2714702 929297973147961966426879 := by
  unfold tailWord_2714702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376664526388220379363295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66008877474070508689937573 12376664526388220379363295)
  ·
    refine ⟨18564996789582330569044943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12376664526388220379363295 18564996789582330569044943)
    ·
      refine ⟨27847495184373495853567415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18564996789582330569044943 27847495184373495853567415)
      ·
        refine ⟨41771242776560243780351123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847495184373495853567415 41771242776560243780351123)
        ·
          refine ⟨62656864164840365670526685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41771242776560243780351123 62656864164840365670526685)
          ·
            refine ⟨23496324061815137126447507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62656864164840365670526685 23496324061815137126447507)
            ·
              refine ⟨35244486092722705689671261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23496324061815137126447507 35244486092722705689671261)
              ·
                refine ⟨13216682284771014633626723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35244486092722705689671261 13216682284771014633626723)
                ·
                  refine ⟨19825023427156521950440085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13216682284771014633626723 19825023427156521950440085)
                  ·
                    refine ⟨929297973147961966426879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19825023427156521950440085 929297973147961966426879)
                    ·
                      rfl

theorem cell22_2714702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_2714702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714702 prefixEnd_2714702 := by exact prefixLift 2714702
  have htrace : WordTrace (prefixWord ++ tailWord_2714702) baseStart_2714702 baseEnd_2714702 := by
    simpa [prefixWord, tailWord_2714702, baseEnd_2714702] using wordTrace_append hprefix tailTrace_2714702
  have hstable : (prefixWord ++ tailWord_2714702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714702).length < 2 ^ (prefixWord ++ tailWord_2714702).sum := by decide
  have hdescent : baseEnd_2714702 < baseStart_2714702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714706 : List Nat := [3, 2, 2, 1, 3, 1, 3, 3, 4]
def baseStart_2714706 : Nat := 118140960795 + 2714706 * 2 ^ 59
def prefixEnd_2714706 : Nat := 4983230072969 + 3 ^ 40 * 2714706 * 2
def baseEnd_2714706 : Nat := 309766447476569096442289

theorem tailTrace_2714706 : CollatzResearch.WordTrace tailWord_2714706 prefixEnd_2714706 309766447476569096442289 := by
  unfold tailWord_2714706
  simp only [CollatzResearch.WordTrace]
  refine ⟨24753365525772817929512993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66008974735394181145367981 24753365525772817929512993)
  ·
    refine ⟨18565024144329613447134745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24753365525772817929512993 18565024144329613447134745)
    ·
      refine ⟨13923768108247210085351059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18565024144329613447134745 13923768108247210085351059)
      ·
        refine ⟨20885652162370815128026589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13923768108247210085351059 20885652162370815128026589)
        ·
          refine ⟨7832119560889055673009971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20885652162370815128026589 7832119560889055673009971)
          ·
            refine ⟨11748179341333583509514957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832119560889055673009971 11748179341333583509514957)
            ·
              refine ⟨4405567253000093816068109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11748179341333583509514957 4405567253000093816068109)
              ·
                refine ⟨1652087719875035181025541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4405567253000093816068109 1652087719875035181025541)
                ·
                  refine ⟨309766447476569096442289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1652087719875035181025541 309766447476569096442289)
                  ·
                    rfl

theorem cell22_2714706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_2714706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714706 prefixEnd_2714706 := by exact prefixLift 2714706
  have htrace : WordTrace (prefixWord ++ tailWord_2714706) baseStart_2714706 baseEnd_2714706 := by
    simpa [prefixWord, tailWord_2714706, baseEnd_2714706] using wordTrace_append hprefix tailTrace_2714706
  have hstable : (prefixWord ++ tailWord_2714706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714706).length < 2 ^ (prefixWord ++ tailWord_2714706).sum := by decide
  have hdescent : baseEnd_2714706 < baseStart_2714706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714734 : List Nat := [4, 1, 2, 2, 1, 3, 2, 7]
def baseStart_2714734 : Nat := 118140960795 + 2714734 * 2 ^ 59
def prefixEnd_2714734 : Nat := 4983230072969 + 3 ^ 40 * 2714734 * 2
def baseEnd_2714734 : Nat := 103256547489102727736309

theorem tailTrace_2714734 : CollatzResearch.WordTrace tailWord_2714734 prefixEnd_2714734 103256547489102727736309 := by
  unfold tailWord_2714734
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376810418373729062508907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66009655564659888333380837 12376810418373729062508907)
  ·
    refine ⟨18565215627560593593763361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12376810418373729062508907 18565215627560593593763361)
    ·
      refine ⟨13923911720670445195322521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18565215627560593593763361 13923911720670445195322521)
      ·
        refine ⟨10442933790502833896491891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13923911720670445195322521 10442933790502833896491891)
        ·
          refine ⟨15664400685754250844737837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10442933790502833896491891 15664400685754250844737837)
          ·
            refine ⟨5874150257157844066776689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15664400685754250844737837 5874150257157844066776689)
            ·
              refine ⟨4405612692868383050082517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5874150257157844066776689 4405612692868383050082517)
              ·
                refine ⟨103256547489102727736309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4405612692868383050082517 103256547489102727736309)
                ·
                  rfl

theorem cell22_2714734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_2714734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714734 prefixEnd_2714734 := by exact prefixLift 2714734
  have htrace : WordTrace (prefixWord ++ tailWord_2714734) baseStart_2714734 baseEnd_2714734 := by
    simpa [prefixWord, tailWord_2714734, baseEnd_2714734] using wordTrace_append hprefix tailTrace_2714734
  have hstable : (prefixWord ++ tailWord_2714734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714734).length < 2 ^ (prefixWord ++ tailWord_2714734).sum := by decide
  have hdescent : baseEnd_2714734 < baseStart_2714734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714749 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_2714749 : Nat := 118140960795 + 2714749 * 2 ^ 59
def prefixEnd_2714749 : Nat := 4983230072969 + 3 ^ 40 * 2714749 * 2
def baseEnd_2714749 : Nat := 929314062208469510501735

theorem tailTrace_2714749 : CollatzResearch.WordTrace tailWord_2714749 prefixEnd_2714749 929314062208469510501735 := by
  unfold tailWord_2714749
  simp only [CollatzResearch.WordTrace]
  refine ⟨99015030441935490061867301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66010020294623660041244867 99015030441935490061867301)
  ·
    refine ⟨18565318207862904386600119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99015030441935490061867301 18565318207862904386600119)
    ·
      refine ⟨27847977311794356579900179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18565318207862904386600119 27847977311794356579900179)
      ·
        refine ⟨41771965967691534869850269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847977311794356579900179 41771965967691534869850269)
        ·
          refine ⟨15664487237884325576193851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41771965967691534869850269 15664487237884325576193851)
          ·
            refine ⟨23496730856826488364290777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15664487237884325576193851 23496730856826488364290777)
            ·
              refine ⟨17622548142619866273218083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23496730856826488364290777 17622548142619866273218083)
              ·
                refine ⟨26433822213929799409827125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17622548142619866273218083 26433822213929799409827125)
                ·
                  refine ⟨2478170832555918694671293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26433822213929799409827125 2478170832555918694671293)
                  ·
                    refine ⟨929314062208469510501735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2478170832555918694671293 929314062208469510501735)
                    ·
                      rfl

theorem cell22_2714749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_2714749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714749 prefixEnd_2714749 := by exact prefixLift 2714749
  have htrace : WordTrace (prefixWord ++ tailWord_2714749) baseStart_2714749 baseEnd_2714749 := by
    simpa [prefixWord, tailWord_2714749, baseEnd_2714749] using wordTrace_append hprefix tailTrace_2714749
  have hstable : (prefixWord ++ tailWord_2714749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714749).length < 2 ^ (prefixWord ++ tailWord_2714749).sum := by decide
  have hdescent : baseEnd_2714749 < baseStart_2714749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714809 : List Nat := [1, 2, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_2714809 : Nat := 118140960795 + 2714809 * 2 ^ 59
def prefixEnd_2714809 : Nat := 4983230072969 + 3 ^ 40 * 2714809 * 2
def baseEnd_2714809 : Nat := 929334601434649354001551

theorem tailTrace_2714809 : CollatzResearch.WordTrace tailWord_2714809 prefixEnd_2714809 929334601434649354001551 := by
  unfold tailWord_2714809
  simp only [CollatzResearch.WordTrace]
  refine ⟨99017218821718120309051481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66011479214478746872700987 99017218821718120309051481)
  ·
    refine ⟨74262914116288590231788611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99017218821718120309051481 74262914116288590231788611)
    ·
      refine ⟨111394371174432885347682917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74262914116288590231788611 111394371174432885347682917)
      ·
        refine ⟨20886444595206166002690547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111394371174432885347682917 20886444595206166002690547)
        ·
          refine ⟨31329666892809249004035821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20886444595206166002690547 31329666892809249004035821)
          ·
            refine ⟨11748625084803468376513433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31329666892809249004035821 11748625084803468376513433)
            ·
              refine ⟨8811468813602601282385075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11748625084803468376513433 8811468813602601282385075)
              ·
                refine ⟨13217203220403901923577613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8811468813602601282385075 13217203220403901923577613)
                ·
                  refine ⟨4956451207651463221341605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13217203220403901923577613 4956451207651463221341605)
                  ·
                    refine ⟨929334601434649354001551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956451207651463221341605 929334601434649354001551)
                    ·
                      rfl

theorem cell22_2714809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_2714809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714809 prefixEnd_2714809 := by exact prefixLift 2714809
  have htrace : WordTrace (prefixWord ++ tailWord_2714809) baseStart_2714809 baseEnd_2714809 := by
    simpa [prefixWord, tailWord_2714809, baseEnd_2714809] using wordTrace_append hprefix tailTrace_2714809
  have hstable : (prefixWord ++ tailWord_2714809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714809).length < 2 ^ (prefixWord ++ tailWord_2714809).sum := by decide
  have hdescent : baseEnd_2714809 < baseStart_2714809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714826 : List Nat := [3, 1, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_2714826 : Nat := 118140960795 + 2714826 * 2 ^ 59
def prefixEnd_2714826 : Nat := 4983230072969 + 3 ^ 40 * 2714826 * 2
def baseEnd_2714826 : Nat := 929340420882066976326499

theorem tailTrace_2714826 : CollatzResearch.WordTrace tailWord_2714826 prefixEnd_2714826 929340420882066976326499 := by
  unfold tailWord_2714826
  simp only [CollatzResearch.WordTrace]
  refine ⟨24754459715664133053105083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66011892575104354808280221 24754459715664133053105083)
  ·
    refine ⟨37131689573496199579657625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24754459715664133053105083 37131689573496199579657625)
    ·
      refine ⟨27848767180122149684743219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37131689573496199579657625 27848767180122149684743219)
      ·
        refine ⟨41773150770183224527114829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27848767180122149684743219 41773150770183224527114829)
        ·
          refine ⟨15664931538818709197668061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41773150770183224527114829 15664931538818709197668061)
          ·
            refine ⟨5874349327057015949125523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15664931538818709197668061 5874349327057015949125523)
            ·
              refine ⟨8811523990585523923688285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874349327057015949125523 8811523990585523923688285)
              ·
                refine ⟨3304321496469571471383107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8811523990585523923688285 3304321496469571471383107)
                ·
                  refine ⟨4956482244704357207074661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304321496469571471383107 4956482244704357207074661)
                  ·
                    refine ⟨929340420882066976326499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956482244704357207074661 929340420882066976326499)
                    ·
                      rfl

theorem cell22_2714826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_2714826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714826 prefixEnd_2714826 := by exact prefixLift 2714826
  have htrace : WordTrace (prefixWord ++ tailWord_2714826) baseStart_2714826 baseEnd_2714826 := by
    simpa [prefixWord, tailWord_2714826, baseEnd_2714826] using wordTrace_append hprefix tailTrace_2714826
  have hstable : (prefixWord ++ tailWord_2714826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714826).length < 2 ^ (prefixWord ++ tailWord_2714826).sum := by decide
  have hdescent : baseEnd_2714826 < baseStart_2714826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714948 : List Nat := [2, 3, 4, 1, 1, 1, 1, 4, 5]
def baseStart_2714948 : Nat := 118140960795 + 2714948 * 2 ^ 59
def prefixEnd_2714948 : Nat := 4983230072969 + 3 ^ 40 * 2714948 * 2
def baseEnd_2714948 : Nat := 309794061325099774925375

theorem tailTrace_2714948 : CollatzResearch.WordTrace tailWord_2714948 prefixEnd_2714948 309794061325099774925375 := by
  unfold tailWord_2714948
  simp only [CollatzResearch.WordTrace]
  refine ⟨49511144284107273524180749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66014859045476364698907665 49511144284107273524180749)
  ·
    refine ⟨18566679106540227571567781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49511144284107273524180749 18566679106540227571567781)
    ·
      refine ⟨3481252332476292669668959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18566679106540227571567781 3481252332476292669668959)
      ·
        refine ⟨5221878498714439004503439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481252332476292669668959 5221878498714439004503439)
        ·
          refine ⟨7832817748071658506755159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221878498714439004503439 7832817748071658506755159)
          ·
            refine ⟨11749226622107487760132739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832817748071658506755159 11749226622107487760132739)
            ·
              refine ⟨17623839933161231640199109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11749226622107487760132739 17623839933161231640199109)
              ·
                refine ⟨3304469987467730932537333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17623839933161231640199109 3304469987467730932537333)
                ·
                  refine ⟨309794061325099774925375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304469987467730932537333 309794061325099774925375)
                  ·
                    rfl

theorem cell22_2714948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_2714948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714948 prefixEnd_2714948 := by exact prefixLift 2714948
  have htrace : WordTrace (prefixWord ++ tailWord_2714948) baseStart_2714948 baseEnd_2714948 := by
    simpa [prefixWord, tailWord_2714948, baseEnd_2714948] using wordTrace_append hprefix tailTrace_2714948
  have hstable : (prefixWord ++ tailWord_2714948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714948).length < 2 ^ (prefixWord ++ tailWord_2714948).sum := by decide
  have hdescent : baseEnd_2714948 < baseStart_2714948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714976 : List Nat := [2, 1, 1, 3, 4, 2, 1, 2, 6]
def baseStart_2714976 : Nat := 118140960795 + 2714976 * 2 ^ 59
def prefixEnd_2714976 : Nat := 4983230072969 + 3 ^ 40 * 2714976 * 2
def baseEnd_2714976 : Nat := 309797256315838861692013

theorem tailTrace_2714976 : CollatzResearch.WordTrace tailWord_2714976 prefixEnd_2714976 309797256315838861692013 := by
  unfold tailWord_2714976
  simp only [CollatzResearch.WordTrace]
  refine ⟨49511654906056553915190391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66015539874742071886920521 49511654906056553915190391)
  ·
    refine ⟨74267482359084830872785587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49511654906056553915190391 74267482359084830872785587)
    ·
      refine ⟨111401223538627246309178381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74267482359084830872785587 111401223538627246309178381)
      ·
        refine ⟨41775458826985217365941893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111401223538627246309178381 41775458826985217365941893)
        ·
          refine ⟨7832898530059728256114105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41775458826985217365941893 7832898530059728256114105)
          ·
            refine ⟨5874673897544796192085579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7832898530059728256114105 5874673897544796192085579)
            ·
              refine ⟨8812010846317194288128369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874673897544796192085579 8812010846317194288128369)
              ·
                refine ⟨6609008134737895716096277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8812010846317194288128369 6609008134737895716096277)
                ·
                  refine ⟨309797256315838861692013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6609008134737895716096277 309797256315838861692013)
                  ·
                    rfl

theorem cell22_2714976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 6].length) (baseStart_2714976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714976 prefixEnd_2714976 := by exact prefixLift 2714976
  have htrace : WordTrace (prefixWord ++ tailWord_2714976) baseStart_2714976 baseEnd_2714976 := by
    simpa [prefixWord, tailWord_2714976, baseEnd_2714976] using wordTrace_append hprefix tailTrace_2714976
  have hstable : (prefixWord ++ tailWord_2714976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714976).length < 2 ^ (prefixWord ++ tailWord_2714976).sum := by decide
  have hdescent : baseEnd_2714976 < baseStart_2714976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714978 : List Nat := [3, 3, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2714978 : Nat := 118140960795 + 2714978 * 2 ^ 59
def prefixEnd_2714978 : Nat := 4983230072969 + 3 ^ 40 * 2714978 * 2
def baseEnd_2714978 : Nat := 929392453588389246526033

theorem tailTrace_2714978 : CollatzResearch.WordTrace tailWord_2714978 prefixEnd_2714978 929392453588389246526033 := by
  unfold tailWord_2714978
  simp only [CollatzResearch.WordTrace]
  refine ⟨24755845689526465542988397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66015588505403908114635725 24755845689526465542988397)
  ·
    refine ⟨9283442133572424578620649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24755845689526465542988397 9283442133572424578620649)
    ·
      refine ⟨6962581600179318433965487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9283442133572424578620649 6962581600179318433965487)
      ·
        refine ⟨10443872400268977650948231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6962581600179318433965487 10443872400268977650948231)
        ·
          refine ⟨15665808600403466476422347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10443872400268977650948231 15665808600403466476422347)
          ·
            refine ⟨23498712900605199714633521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15665808600403466476422347 23498712900605199714633521)
            ·
              refine ⟨17624034675453899785975141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23498712900605199714633521 17624034675453899785975141)
              ·
                refine ⟨3304506501647606209870339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17624034675453899785975141 3304506501647606209870339)
                ·
                  refine ⟨4956759752471409314805509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304506501647606209870339 4956759752471409314805509)
                  ·
                    refine ⟨929392453588389246526033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956759752471409314805509 929392453588389246526033)
                    ·
                      rfl

theorem cell22_2714978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2714978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714978 prefixEnd_2714978 := by exact prefixLift 2714978
  have htrace : WordTrace (prefixWord ++ tailWord_2714978) baseStart_2714978 baseEnd_2714978 := by
    simpa [prefixWord, tailWord_2714978, baseEnd_2714978] using wordTrace_append hprefix tailTrace_2714978
  have hstable : (prefixWord ++ tailWord_2714978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714978).length < 2 ^ (prefixWord ++ tailWord_2714978).sum := by decide
  have hdescent : baseEnd_2714978 < baseStart_2714978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2714991 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 4, 3]
def baseStart_2714991 : Nat := 118140960795 + 2714991 * 2 ^ 59
def prefixEnd_2714991 : Nat := 4983230072969 + 3 ^ 40 * 2714991 * 2
def baseEnd_2714991 : Nat := 929396903754061545950993

theorem tailTrace_2714991 : CollatzResearch.WordTrace tailWord_2714991 prefixEnd_2714991 929396903754061545950993 := by
  unfold tailWord_2714991
  simp only [CollatzResearch.WordTrace]
  refine ⟨99023856907058765392176827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66015904604705843594784551 99023856907058765392176827)
  ·
    refine ⟨148535785360588148088265241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99023856907058765392176827 148535785360588148088265241)
    ·
      refine ⟨111401839020441111066198931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148535785360588148088265241 111401839020441111066198931)
      ·
        refine ⟨167102758530661666599298397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111401839020441111066198931 167102758530661666599298397)
        ·
          refine ⟨62663534448998124974736899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167102758530661666599298397 62663534448998124974736899)
          ·
            refine ⟨93995301673497187462105349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62663534448998124974736899 93995301673497187462105349)
            ·
              refine ⟨17624119063780722649144753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93995301673497187462105349 17624119063780722649144753)
              ·
                refine ⟨13218089297835541986858565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17624119063780722649144753 13218089297835541986858565)
                ·
                  refine ⟨2478391743344164122535981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13218089297835541986858565 2478391743344164122535981)
                  ·
                    refine ⟨929396903754061545950993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2478391743344164122535981 929396903754061545950993)
                    ·
                      rfl

theorem cell22_2714991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 4, 3].length) (baseStart_2714991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2714991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2714991 prefixEnd_2714991 := by exact prefixLift 2714991
  have htrace : WordTrace (prefixWord ++ tailWord_2714991) baseStart_2714991 baseEnd_2714991 := by
    simpa [prefixWord, tailWord_2714991, baseEnd_2714991] using wordTrace_append hprefix tailTrace_2714991
  have hstable : (prefixWord ++ tailWord_2714991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2714991).length < 2 ^ (prefixWord ++ tailWord_2714991).sum := by decide
  have hdescent : baseEnd_2714991 < baseStart_2714991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2714991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715004 : List Nat := [2, 2, 2, 1, 1, 1, 13]
def baseStart_2715004 : Nat := 118140960795 + 2715004 * 2 ^ 59
def prefixEnd_2715004 : Nat := 4983230072969 + 3 ^ 40 * 2715004 * 2
def baseEnd_2715004 : Nat := 34422272367397549828739

theorem tailTrace_2715004 : CollatzResearch.WordTrace tailWord_2715004 prefixEnd_2715004 34422272367397549828739 := by
  unfold tailWord_2715004
  simp only [CollatzResearch.WordTrace]
  refine ⟨49512165528005834306200033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66016220704007779074933377 49512165528005834306200033)
  ·
    refine ⟨37134124146004375729650025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49512165528005834306200033 37134124146004375729650025)
    ·
      refine ⟨27850593109503281797237519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37134124146004375729650025 27850593109503281797237519)
      ·
        refine ⟨41775889664254922695856279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27850593109503281797237519 41775889664254922695856279)
        ·
          refine ⟨62663834496382384043784419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41775889664254922695856279 62663834496382384043784419)
          ·
            refine ⟨93995751744573576065676629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62663834496382384043784419 93995751744573576065676629)
            ·
              refine ⟨34422272367397549828739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 93995751744573576065676629 34422272367397549828739)
              ·
                rfl

theorem cell22_2715004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 13].length) (baseStart_2715004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715004 prefixEnd_2715004 := by exact prefixLift 2715004
  have htrace : WordTrace (prefixWord ++ tailWord_2715004) baseStart_2715004 baseEnd_2715004 := by
    simpa [prefixWord, tailWord_2715004, baseEnd_2715004] using wordTrace_append hprefix tailTrace_2715004
  have hstable : (prefixWord ++ tailWord_2715004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715004).length < 2 ^ (prefixWord ++ tailWord_2715004).sum := by decide
  have hdescent : baseEnd_2715004 < baseStart_2715004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715010 : List Nat := [3, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2715010 : Nat := 118140960795 + 2715010 * 2 ^ 59
def prefixEnd_2715010 : Nat := 4983230072969 + 3 ^ 40 * 2715010 * 2
def baseEnd_2715010 : Nat := 309801135947450609908645

theorem tailTrace_2715010 : CollatzResearch.WordTrace tailWord_2715010 prefixEnd_2715010 309801135947450609908645 := by
  unfold tailWord_2715010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24756137473497482909279621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66016366595993287758078989 24756137473497482909279621)
  ·
    refine ⟨4641775776280778045489929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24756137473497482909279621 4641775776280778045489929)
    ·
      refine ⟨3481331832210583534117447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4641775776280778045489929 3481331832210583534117447)
      ·
        refine ⟨5221997748315875301176171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481331832210583534117447 5221997748315875301176171)
        ·
          refine ⟨7832996622473812951764257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221997748315875301176171 7832996622473812951764257)
          ·
            refine ⟨5874747466855359713823193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7832996622473812951764257 5874747466855359713823193)
            ·
              refine ⟨4406060600141519785367395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5874747466855359713823193 4406060600141519785367395)
              ·
                refine ⟨6609090900212279678051093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406060600141519785367395 6609090900212279678051093)
                ·
                  refine ⟨309801135947450609908645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6609090900212279678051093 309801135947450609908645)
                  ·
                    rfl

theorem cell22_2715010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2715010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715010 prefixEnd_2715010 := by exact prefixLift 2715010
  have htrace : WordTrace (prefixWord ++ tailWord_2715010) baseStart_2715010 baseEnd_2715010 := by
    simpa [prefixWord, tailWord_2715010, baseEnd_2715010] using wordTrace_append hprefix tailTrace_2715010
  have hstable : (prefixWord ++ tailWord_2715010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715010).length < 2 ^ (prefixWord ++ tailWord_2715010).sum := by decide
  have hdescent : baseEnd_2715010 < baseStart_2715010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715083 : List Nat := [1, 1, 1, 1, 3, 3, 6, 1, 5]
def baseStart_2715083 : Nat := 118140960795 + 2715083 * 2 ^ 59
def prefixEnd_2715083 : Nat := 4983230072969 + 3 ^ 40 * 2715083 * 2
def baseEnd_2715083 : Nat := 309809465744734657550237

theorem tailTrace_2715083 : CollatzResearch.WordTrace tailWord_2715083 prefixEnd_2715083 309809465744734657550237 := by
  unfold tailWord_2715083
  simp only [CollatzResearch.WordTrace]
  refine ⟨99027212422725465104525903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66018141615150310069683935 99027212422725465104525903)
  ·
    refine ⟨148540818634088197656788855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99027212422725465104525903 148540818634088197656788855)
    ·
      refine ⟨222811227951132296485183283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148540818634088197656788855 222811227951132296485183283)
      ·
        refine ⟨334216841926698444727774925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222811227951132296485183283 334216841926698444727774925)
        ·
          refine ⟨125331315722511916772915597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334216841926698444727774925 125331315722511916772915597)
          ·
            refine ⟨46999243395941968789843349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125331315722511916772915597 46999243395941968789843349)
            ·
              refine ⟨2203089534184779787023907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 46999243395941968789843349 2203089534184779787023907)
              ·
                refine ⟨3304634301277169680535861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2203089534184779787023907 3304634301277169680535861)
                ·
                  refine ⟨309809465744734657550237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304634301277169680535861 309809465744734657550237)
                  ·
                    rfl

theorem cell22_2715083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 6, 1, 5].length) (baseStart_2715083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715083 prefixEnd_2715083 := by exact prefixLift 2715083
  have htrace : WordTrace (prefixWord ++ tailWord_2715083) baseStart_2715083 baseEnd_2715083 := by
    simpa [prefixWord, tailWord_2715083, baseEnd_2715083] using wordTrace_append hprefix tailTrace_2715083
  have hstable : (prefixWord ++ tailWord_2715083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715083).length < 2 ^ (prefixWord ++ tailWord_2715083).sum := by decide
  have hdescent : baseEnd_2715083 < baseStart_2715083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715141 : List Nat := [1, 3, 1, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2715141 : Nat := 118140960795 + 2715141 * 2 ^ 59
def prefixEnd_2715141 : Nat := 4983230072969 + 3 ^ 40 * 2715141 * 2
def baseEnd_2715141 : Nat := 929448251819511154700533

theorem tailTrace_2715141 : CollatzResearch.WordTrace tailWord_2715141 prefixEnd_2715141 929448251819511154700533 := by
  unfold tailWord_2715141
  simp only [CollatzResearch.WordTrace]
  refine ⟨99029327856515341010137277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66019551904343560673424851 99029327856515341010137277)
  ·
    refine ⟨37135997946193252878801479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99029327856515341010137277 37135997946193252878801479)
    ·
      refine ⟨55703996919289879318202219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37135997946193252878801479 55703996919289879318202219)
      ·
        refine ⟨83555995378934818977303329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55703996919289879318202219 83555995378934818977303329)
        ·
          refine ⟨62666996534201114232977497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83555995378934818977303329 62666996534201114232977497)
          ·
            refine ⟨47000247400650835674733123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62666996534201114232977497 47000247400650835674733123)
            ·
              refine ⟨70500371100976253512099685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47000247400650835674733123 70500371100976253512099685)
              ·
                refine ⟨13218819581433047533518691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70500371100976253512099685 13218819581433047533518691)
                ·
                  refine ⟨19828229372149571300278037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13218819581433047533518691 19828229372149571300278037)
                  ·
                    refine ⟨929448251819511154700533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19828229372149571300278037 929448251819511154700533)
                    ·
                      rfl

theorem cell22_2715141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2715141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715141 prefixEnd_2715141 := by exact prefixLift 2715141
  have htrace : WordTrace (prefixWord ++ tailWord_2715141) baseStart_2715141 baseEnd_2715141 := by
    simpa [prefixWord, tailWord_2715141, baseEnd_2715141] using wordTrace_append hprefix tailTrace_2715141
  have hstable : (prefixWord ++ tailWord_2715141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715141).length < 2 ^ (prefixWord ++ tailWord_2715141).sum := by decide
  have hdescent : baseEnd_2715141 < baseStart_2715141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715143 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 1, 5]
def baseStart_2715143 : Nat := 118140960795 + 2715143 * 2 ^ 59
def prefixEnd_2715143 : Nat := 4983230072969 + 3 ^ 40 * 2715143 * 2
def baseEnd_2715143 : Nat := 929448936460383816150527

theorem tailTrace_2715143 : CollatzResearch.WordTrace tailWord_2715143 prefixEnd_2715143 929448936460383816150527 := by
  unfold tailWord_2715143
  simp only [CollatzResearch.WordTrace]
  refine ⟨99029400802508095351710083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66019600535005396901140055 99029400802508095351710083)
  ·
    refine ⟨148544101203762143027565125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99029400802508095351710083 148544101203762143027565125)
    ·
      refine ⟨27852018975705401817668461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148544101203762143027565125 27852018975705401817668461)
      ·
        refine ⟨10444507115889525681625673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27852018975705401817668461 10444507115889525681625673)
        ·
          refine ⟨7833380336917144261219255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10444507115889525681625673 7833380336917144261219255)
          ·
            refine ⟨11750070505375716391828883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833380336917144261219255 11750070505375716391828883)
            ·
              refine ⟨17625105758063574587743325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750070505375716391828883 17625105758063574587743325)
              ·
                refine ⟨6609414659273840470403747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17625105758063574587743325 6609414659273840470403747)
                ·
                  refine ⟨9914121988910760705605621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609414659273840470403747 9914121988910760705605621)
                  ·
                    refine ⟨929448936460383816150527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9914121988910760705605621 929448936460383816150527)
                    ·
                      rfl

theorem cell22_2715143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_2715143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715143 prefixEnd_2715143 := by exact prefixLift 2715143
  have htrace : WordTrace (prefixWord ++ tailWord_2715143) baseStart_2715143 baseEnd_2715143 := by
    simpa [prefixWord, tailWord_2715143, baseEnd_2715143] using wordTrace_append hprefix tailTrace_2715143
  have hstable : (prefixWord ++ tailWord_2715143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715143).length < 2 ^ (prefixWord ++ tailWord_2715143).sum := by decide
  have hdescent : baseEnd_2715143 < baseStart_2715143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715207 : List Nat := [1, 1, 4, 1, 6, 1, 2, 6]
def baseStart_2715207 : Nat := 118140960795 + 2715207 * 2 ^ 59
def prefixEnd_2715207 : Nat := 4983230072969 + 3 ^ 40 * 2715207 * 2
def baseEnd_2715207 : Nat := 103274538329812109172259

theorem tailTrace_2715207 : CollatzResearch.WordTrace tailWord_2715207 prefixEnd_2715207 103274538329812109172259 := by
  unfold tailWord_2715207
  simp only [CollatzResearch.WordTrace]
  refine ⟨99031735074276234282039875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66021156716184156188026583 99031735074276234282039875)
  ·
    refine ⟨148547602611414351423059813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99031735074276234282039875 148547602611414351423059813)
    ·
      refine ⟨27852675489640190891823715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148547602611414351423059813 27852675489640190891823715)
      ·
        refine ⟨41779013234460286337735573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27852675489640190891823715 41779013234460286337735573)
        ·
          refine ⟨1958391245365325922081355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41779013234460286337735573 1958391245365325922081355)
          ·
            refine ⟨2937586868047988883122033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958391245365325922081355 2937586868047988883122033)
            ·
              refine ⟨2203190151035991662341525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2937586868047988883122033 2203190151035991662341525)
              ·
                refine ⟨103274538329812109172259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2203190151035991662341525 103274538329812109172259)
                ·
                  rfl

theorem cell22_2715207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 2, 6].length) (baseStart_2715207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715207 prefixEnd_2715207 := by exact prefixLift 2715207
  have htrace : WordTrace (prefixWord ++ tailWord_2715207) baseStart_2715207 baseEnd_2715207 := by
    simpa [prefixWord, tailWord_2715207, baseEnd_2715207] using wordTrace_append hprefix tailTrace_2715207
  have hstable : (prefixWord ++ tailWord_2715207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715207).length < 2 ^ (prefixWord ++ tailWord_2715207).sum := by decide
  have hdescent : baseEnd_2715207 < baseStart_2715207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715218 : List Nat := [3, 2, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2715218 : Nat := 118140960795 + 2715218 * 2 ^ 59
def prefixEnd_2715218 : Nat := 4983230072969 + 3 ^ 40 * 2715218 * 2
def baseEnd_2715218 : Nat := 309824870164369540175099

theorem tailTrace_2715218 : CollatzResearch.WordTrace tailWord_2715218 prefixEnd_2715218 309824870164369540175099 := by
  unfold tailWord_2715218
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758034069309095790172577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66021424184824255440460205 24758034069309095790172577)
  ·
    refine ⟨18568525551981821842629433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24758034069309095790172577 18568525551981821842629433)
    ·
      refine ⟨13926394163986366381972075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18568525551981821842629433 13926394163986366381972075)
      ·
        refine ⟨20889591245979549572958113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13926394163986366381972075 20889591245979549572958113)
        ·
          refine ⟨15667193434484662179718585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20889591245979549572958113 15667193434484662179718585)
          ·
            refine ⟨11750395075863496634788939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15667193434484662179718585 11750395075863496634788939)
            ·
              refine ⟨17625592613795244952183409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750395075863496634788939 17625592613795244952183409)
              ·
                refine ⟨13219194460346433714137557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17625592613795244952183409 13219194460346433714137557)
                ·
                  refine ⟨309824870164369540175099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13219194460346433714137557 309824870164369540175099)
                  ·
                    rfl

theorem cell22_2715218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2715218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715218 prefixEnd_2715218 := by exact prefixLift 2715218
  have htrace : WordTrace (prefixWord ++ tailWord_2715218) baseStart_2715218 baseEnd_2715218 := by
    simpa [prefixWord, tailWord_2715218, baseEnd_2715218] using wordTrace_append hprefix tailTrace_2715218
  have hstable : (prefixWord ++ tailWord_2715218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715218).length < 2 ^ (prefixWord ++ tailWord_2715218).sum := by decide
  have hdescent : baseEnd_2715218 < baseStart_2715218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715265 : List Nat := [1, 2, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_2715265 : Nat := 118140960795 + 2715265 * 2 ^ 59
def prefixEnd_2715265 : Nat := 4983230072969 + 3 ^ 40 * 2715265 * 2
def baseEnd_2715265 : Nat := 929490699553616164600153

theorem tailTrace_2715265 : CollatzResearch.WordTrace tailWord_2715265 prefixEnd_2715265 929490699553616164600153 := by
  unfold tailWord_2715265
  simp only [CollatzResearch.WordTrace]
  refine ⟨99033850508066110187651249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66022567005377406791767499 99033850508066110187651249)
  ·
    refine ⟨74275387881049582640738437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99033850508066110187651249 74275387881049582640738437)
    ·
      refine ⟨13926635227696796745138457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74275387881049582640738437 13926635227696796745138457)
      ·
        refine ⟨10444976420772597558853843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13926635227696796745138457 10444976420772597558853843)
        ·
          refine ⟨15667464631158896338280765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10444976420772597558853843 15667464631158896338280765)
          ·
            refine ⟨5875299236684586126855287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15667464631158896338280765 5875299236684586126855287)
            ·
              refine ⟨8812948855026879190282931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875299236684586126855287 8812948855026879190282931)
              ·
                refine ⟨13219423282540318785424397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8812948855026879190282931 13219423282540318785424397)
                ·
                  refine ⟨4957283730952619544534149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13219423282540318785424397 4957283730952619544534149)
                  ·
                    refine ⟨929490699553616164600153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4957283730952619544534149 929490699553616164600153)
                    ·
                      rfl

theorem cell22_2715265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_2715265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715265 prefixEnd_2715265 := by exact prefixLift 2715265
  have htrace : WordTrace (prefixWord ++ tailWord_2715265) baseStart_2715265 baseEnd_2715265 := by
    simpa [prefixWord, tailWord_2715265, baseEnd_2715265] using wordTrace_append hprefix tailTrace_2715265
  have hstable : (prefixWord ++ tailWord_2715265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715265).length < 2 ^ (prefixWord ++ tailWord_2715265).sum := by decide
  have hdescent : baseEnd_2715265 < baseStart_2715265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715293 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 3, 6]
def baseStart_2715293 : Nat := 118140960795 + 2715293 * 2 ^ 59
def prefixEnd_2715293 : Nat := 4983230072969 + 3 ^ 40 * 2715293 * 2
def baseEnd_2715293 : Nat := 929500284525833424900067

theorem tailTrace_2715293 : CollatzResearch.WordTrace tailWord_2715293 prefixEnd_2715293 929500284525833424900067 := by
  unfold tailWord_2715293
  simp only [CollatzResearch.WordTrace]
  refine ⟨99034871751964670969670533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66023247834643113979780355 99034871751964670969670533)
  ·
    refine ⟨18569038453493375806813225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99034871751964670969670533 18569038453493375806813225)
    ·
      refine ⟨13926778840120031855109919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18569038453493375806813225 13926778840120031855109919)
      ·
        refine ⟨20890168260180047782664879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13926778840120031855109919 20890168260180047782664879)
        ·
          refine ⟨31335252390270071673997319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20890168260180047782664879 31335252390270071673997319)
          ·
            refine ⟨47002878585405107510995979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31335252390270071673997319 47002878585405107510995979)
            ·
              refine ⟨70504317878107661266493969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47002878585405107510995979 70504317878107661266493969)
              ·
                refine ⟨52878238408580745949870477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70504317878107661266493969 52878238408580745949870477)
                ·
                  refine ⟨19829339403217779731201429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52878238408580745949870477 19829339403217779731201429)
                  ·
                    refine ⟨929500284525833424900067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19829339403217779731201429 929500284525833424900067)
                    ·
                      rfl

theorem cell22_2715293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_2715293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715293 prefixEnd_2715293 := by exact prefixLift 2715293
  have htrace : WordTrace (prefixWord ++ tailWord_2715293) baseStart_2715293 baseEnd_2715293 := by
    simpa [prefixWord, tailWord_2715293, baseEnd_2715293] using wordTrace_append hprefix tailTrace_2715293
  have hstable : (prefixWord ++ tailWord_2715293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715293).length < 2 ^ (prefixWord ++ tailWord_2715293).sum := by decide
  have hdescent : baseEnd_2715293 < baseStart_2715293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715297 : List Nat := [1, 2, 3, 3, 2, 2, 1, 4, 4]
def baseStart_2715297 : Nat := 118140960795 + 2715297 * 2 ^ 59
def prefixEnd_2715297 : Nat := 4983230072969 + 3 ^ 40 * 2715297 * 2
def baseEnd_2715297 : Nat := 309833884602526249266685

theorem tailTrace_2715297 : CollatzResearch.WordTrace tailWord_2715297 prefixEnd_2715297 309833884602526249266685 := by
  unfold tailWord_2715297
  simp only [CollatzResearch.WordTrace]
  refine ⟨99035017643950179652816145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66023345095966786435210763 99035017643950179652816145)
  ·
    refine ⟨74276263232962634739612109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99035017643950179652816145 74276263232962634739612109)
    ·
      refine ⟨27853598712360988027354541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74276263232962634739612109 27853598712360988027354541)
      ·
        refine ⟨10445099517135370510257953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27853598712360988027354541 10445099517135370510257953)
        ·
          refine ⟨7833824637851527882693465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10445099517135370510257953 7833824637851527882693465)
          ·
            refine ⟨5875368478388645912020099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7833824637851527882693465 5875368478388645912020099)
            ·
              refine ⟨8813052717582968868030149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5875368478388645912020099 8813052717582968868030149)
              ·
                refine ⟨1652447384546806662755653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8813052717582968868030149 1652447384546806662755653)
                ·
                  refine ⟨309833884602526249266685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1652447384546806662755653 309833884602526249266685)
                  ·
                    rfl

theorem cell22_2715297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 4, 4].length) (baseStart_2715297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715297 prefixEnd_2715297 := by exact prefixLift 2715297
  have htrace : WordTrace (prefixWord ++ tailWord_2715297) baseStart_2715297 baseEnd_2715297 := by
    simpa [prefixWord, tailWord_2715297, baseEnd_2715297] using wordTrace_append hprefix tailTrace_2715297
  have hstable : (prefixWord ++ tailWord_2715297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715297).length < 2 ^ (prefixWord ++ tailWord_2715297).sum := by decide
  have hdescent : baseEnd_2715297 < baseStart_2715297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715325 : List Nat := [1, 4, 1, 2, 1, 2, 5, 6]
def baseStart_2715325 : Nat := 118140960795 + 2715325 * 2 ^ 59
def prefixEnd_2715325 : Nat := 4983230072969 + 3 ^ 40 * 2715325 * 2
def baseEnd_2715325 : Nat := 103279026531088445344441

theorem tailTrace_2715325 : CollatzResearch.WordTrace tailWord_2715325 prefixEnd_2715325 103279026531088445344441 := by
  unfold tailWord_2715325
  simp only [CollatzResearch.WordTrace]
  refine ⟨99036038887848740434835429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66024025925232493623223619 99036038887848740434835429)
  ·
    refine ⟨18569257291471638831531643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99036038887848740434835429 18569257291471638831531643)
    ·
      refine ⟨27853885937207458247297465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18569257291471638831531643 27853885937207458247297465)
      ·
        refine ⟨20890414452905593685473099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27853885937207458247297465 20890414452905593685473099)
        ·
          refine ⟨31335621679358390528209649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20890414452905593685473099 31335621679358390528209649)
          ·
            refine ⟨23501716259518792896157237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31335621679358390528209649 23501716259518792896157237)
            ·
              refine ⟨2203285899329886834014741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23501716259518792896157237 2203285899329886834014741)
              ·
                refine ⟨103279026531088445344441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2203285899329886834014741 103279026531088445344441)
                ·
                  rfl

theorem cell22_2715325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 6].length) (baseStart_2715325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715325 prefixEnd_2715325 := by exact prefixLift 2715325
  have htrace : WordTrace (prefixWord ++ tailWord_2715325) baseStart_2715325 baseEnd_2715325 := by
    simpa [prefixWord, tailWord_2715325, baseEnd_2715325] using wordTrace_append hprefix tailTrace_2715325
  have hstable : (prefixWord ++ tailWord_2715325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715325).length < 2 ^ (prefixWord ++ tailWord_2715325).sum := by decide
  have hdescent : baseEnd_2715325 < baseStart_2715325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715370 : List Nat := [3, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_2715370 : Nat := 118140960795 + 2715370 * 2 ^ 59
def prefixEnd_2715370 : Nat := 4983230072969 + 3 ^ 40 * 2715370 * 2
def baseEnd_2715370 : Nat := 309842214399810296908277

theorem tailTrace_2715370 : CollatzResearch.WordTrace tailWord_2715370 prefixEnd_2715370 309842214399810296908277 := by
  unfold tailWord_2715370
  simp only [CollatzResearch.WordTrace]
  refine ⟨24759420043171428280055891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66025120115123808746815709 24759420043171428280055891)
  ·
    refine ⟨37139130064757142420083837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24759420043171428280055891 37139130064757142420083837)
    ·
      refine ⟨13927173774283928407531439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37139130064757142420083837 13927173774283928407531439)
      ·
        refine ⟨20890760661425892611297159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13927173774283928407531439 20890760661425892611297159)
        ·
          refine ⟨31336140992138838916945739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20890760661425892611297159 31336140992138838916945739)
          ·
            refine ⟨47004211488208258375418609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31336140992138838916945739 47004211488208258375418609)
            ·
              refine ⟨35253158616156193781563957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47004211488208258375418609 35253158616156193781563957)
              ·
                refine ⟨3304983620264643167021621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35253158616156193781563957 3304983620264643167021621)
                ·
                  refine ⟨309842214399810296908277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304983620264643167021621 309842214399810296908277)
                  ·
                    rfl

theorem cell22_2715370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_2715370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715370 prefixEnd_2715370 := by exact prefixLift 2715370
  have htrace : WordTrace (prefixWord ++ tailWord_2715370) baseStart_2715370 baseEnd_2715370 := by
    simpa [prefixWord, tailWord_2715370, baseEnd_2715370] using wordTrace_append hprefix tailTrace_2715370
  have hstable : (prefixWord ++ tailWord_2715370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715370).length < 2 ^ (prefixWord ++ tailWord_2715370).sum := by decide
  have hdescent : baseEnd_2715370 < baseStart_2715370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715460 : List Nat := [2, 3, 4, 13]
def baseStart_2715460 : Nat := 118140960795 + 2715460 * 2 ^ 59
def prefixEnd_2715460 : Nat := 4983230072969 + 3 ^ 40 * 2715460 * 2
def baseEnd_2715460 : Nat := 1275113102933745755795

theorem tailTrace_2715460 : CollatzResearch.WordTrace tailWord_2715460 prefixEnd_2715460 1275113102933745755795 := by
  unfold tailWord_2715460
  simp only [CollatzResearch.WordTrace]
  refine ⟨49520481371179829245499917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66027308494906438993999889 49520481371179829245499917)
  ·
    refine ⟨18570180514192435967062469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49520481371179829245499917 18570180514192435967062469)
    ·
      refine ⟨3481908846411081743824213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18570180514192435967062469 3481908846411081743824213)
      ·
        refine ⟨1275113102933745755795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 3481908846411081743824213 1275113102933745755795)
        ·
          rfl

theorem cell22_2715460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 13].length) (baseStart_2715460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715460 prefixEnd_2715460 := by exact prefixLift 2715460
  have htrace : WordTrace (prefixWord ++ tailWord_2715460) baseStart_2715460 baseEnd_2715460 := by
    simpa [prefixWord, tailWord_2715460, baseEnd_2715460] using wordTrace_append hprefix tailTrace_2715460
  have hstable : (prefixWord ++ tailWord_2715460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715460).length < 2 ^ (prefixWord ++ tailWord_2715460).sum := by decide
  have hdescent : baseEnd_2715460 < baseStart_2715460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715464 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 2, 3]
def baseStart_2715464 : Nat := 118140960795 + 2715464 * 2 ^ 59
def prefixEnd_2715464 : Nat := 4983230072969 + 3 ^ 40 * 2715464 * 2
def baseEnd_2715464 : Nat := 929558821320445978874543

theorem tailTrace_2715464 : CollatzResearch.WordTrace tailWord_2715464 prefixEnd_2715464 929558821320445978874543 := by
  unfold tailWord_2715464
  simp only [CollatzResearch.WordTrace]
  refine ⟨49520554317172583587072723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66027405756230111449430297 49520554317172583587072723)
  ·
    refine ⟨74280831475758875380609085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49520554317172583587072723 74280831475758875380609085)
    ·
      refine ⟨27855311803409578267728407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74280831475758875380609085 27855311803409578267728407)
      ·
        refine ⟨41782967705114367401592611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27855311803409578267728407 41782967705114367401592611)
        ·
          refine ⟨62674451557671551102388917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41782967705114367401592611 62674451557671551102388917)
          ·
            refine ⟨5875729833531707915848961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62674451557671551102388917 5875729833531707915848961)
            ·
              refine ⟨4406797375148780936886721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5875729833531707915848961 4406797375148780936886721)
              ·
                refine ⟨3305098031361585702665041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4406797375148780936886721 3305098031361585702665041)
                ·
                  refine ⟨2478823523521189276998781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305098031361585702665041 2478823523521189276998781)
                  ·
                    refine ⟨929558821320445978874543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2478823523521189276998781 929558821320445978874543)
                    ·
                      rfl

theorem cell22_2715464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 3].length) (baseStart_2715464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715464 prefixEnd_2715464 := by exact prefixLift 2715464
  have htrace : WordTrace (prefixWord ++ tailWord_2715464) baseStart_2715464 baseEnd_2715464 := by
    simpa [prefixWord, tailWord_2715464, baseEnd_2715464] using wordTrace_append hprefix tailTrace_2715464
  have hstable : (prefixWord ++ tailWord_2715464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715464).length < 2 ^ (prefixWord ++ tailWord_2715464).sum := by decide
  have hdescent : baseEnd_2715464 < baseStart_2715464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715477 : List Nat := [1, 3, 2, 2, 2, 4, 1, 7]
def baseStart_2715477 : Nat := 118140960795 + 2715477 * 2 ^ 59
def prefixEnd_2715477 : Nat := 4983230072969 + 3 ^ 40 * 2715477 * 2
def baseEnd_2715477 : Nat := 103284807942902030922167

theorem tailTrace_2715477 : CollatzResearch.WordTrace tailWord_2715477 prefixEnd_2715477 103284807942902030922167 := by
  unfold tailWord_2715477
  simp only [CollatzResearch.WordTrace]
  refine ⟨99041582783298070394368685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66027721855532046929579123 99041582783298070394368685)
  ·
    refine ⟨37140593543736776397888257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99041582783298070394368685 37140593543736776397888257)
    ·
      refine ⟨27855445157802582298416193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37140593543736776397888257 27855445157802582298416193)
      ·
        refine ⟨20891583868351936723812145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27855445157802582298416193 20891583868351936723812145)
        ·
          refine ⟨15668687901263952542859109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20891583868351936723812145 15668687901263952542859109)
          ·
            refine ⟨2937878981486991101786083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15668687901263952542859109 2937878981486991101786083)
            ·
              refine ⟨4406818472230486652679125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937878981486991101786083 4406818472230486652679125)
              ·
                refine ⟨103284807942902030922167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4406818472230486652679125 103284807942902030922167)
                ·
                  rfl

theorem cell22_2715477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 7].length) (baseStart_2715477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715477 prefixEnd_2715477 := by exact prefixLift 2715477
  have htrace : WordTrace (prefixWord ++ tailWord_2715477) baseStart_2715477 baseEnd_2715477 := by
    simpa [prefixWord, tailWord_2715477, baseEnd_2715477] using wordTrace_append hprefix tailTrace_2715477
  have hstable : (prefixWord ++ tailWord_2715477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715477).length < 2 ^ (prefixWord ++ tailWord_2715477).sum := by decide
  have hdescent : baseEnd_2715477 < baseStart_2715477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715505 : List Nat := [1, 2, 2, 2, 1, 3, 2, 2, 7]
def baseStart_2715505 : Nat := 118140960795 + 2715505 * 2 ^ 59
def prefixEnd_2715505 : Nat := 4983230072969 + 3 ^ 40 * 2715505 * 2
def baseEnd_2715505 : Nat := 309857618819445179533139

theorem tailTrace_2715505 : CollatzResearch.WordTrace tailWord_2715505 prefixEnd_2715505 309857618819445179533139 := by
  unfold tailWord_2715505
  simp only [CollatzResearch.WordTrace]
  refine ⟨99042604027196631176387969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66028402684797754117591979 99042604027196631176387969)
  ·
    refine ⟨74281953020397473382290977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99042604027196631176387969 74281953020397473382290977)
    ·
      refine ⟨55711464765298105036718233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74281953020397473382290977 55711464765298105036718233)
      ·
        refine ⟨41783598573973578777538675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55711464765298105036718233 41783598573973578777538675)
        ·
          refine ⟨62675397860960368166308013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41783598573973578777538675 62675397860960368166308013)
          ·
            refine ⟨23503274197860138062365505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62675397860960368166308013 23503274197860138062365505)
            ·
              refine ⟨17627455648395103546774129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23503274197860138062365505 17627455648395103546774129)
              ·
                refine ⟨13220591736296327660080597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17627455648395103546774129 13220591736296327660080597)
                ·
                  refine ⟨309857618819445179533139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13220591736296327660080597 309857618819445179533139)
                  ·
                    rfl

theorem cell22_2715505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_2715505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715505 prefixEnd_2715505 := by exact prefixLift 2715505
  have htrace : WordTrace (prefixWord ++ tailWord_2715505) baseStart_2715505 baseEnd_2715505 := by
    simpa [prefixWord, tailWord_2715505, baseEnd_2715505] using wordTrace_append hprefix tailTrace_2715505
  have hstable : (prefixWord ++ tailWord_2715505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715505).length < 2 ^ (prefixWord ++ tailWord_2715505).sum := by decide
  have hdescent : baseEnd_2715505 < baseStart_2715505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715520 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_2715520 : Nat := 118140960795 + 2715520 * 2 ^ 59
def prefixEnd_2715520 : Nat := 4983230072969 + 3 ^ 40 * 2715520 * 2
def baseEnd_2715520 : Nat := 929577991264880499474371

theorem tailTrace_2715520 : CollatzResearch.WordTrace tailWord_2715520 prefixEnd_2715520 929577991264880499474371 := by
  unfold tailWord_2715520
  simp only [CollatzResearch.WordTrace]
  refine ⟨49521575561071144369092007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66028767414761525825456009 49521575561071144369092007)
  ·
    refine ⟨74282363341606716553638011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49521575561071144369092007 74282363341606716553638011)
    ·
      refine ⟨111423545012410074830457017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74282363341606716553638011 111423545012410074830457017)
      ·
        refine ⟨83567658759307556122842763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111423545012410074830457017 83567658759307556122842763)
        ·
          refine ⟨125351488138961334184264145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83567658759307556122842763 125351488138961334184264145)
          ·
            refine ⟨94013616104221000638198109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125351488138961334184264145 94013616104221000638198109)
            ·
              refine ⟨35255106039082875239324291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94013616104221000638198109 35255106039082875239324291)
              ·
                refine ⟨52882659058624312858986437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35255106039082875239324291 52882659058624312858986437)
                ·
                  refine ⟨9915498573492058661059957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52882659058624312858986437 9915498573492058661059957)
                  ·
                    refine ⟨929577991264880499474371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9915498573492058661059957 929577991264880499474371)
                    ·
                      rfl

theorem cell22_2715520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_2715520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715520 prefixEnd_2715520 := by exact prefixLift 2715520
  have htrace : WordTrace (prefixWord ++ tailWord_2715520) baseStart_2715520 baseEnd_2715520 := by
    simpa [prefixWord, tailWord_2715520, baseEnd_2715520] using wordTrace_append hprefix tailTrace_2715520
  have hstable : (prefixWord ++ tailWord_2715520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715520).length < 2 ^ (prefixWord ++ tailWord_2715520).sum := by decide
  have hdescent : baseEnd_2715520 < baseStart_2715520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715569 : List Nat := [1, 2, 2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_2715569 : Nat := 118140960795 + 2715569 * 2 ^ 59
def prefixEnd_2715569 : Nat := 4983230072969 + 3 ^ 40 * 2715569 * 2
def baseEnd_2715569 : Nat := 929594764966260704999221

theorem tailTrace_2715569 : CollatzResearch.WordTrace tailWord_2715569 prefixEnd_2715569 929594764966260704999221 := by
  unfold tailWord_2715569
  simp only [CollatzResearch.WordTrace]
  refine ⟨99044938298964770106717761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66029958865976513404478507 99044938298964770106717761)
  ·
    refine ⟨74283703724223577580038321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99044938298964770106717761 74283703724223577580038321)
    ·
      refine ⟨55712777793167683185028741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74283703724223577580038321 55712777793167683185028741)
      ·
        refine ⟨10446145836218940597192889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55712777793167683185028741 10446145836218940597192889)
        ·
          refine ⟨7834609377164205447894667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10446145836218940597192889 7834609377164205447894667)
          ·
            refine ⟨11751914065746308171842001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7834609377164205447894667 11751914065746308171842001)
            ·
              refine ⟨8813935549309731128881501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11751914065746308171842001 8813935549309731128881501)
              ·
                refine ⟨3305225830991149173330563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8813935549309731128881501 3305225830991149173330563)
                ·
                  refine ⟨4957838746486723759995845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305225830991149173330563 4957838746486723759995845)
                  ·
                    refine ⟨929594764966260704999221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4957838746486723759995845 929594764966260704999221)
                    ·
                      rfl

theorem cell22_2715569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_2715569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715569 prefixEnd_2715569 := by exact prefixLift 2715569
  have htrace : WordTrace (prefixWord ++ tailWord_2715569) baseStart_2715569 baseEnd_2715569 := by
    simpa [prefixWord, tailWord_2715569, baseEnd_2715569] using wordTrace_append hprefix tailTrace_2715569
  have hstable : (prefixWord ++ tailWord_2715569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715569).length < 2 ^ (prefixWord ++ tailWord_2715569).sum := by decide
  have hdescent : baseEnd_2715569 < baseStart_2715569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715599 : List Nat := [1, 1, 2, 1, 1, 5, 3, 3, 2, 3]
def baseStart_2715599 : Nat := 118140960795 + 2715599 * 2 ^ 59
def prefixEnd_2715599 : Nat := 4983230072969 + 3 ^ 40 * 2715599 * 2
def baseEnd_2715599 : Nat := 929605034579350626749129

theorem tailTrace_2715599 : CollatzResearch.WordTrace tailWord_2715599 prefixEnd_2715599 929605034579350626749129 := by
  unfold tailWord_2715599
  simp only [CollatzResearch.WordTrace]
  refine ⟨99046032488856085230309851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66030688325904056820206567 99046032488856085230309851)
  ·
    refine ⟨148569048733284127845464777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99046032488856085230309851 148569048733284127845464777)
    ·
      refine ⟨111426786549963095884098583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148569048733284127845464777 111426786549963095884098583)
      ·
        refine ⟨167140179824944643826147875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111426786549963095884098583 167140179824944643826147875)
        ·
          refine ⟨250710269737416965739221813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167140179824944643826147875 250710269737416965739221813)
          ·
            refine ⟨23504087787882840538052045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 250710269737416965739221813 23504087787882840538052045)
            ·
              refine ⟨8814032920456065201769517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23504087787882840538052045 8814032920456065201769517)
              ·
                refine ⟨3305262345171024450663569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8814032920456065201769517 3305262345171024450663569)
                ·
                  refine ⟨2478946758878268337997677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305262345171024450663569 2478946758878268337997677)
                  ·
                    refine ⟨929605034579350626749129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2478946758878268337997677 929605034579350626749129)
                    ·
                      rfl

theorem cell22_2715599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 2, 3].length) (baseStart_2715599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715599 prefixEnd_2715599 := by exact prefixLift 2715599
  have htrace : WordTrace (prefixWord ++ tailWord_2715599) baseStart_2715599 baseEnd_2715599 := by
    simpa [prefixWord, tailWord_2715599, baseEnd_2715599] using wordTrace_append hprefix tailTrace_2715599
  have hstable : (prefixWord ++ tailWord_2715599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715599).length < 2 ^ (prefixWord ++ tailWord_2715599).sum := by decide
  have hdescent : baseEnd_2715599 < baseStart_2715599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715629 : List Nat := [1, 5, 1, 4, 1, 10]
def baseStart_2715629 : Nat := 118140960795 + 2715629 * 2 ^ 59
def prefixEnd_2715629 : Nat := 4983230072969 + 3 ^ 40 * 2715629 * 2
def baseEnd_2715629 : Nat := 11476732150523957388877

theorem tailTrace_2715629 : CollatzResearch.WordTrace tailWord_2715629 prefixEnd_2715629 11476732150523957388877 := by
  unfold tailWord_2715629
  simp only [CollatzResearch.WordTrace]
  refine ⟨99047126678747400353901941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66031417785831600235934627 99047126678747400353901941)
  ·
    refine ⟨9285668126132568783178307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99047126678747400353901941 9285668126132568783178307)
    ·
      refine ⟨13928502189198853174767461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9285668126132568783178307 13928502189198853174767461)
      ·
        refine ⟨2611594160474784970268899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13928502189198853174767461 2611594160474784970268899)
        ·
          refine ⟨3917391240712177455403349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2611594160474784970268899 3917391240712177455403349)
          ·
            refine ⟨11476732150523957388877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3917391240712177455403349 11476732150523957388877)
            ·
              rfl

theorem cell22_2715629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 10].length) (baseStart_2715629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715629 prefixEnd_2715629 := by exact prefixLift 2715629
  have htrace : WordTrace (prefixWord ++ tailWord_2715629) baseStart_2715629 baseEnd_2715629 := by
    simpa [prefixWord, tailWord_2715629, baseEnd_2715629] using wordTrace_append hprefix tailTrace_2715629
  have hstable : (prefixWord ++ tailWord_2715629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715629).length < 2 ^ (prefixWord ++ tailWord_2715629).sum := by decide
  have hdescent : baseEnd_2715629 < baseStart_2715629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715644 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 3, 3]
def baseStart_2715644 : Nat := 118140960795 + 2715644 * 2 ^ 59
def prefixEnd_2715644 : Nat := 4983230072969 + 3 ^ 40 * 2715644 * 2
def baseEnd_2715644 : Nat := 929620438998985509373991

theorem tailTrace_2715644 : CollatzResearch.WordTrace tailWord_2715644 prefixEnd_2715644 929620438998985509373991 := by
  unfold tailWord_2715644
  simp only [CollatzResearch.WordTrace]
  refine ⟨49523836886846528957848993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66031782515795371943798657 49523836886846528957848993)
  ·
    refine ⟨37142877665134896718386745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49523836886846528957848993 37142877665134896718386745)
    ·
      refine ⟨27857158248851172538790059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37142877665134896718386745 27857158248851172538790059)
      ·
        refine ⟨41785737373276758808185089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27857158248851172538790059 41785737373276758808185089)
        ·
          refine ⟨31339303029957569106138817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41785737373276758808185089 31339303029957569106138817)
          ·
            refine ⟨23504477272468176829604113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31339303029957569106138817 23504477272468176829604113)
            ·
              refine ⟨17628357954351132622203085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23504477272468176829604113 17628357954351132622203085)
              ·
                refine ⟨6610634232881674733326157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17628357954351132622203085 6610634232881674733326157)
                ·
                  refine ⟨2478987837330628024997309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6610634232881674733326157 2478987837330628024997309)
                  ·
                    refine ⟨929620438998985509373991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2478987837330628024997309 929620438998985509373991)
                    ·
                      rfl

theorem cell22_2715644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 3].length) (baseStart_2715644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715644 prefixEnd_2715644 := by exact prefixLift 2715644
  have htrace : WordTrace (prefixWord ++ tailWord_2715644) baseStart_2715644 baseEnd_2715644 := by
    simpa [prefixWord, tailWord_2715644, baseEnd_2715644] using wordTrace_append hprefix tailTrace_2715644
  have hstable : (prefixWord ++ tailWord_2715644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715644).length < 2 ^ (prefixWord ++ tailWord_2715644).sum := by decide
  have hdescent : baseEnd_2715644 < baseStart_2715644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715646 : List Nat := [4, 2, 2, 2, 1, 3, 1, 7]
def baseStart_2715646 : Nat := 118140960795 + 2715646 * 2 ^ 59
def prefixEnd_2715646 : Nat := 4983230072969 + 3 ^ 40 * 2715646 * 2
def baseEnd_2715646 : Nat := 103291235959984241202665

theorem tailTrace_2715646 : CollatzResearch.WordTrace tailWord_2715646 prefixEnd_2715646 103291235959984241202665 := by
  unfold tailWord_2715646
  simp only [CollatzResearch.WordTrace]
  refine ⟨12380968339960726532158849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66031831146457208171513861 12380968339960726532158849)
  ·
    refine ⟨9285726254970544899119137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12380968339960726532158849 9285726254970544899119137)
    ·
      refine ⟨6964294691227908674339353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285726254970544899119137 6964294691227908674339353)
      ·
        refine ⟨5223221018420931505754515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6964294691227908674339353 5223221018420931505754515)
        ·
          refine ⟨7834831527631397258631773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223221018420931505754515 7834831527631397258631773)
          ·
            refine ⟨2938061822861773971986915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7834831527631397258631773 2938061822861773971986915)
            ·
              refine ⟨4407092734292660957980373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938061822861773971986915 4407092734292660957980373)
              ·
                refine ⟨103291235959984241202665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4407092734292660957980373 103291235959984241202665)
                ·
                  rfl

theorem cell22_2715646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_2715646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715646 prefixEnd_2715646 := by exact prefixLift 2715646
  have htrace : WordTrace (prefixWord ++ tailWord_2715646) baseStart_2715646 baseEnd_2715646 := by
    simpa [prefixWord, tailWord_2715646, baseEnd_2715646] using wordTrace_append hprefix tailTrace_2715646
  have hstable : (prefixWord ++ tailWord_2715646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715646).length < 2 ^ (prefixWord ++ tailWord_2715646).sum := by decide
  have hdescent : baseEnd_2715646 < baseStart_2715646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715672 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 1, 7]
def baseStart_2715672 : Nat := 118140960795 + 2715672 * 2 ^ 59
def prefixEnd_2715672 : Nat := 4983230072969 + 3 ^ 40 * 2715672 * 2
def baseEnd_2715672 : Nat := 929630023971202769673905

theorem tailTrace_2715672 : CollatzResearch.WordTrace tailWord_2715672 prefixEnd_2715672 929630023971202769673905 := by
  unfold tailWord_2715672
  simp only [CollatzResearch.WordTrace]
  refine ⟨49524347508795809348858635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66032463345061079131811513 49524347508795809348858635)
  ·
    refine ⟨74286521263193714023287953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49524347508795809348858635 74286521263193714023287953)
    ·
      refine ⟨55714890947395285517465965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74286521263193714023287953 55714890947395285517465965)
      ·
        refine ⟨20893084105273232069049737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55714890947395285517465965 20893084105273232069049737)
        ·
          refine ⟨15669813078954924051787303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20893084105273232069049737 15669813078954924051787303)
          ·
            refine ⟨23504719618432386077680955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15669813078954924051787303 23504719618432386077680955)
            ·
              refine ⟨35257079427648579116521433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23504719618432386077680955 35257079427648579116521433)
              ·
                refine ⟨26442809570736434337391075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35257079427648579116521433 26442809570736434337391075)
                ·
                  refine ⟨39664214356104651506086613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26442809570736434337391075 39664214356104651506086613)
                  ·
                    refine ⟨929630023971202769673905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39664214356104651506086613 929630023971202769673905)
                    ·
                      rfl

theorem cell22_2715672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 7].length) (baseStart_2715672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715672 prefixEnd_2715672 := by exact prefixLift 2715672
  have htrace : WordTrace (prefixWord ++ tailWord_2715672) baseStart_2715672 baseEnd_2715672 := by
    simpa [prefixWord, tailWord_2715672, baseEnd_2715672] using wordTrace_append hprefix tailTrace_2715672
  have hstable : (prefixWord ++ tailWord_2715672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715672).length < 2 ^ (prefixWord ++ tailWord_2715672).sum := by decide
  have hdescent : baseEnd_2715672 < baseStart_2715672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715736 : List Nat := [2, 1, 2, 2, 1, 4, 3, 3, 4]
def baseStart_2715736 : Nat := 118140960795 + 2715736 * 2 ^ 59
def prefixEnd_2715736 : Nat := 4983230072969 + 3 ^ 40 * 2715736 * 2
def baseEnd_2715736 : Nat := 309883977493042645357903

theorem tailTrace_2715736 : CollatzResearch.WordTrace tailWord_2715736 prefixEnd_2715736 309883977493042645357903 := by
  unfold tailWord_2715736
  simp only [CollatzResearch.WordTrace]
  refine ⟨49525514644679878814023531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66034019526239838418698041 49525514644679878814023531)
  ·
    refine ⟨74288271967019818221035297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49525514644679878814023531 74288271967019818221035297)
    ·
      refine ⟨55716203975264863665776473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74288271967019818221035297 55716203975264863665776473)
      ·
        refine ⟨41787152981448647749332355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55716203975264863665776473 41787152981448647749332355)
        ·
          refine ⟨62680729472172971623998533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41787152981448647749332355 62680729472172971623998533)
          ·
            refine ⟨11752636776032432179499725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62680729472172971623998533 11752636776032432179499725)
            ·
              refine ⟨4407238791012162067312397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11752636776032432179499725 4407238791012162067312397)
              ·
                refine ⟨1652714546629560775242149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4407238791012162067312397 1652714546629560775242149)
                ·
                  refine ⟨309883977493042645357903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1652714546629560775242149 309883977493042645357903)
                  ·
                    rfl

theorem cell22_2715736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_2715736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715736 prefixEnd_2715736 := by exact prefixLift 2715736
  have htrace : WordTrace (prefixWord ++ tailWord_2715736) baseStart_2715736 baseEnd_2715736 := by
    simpa [prefixWord, tailWord_2715736, baseEnd_2715736] using wordTrace_append hprefix tailTrace_2715736
  have hstable : (prefixWord ++ tailWord_2715736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715736).length < 2 ^ (prefixWord ++ tailWord_2715736).sum := by decide
  have hdescent : baseEnd_2715736 < baseStart_2715736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715747 : List Nat := [1, 1, 1, 5, 1, 1, 12]
def baseStart_2715747 : Nat := 118140960795 + 2715747 * 2 ^ 59
def prefixEnd_2715747 : Nat := 4983230072969 + 3 ^ 40 * 2715747 * 2
def baseEnd_2715747 : Nat := 34431692518663984224025

theorem tailTrace_2715747 : CollatzResearch.WordTrace tailWord_2715747 prefixEnd_2715747 34431692518663984224025 := by
  unfold tailWord_2715747
  simp only [CollatzResearch.WordTrace]
  refine ⟨99051430492319906506697495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66034286994879937671131663 99051430492319906506697495)
  ·
    refine ⟨148577145738479859760046243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99051430492319906506697495 148577145738479859760046243)
    ·
      refine ⟨222865718607719789640069365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148577145738479859760046243 222865718607719789640069365)
      ·
        refine ⟨20893661119473730278756503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222865718607719789640069365 20893661119473730278756503)
        ·
          refine ⟨31340491679210595418134755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20893661119473730278756503 31340491679210595418134755)
          ·
            refine ⟨47010737518815893127202133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31340491679210595418134755 47010737518815893127202133)
            ·
              refine ⟨34431692518663984224025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 47010737518815893127202133 34431692518663984224025)
              ·
                rfl

theorem cell22_2715747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 12].length) (baseStart_2715747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715747 prefixEnd_2715747 := by exact prefixLift 2715747
  have htrace : WordTrace (prefixWord ++ tailWord_2715747) baseStart_2715747 baseEnd_2715747 := by
    simpa [prefixWord, tailWord_2715747, baseEnd_2715747] using wordTrace_append hprefix tailTrace_2715747
  have hstable : (prefixWord ++ tailWord_2715747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715747).length < 2 ^ (prefixWord ++ tailWord_2715747).sum := by decide
  have hdescent : baseEnd_2715747 < baseStart_2715747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715749 : List Nat := [1, 3, 1, 3, 2, 2, 1, 1, 4, 4]
def baseStart_2715749 : Nat := 118140960795 + 2715749 * 2 ^ 59
def prefixEnd_2715749 : Nat := 4983230072969 + 3 ^ 40 * 2715749 * 2
def baseEnd_2715749 : Nat := 929656382644800235498669

theorem tailTrace_2715749 : CollatzResearch.WordTrace tailWord_2715749 prefixEnd_2715749 929656382644800235498669 := by
  unfold tailWord_2715749
  simp only [CollatzResearch.WordTrace]
  refine ⟨99051503438312660848270301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66034335625541773898846867 99051503438312660848270301)
  ·
    refine ⟨37144313789367247818101363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99051503438312660848270301 37144313789367247818101363)
    ·
      refine ⟨55716470684050871727152045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37144313789367247818101363 55716470684050871727152045)
      ·
        refine ⟨20893676506519076897682017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55716470684050871727152045 20893676506519076897682017)
        ·
          refine ⟨15670257379889307673261513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20893676506519076897682017 15670257379889307673261513)
          ·
            refine ⟨11752693034916980754946135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15670257379889307673261513 11752693034916980754946135)
            ·
              refine ⟨17629039552375471132419203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11752693034916980754946135 17629039552375471132419203)
              ·
                refine ⟨26443559328563206698628805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17629039552375471132419203 26443559328563206698628805)
                ·
                  refine ⟨4958167374105601255992901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26443559328563206698628805 4958167374105601255992901)
                  ·
                    refine ⟨929656382644800235498669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4958167374105601255992901 929656382644800235498669)
                    ·
                      rfl

theorem cell22_2715749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 4].length) (baseStart_2715749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715749 prefixEnd_2715749 := by exact prefixLift 2715749
  have htrace : WordTrace (prefixWord ++ tailWord_2715749) baseStart_2715749 baseEnd_2715749 := by
    simpa [prefixWord, tailWord_2715749, baseEnd_2715749] using wordTrace_append hprefix tailTrace_2715749
  have hstable : (prefixWord ++ tailWord_2715749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715749).length < 2 ^ (prefixWord ++ tailWord_2715749).sum := by decide
  have hdescent : baseEnd_2715749 < baseStart_2715749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715751 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 2, 3]
def baseStart_2715751 : Nat := 118140960795 + 2715751 * 2 ^ 59
def prefixEnd_2715751 : Nat := 4983230072969 + 3 ^ 40 * 2715751 * 2
def baseEnd_2715751 : Nat := 929657067285672896948663

theorem tailTrace_2715751 : CollatzResearch.WordTrace tailWord_2715751 prefixEnd_2715751 929657067285672896948663 := by
  unfold tailWord_2715751
  simp only [CollatzResearch.WordTrace]
  refine ⟨99051576384305415189843107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66034384256203610126562071 99051576384305415189843107)
  ·
    refine ⟨148577364576458122784764661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99051576384305415189843107 148577364576458122784764661)
    ·
      refine ⟨13929127929042949011071687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148577364576458122784764661 13929127929042949011071687)
      ·
        refine ⟨20893691893564423516607531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13929127929042949011071687 20893691893564423516607531)
        ·
          refine ⟨31340537840346635274911297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20893691893564423516607531 31340537840346635274911297)
          ·
            refine ⟨23505403380259976456183473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31340537840346635274911297 23505403380259976456183473)
            ·
              refine ⟨17629052535194982342137605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23505403380259976456183473 17629052535194982342137605)
              ·
                refine ⟨3305447350349059189150801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17629052535194982342137605 3305447350349059189150801)
                ·
                  refine ⟨2479085512761794391863101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3305447350349059189150801 2479085512761794391863101)
                  ·
                    refine ⟨929657067285672896948663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2479085512761794391863101 929657067285672896948663)
                    ·
                      rfl

theorem cell22_2715751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_2715751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715751 prefixEnd_2715751 := by exact prefixLift 2715751
  have htrace : WordTrace (prefixWord ++ tailWord_2715751) baseStart_2715751 baseEnd_2715751 := by
    simpa [prefixWord, tailWord_2715751, baseEnd_2715751] using wordTrace_append hprefix tailTrace_2715751
  have hstable : (prefixWord ++ tailWord_2715751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715751).length < 2 ^ (prefixWord ++ tailWord_2715751).sum := by decide
  have hdescent : baseEnd_2715751 < baseStart_2715751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715813 : List Nat := [1, 3, 1, 2, 1, 3, 3, 4, 1, 3]
def baseStart_2715813 : Nat := 118140960795 + 2715813 * 2 ^ 59
def prefixEnd_2715813 : Nat := 4983230072969 + 3 ^ 40 * 2715813 * 2
def baseEnd_2715813 : Nat := 929678291152725401898473

theorem tailTrace_2715813 : CollatzResearch.WordTrace tailWord_2715813 prefixEnd_2715813 929678291152725401898473 := by
  unfold tailWord_2715813
  simp only [CollatzResearch.WordTrace]
  refine ⟨99053837710080799778600093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66035891806720533185733395 99053837710080799778600093)
  ·
    refine ⟨37145189141280299916975035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99053837710080799778600093 37145189141280299916975035)
    ·
      refine ⟨55717783711920449875462553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37145189141280299916975035 55717783711920449875462553)
      ·
        refine ⟨41788337783940337406596915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55717783711920449875462553 41788337783940337406596915)
        ·
          refine ⟨62682506675910506109895373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41788337783940337406596915 62682506675910506109895373)
          ·
            refine ⟨23505940003466439791210765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62682506675910506109895373 23505940003466439791210765)
            ·
              refine ⟨8814727501299914921704037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23505940003466439791210765 8814727501299914921704037)
              ·
                refine ⟨1652761406493734047819507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8814727501299914921704037 1652761406493734047819507)
                ·
                  refine ⟨2479142109740601071729261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1652761406493734047819507 2479142109740601071729261)
                  ·
                    refine ⟨929678291152725401898473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2479142109740601071729261 929678291152725401898473)
                    ·
                      rfl

theorem cell22_2715813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 4, 1, 3].length) (baseStart_2715813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715813 prefixEnd_2715813 := by exact prefixLift 2715813
  have htrace : WordTrace (prefixWord ++ tailWord_2715813) baseStart_2715813 baseEnd_2715813 := by
    simpa [prefixWord, tailWord_2715813, baseEnd_2715813] using wordTrace_append hprefix tailTrace_2715813
  have hstable : (prefixWord ++ tailWord_2715813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715813).length < 2 ^ (prefixWord ++ tailWord_2715813).sum := by decide
  have hdescent : baseEnd_2715813 < baseStart_2715813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715884 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 3, 6]
def baseStart_2715884 : Nat := 118140960795 + 2715884 * 2 ^ 59
def prefixEnd_2715884 : Nat := 4983230072969 + 3 ^ 40 * 2715884 * 2
def baseEnd_2715884 : Nat := 929702595903704883373255

theorem tailTrace_2715884 : CollatzResearch.WordTrace tailWord_2715884 prefixEnd_2715884 929702595903704883373255 := by
  unfold tailWord_2715884
  simp only [CollatzResearch.WordTrace]
  refine ⟨49528213646411789452217353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66037618195215719269623137 49528213646411789452217353)
  ·
    refine ⟨37146160234808842089163015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49528213646411789452217353 37146160234808842089163015)
    ·
      refine ⟨55719240352213263133744523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37146160234808842089163015 55719240352213263133744523)
      ·
        refine ⟨83578860528319894700616785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55719240352213263133744523 83578860528319894700616785)
        ·
          refine ⟨62684145396239921025462589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83578860528319894700616785 62684145396239921025462589)
          ·
            refine ⟨23506554523589970384548471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62684145396239921025462589 23506554523589970384548471)
            ·
              refine ⟨35259831785384955576822707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23506554523589970384548471 35259831785384955576822707)
              ·
                refine ⟨52889747678077433365234061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35259831785384955576822707 52889747678077433365234061)
                ·
                  refine ⟨19833655379279037511962773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52889747678077433365234061 19833655379279037511962773)
                  ·
                    refine ⟨929702595903704883373255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19833655379279037511962773 929702595903704883373255)
                    ·
                      rfl

theorem cell22_2715884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 6].length) (baseStart_2715884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715884 prefixEnd_2715884 := by exact prefixLift 2715884
  have htrace : WordTrace (prefixWord ++ tailWord_2715884) baseStart_2715884 baseEnd_2715884 := by
    simpa [prefixWord, tailWord_2715884, baseEnd_2715884] using wordTrace_append hprefix tailTrace_2715884
  have hstable : (prefixWord ++ tailWord_2715884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715884).length < 2 ^ (prefixWord ++ tailWord_2715884).sum := by decide
  have hdescent : baseEnd_2715884 < baseStart_2715884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715933 : List Nat := [1, 4, 2, 3, 2, 1, 2, 7]
def baseStart_2715933 : Nat := 118140960795 + 2715933 * 2 ^ 59
def prefixEnd_2715933 : Nat := 4983230072969 + 3 ^ 40 * 2715933 * 2
def baseEnd_2715933 : Nat := 103302152178342787655345

theorem tailTrace_2715933 : CollatzResearch.WordTrace tailWord_2715933 prefixEnd_2715933 103302152178342787655345 := by
  unfold tailWord_2715933
  simp only [CollatzResearch.WordTrace]
  refine ⟨99058214469646060272968453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66038809646430706848645635 99058214469646060272968453)
  ·
    refine ⟨18573415213058636301181585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99058214469646060272968453 18573415213058636301181585)
    ·
      refine ⟨13930061409793977225886189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18573415213058636301181585 13930061409793977225886189)
      ·
        refine ⟨5223773028672741459707321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13930061409793977225886189 5223773028672741459707321)
        ·
          refine ⟨3917829771504556094780491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5223773028672741459707321 3917829771504556094780491)
          ·
            refine ⟨5876744657256834142170737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917829771504556094780491 5876744657256834142170737)
            ·
              refine ⟨4407558492942625606628053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5876744657256834142170737 4407558492942625606628053)
              ·
                refine ⟨103302152178342787655345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4407558492942625606628053 103302152178342787655345)
                ·
                  rfl

theorem cell22_2715933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 7].length) (baseStart_2715933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715933 prefixEnd_2715933 := by exact prefixLift 2715933
  have htrace : WordTrace (prefixWord ++ tailWord_2715933) baseStart_2715933 baseEnd_2715933 := by
    simpa [prefixWord, tailWord_2715933, baseEnd_2715933] using wordTrace_append hprefix tailTrace_2715933
  have hstable : (prefixWord ++ tailWord_2715933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715933).length < 2 ^ (prefixWord ++ tailWord_2715933).sum := by decide
  have hdescent : baseEnd_2715933 < baseStart_2715933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2715991 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 5, 4]
def baseStart_2715991 : Nat := 118140960795 + 2715991 * 2 ^ 59
def prefixEnd_2715991 : Nat := 4983230072969 + 3 ^ 40 * 2715991 * 2
def baseEnd_2715991 : Nat := 929739224190392270947927

theorem tailTrace_2715991 : CollatzResearch.WordTrace tailWord_2715991 prefixEnd_2715991 929739224190392270947927 := by
  unfold tailWord_2715991
  simp only [CollatzResearch.WordTrace]
  refine ⟨99060329903435936178579827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66040219935623957452386551 99060329903435936178579827)
  ·
    refine ⟨148590494855153904267869741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99060329903435936178579827 148590494855153904267869741)
    ·
      refine ⟨55721435570682714100451153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148590494855153904267869741 55721435570682714100451153)
      ·
        refine ⟨41791076678012035575338365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55721435570682714100451153 41791076678012035575338365)
        ·
          refine ⟨15671653754254513340751887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41791076678012035575338365 15671653754254513340751887)
          ·
            refine ⟨23507480631381770011127831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15671653754254513340751887 23507480631381770011127831)
            ·
              refine ⟨35261220947072655016691747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23507480631381770011127831 35261220947072655016691747)
              ·
                refine ⟨52891831420608982525037621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35261220947072655016691747 52891831420608982525037621)
                ·
                  refine ⟨4958609195682092111722277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52891831420608982525037621 4958609195682092111722277)
                  ·
                    refine ⟨929739224190392270947927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4958609195682092111722277 929739224190392270947927)
                    ·
                      rfl

theorem cell22_2715991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_2715991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2715991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2715991 prefixEnd_2715991 := by exact prefixLift 2715991
  have htrace : WordTrace (prefixWord ++ tailWord_2715991) baseStart_2715991 baseEnd_2715991 := by
    simpa [prefixWord, tailWord_2715991, baseEnd_2715991] using wordTrace_append hprefix tailTrace_2715991
  have hstable : (prefixWord ++ tailWord_2715991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2715991).length < 2 ^ (prefixWord ++ tailWord_2715991).sum := by decide
  have hdescent : baseEnd_2715991 < baseStart_2715991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2715991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716008 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 3, 4]
def baseStart_2716008 : Nat := 118140960795 + 2716008 * 2 ^ 59
def prefixEnd_2716008 : Nat := 4983230072969 + 3 ^ 40 * 2716008 * 2
def baseEnd_2716008 : Nat := 929745043637809893272875

theorem tailTrace_2716008 : CollatzResearch.WordTrace tailWord_2716008 prefixEnd_2716008 929745043637809893272875 := by
  unfold tailWord_2716008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49530474972187174040974339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66040633296249565387965785 49530474972187174040974339)
  ·
    refine ⟨74295712458280761061461509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49530474972187174040974339 74295712458280761061461509)
    ·
      refine ⟨13930446085927642699024033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74295712458280761061461509 13930446085927642699024033)
      ·
        refine ⟨10447834564445732024268025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13930446085927642699024033 10447834564445732024268025)
        ·
          refine ⟨7835875923334299018201019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10447834564445732024268025 7835875923334299018201019)
          ·
            refine ⟨11753813885001448527301529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835875923334299018201019 11753813885001448527301529)
            ·
              refine ⟨8815360413751086395476147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11753813885001448527301529 8815360413751086395476147)
              ·
                refine ⟨13223040620626629593214221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815360413751086395476147 13223040620626629593214221)
                ·
                  refine ⟨4958640232734986097455333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13223040620626629593214221 4958640232734986097455333)
                  ·
                    refine ⟨929745043637809893272875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4958640232734986097455333 929745043637809893272875)
                    ·
                      rfl

theorem cell22_2716008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_2716008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716008 prefixEnd_2716008 := by exact prefixLift 2716008
  have htrace : WordTrace (prefixWord ++ tailWord_2716008) baseStart_2716008 baseEnd_2716008 := by
    simpa [prefixWord, tailWord_2716008, baseEnd_2716008] using wordTrace_append hprefix tailTrace_2716008
  have hstable : (prefixWord ++ tailWord_2716008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716008).length < 2 ^ (prefixWord ++ tailWord_2716008).sum := by decide
  have hdescent : baseEnd_2716008 < baseStart_2716008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716068 : List Nat := [2, 3, 1, 2, 1, 1, 6, 6]
def baseStart_2716068 : Nat := 118140960795 + 2716068 * 2 ^ 59
def prefixEnd_2716068 : Nat := 4983230072969 + 3 ^ 40 * 2716068 * 2
def baseEnd_2716068 : Nat := 103307286984887748530299

theorem tailTrace_2716068 : CollatzResearch.WordTrace tailWord_2716068 prefixEnd_2716068 103307286984887748530299 := by
  unfold tailWord_2716068
  simp only [CollatzResearch.WordTrace]
  refine ⟨49531569162078489164566429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66042092216104652219421905 49531569162078489164566429)
  ·
    refine ⟨18574338435779433436712411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49531569162078489164566429 18574338435779433436712411)
    ·
      refine ⟨27861507653669150155068617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18574338435779433436712411 27861507653669150155068617)
      ·
        refine ⟨20896130740251862616301463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27861507653669150155068617 20896130740251862616301463)
        ·
          refine ⟨31344196110377793924452195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20896130740251862616301463 31344196110377793924452195)
          ·
            refine ⟨47016294165566690886678293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31344196110377793924452195 47016294165566690886678293)
            ·
              refine ⟨2203888789010938635313045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47016294165566690886678293 2203888789010938635313045)
              ·
                refine ⟨103307286984887748530299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2203888789010938635313045 103307286984887748530299)
                ·
                  rfl

theorem cell22_2716068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 6, 6].length) (baseStart_2716068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716068 prefixEnd_2716068 := by exact prefixLift 2716068
  have htrace : WordTrace (prefixWord ++ tailWord_2716068) baseStart_2716068 baseEnd_2716068 := by
    simpa [prefixWord, tailWord_2716068, baseEnd_2716068] using wordTrace_append hprefix tailTrace_2716068
  have hstable : (prefixWord ++ tailWord_2716068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716068).length < 2 ^ (prefixWord ++ tailWord_2716068).sum := by decide
  have hdescent : baseEnd_2716068 < baseStart_2716068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716085 : List Nat := [1, 3, 3, 2, 4, 1, 8]
def baseStart_2716085 : Nat := 118140960795 + 2716085 * 2 ^ 59
def prefixEnd_2716085 : Nat := 4983230072969 + 3 ^ 40 * 2716085 * 2
def baseEnd_2716085 : Nat := 34435977863385457744357

theorem tailTrace_2716085 : CollatzResearch.WordTrace tailWord_2716085 prefixEnd_2716085 34435977863385457744357 := by
  unfold tailWord_2716085
  simp only [CollatzResearch.WordTrace]
  refine ⟨99063758365095390232501709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66042505576730260155001139 99063758365095390232501709)
  ·
    refine ⟨37148909386910771337188141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99063758365095390232501709 37148909386910771337188141)
    ·
      refine ⟨13930841020091539251445553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37148909386910771337188141 13930841020091539251445553)
      ·
        refine ⟨10448130765068654438584165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13930841020091539251445553 10448130765068654438584165)
        ·
          refine ⟨1959024518450372707234531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10448130765068654438584165 1959024518450372707234531)
          ·
            refine ⟨2938536777675559060851797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959024518450372707234531 2938536777675559060851797)
            ·
              refine ⟨34435977863385457744357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2938536777675559060851797 34435977863385457744357)
              ·
                rfl

theorem cell22_2716085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 8].length) (baseStart_2716085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716085 prefixEnd_2716085 := by exact prefixLift 2716085
  have htrace : WordTrace (prefixWord ++ tailWord_2716085) baseStart_2716085 baseEnd_2716085 := by
    simpa [prefixWord, tailWord_2716085, baseEnd_2716085] using wordTrace_append hprefix tailTrace_2716085
  have hstable : (prefixWord ++ tailWord_2716085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716085).length < 2 ^ (prefixWord ++ tailWord_2716085).sum := by decide
  have hdescent : baseEnd_2716085 < baseStart_2716085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716111 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_2716111 : Nat := 118140960795 + 2716111 * 2 ^ 59
def prefixEnd_2716111 : Nat := 4983230072969 + 3 ^ 40 * 2716111 * 2
def baseEnd_2716111 : Nat := 929780302642751957947559

theorem tailTrace_2716111 : CollatzResearch.WordTrace tailWord_2716111 prefixEnd_2716111 929780302642751957947559 := by
  unfold tailWord_2716111
  simp only [CollatzResearch.WordTrace]
  refine ⟨99064706663001196672948187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66043137775334131115298791 99064706663001196672948187)
  ·
    refine ⟨148597059994501795009422281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99064706663001196672948187 148597059994501795009422281)
    ·
      refine ⟨111447794995876346257066711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148597059994501795009422281 111447794995876346257066711)
      ·
        refine ⟨167171692493814519385600067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111447794995876346257066711 167171692493814519385600067)
        ·
          refine ⟨250757538740721779078400101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167171692493814519385600067 250757538740721779078400101)
          ·
            refine ⟨47017038513885333577200019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250757538740721779078400101 47017038513885333577200019)
            ·
              refine ⟨70525557770828000365800029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47017038513885333577200019 70525557770828000365800029)
              ·
                refine ⟨26447084164060500137175011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70525557770828000365800029 26447084164060500137175011)
                ·
                  refine ⟨39670626246090750205762517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26447084164060500137175011 39670626246090750205762517)
                  ·
                    refine ⟨929780302642751957947559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39670626246090750205762517 929780302642751957947559)
                    ·
                      rfl

theorem cell22_2716111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_2716111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716111 prefixEnd_2716111 := by exact prefixLift 2716111
  have htrace : WordTrace (prefixWord ++ tailWord_2716111) baseStart_2716111 baseEnd_2716111 := by
    simpa [prefixWord, tailWord_2716111, baseEnd_2716111] using wordTrace_append hprefix tailTrace_2716111
  have hstable : (prefixWord ++ tailWord_2716111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716111).length < 2 ^ (prefixWord ++ tailWord_2716111).sum := by decide
  have hdescent : baseEnd_2716111 < baseStart_2716111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716162 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_2716162 : Nat := 118140960795 + 2716162 * 2 ^ 59
def prefixEnd_2716162 : Nat := 4983230072969 + 3 ^ 40 * 2716162 * 2
def baseEnd_2716162 : Nat := 929797760985004824922403

theorem tailTrace_2716162 : CollatzResearch.WordTrace tailWord_2716162 prefixEnd_2716162 929797760985004824922403 := by
  unfold tailWord_2716162
  simp only [CollatzResearch.WordTrace]
  refine ⟨24766641696454108095763685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66044377857210954922036493 24766641696454108095763685)
  ·
    refine ⟨4643745318085145267955691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24766641696454108095763685 4643745318085145267955691)
    ·
      refine ⟨6965617977127717901933537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643745318085145267955691 6965617977127717901933537)
      ·
        refine ⟨5224213482845788426450153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6965617977127717901933537 5224213482845788426450153)
        ·
          refine ⟨3918160112134341319837615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5224213482845788426450153 3918160112134341319837615)
          ·
            refine ⟨5877240168201511979756423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918160112134341319837615 5877240168201511979756423)
            ·
              refine ⟨8815860252302267969634635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5877240168201511979756423 8815860252302267969634635)
              ·
                refine ⟨13223790378453401954451953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815860252302267969634635 13223790378453401954451953)
                ·
                  refine ⟨9917842783840051465838965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13223790378453401954451953 9917842783840051465838965)
                  ·
                    refine ⟨929797760985004824922403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9917842783840051465838965 929797760985004824922403)
                    ·
                      rfl

theorem cell22_2716162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_2716162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716162 prefixEnd_2716162 := by exact prefixLift 2716162
  have htrace : WordTrace (prefixWord ++ tailWord_2716162) baseStart_2716162 baseEnd_2716162 := by
    simpa [prefixWord, tailWord_2716162, baseEnd_2716162] using wordTrace_append hprefix tailTrace_2716162
  have hstable : (prefixWord ++ tailWord_2716162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716162).length < 2 ^ (prefixWord ++ tailWord_2716162).sum := by decide
  have hdescent : baseEnd_2716162 < baseStart_2716162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716235 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 3, 3]
def baseStart_2716235 : Nat := 118140960795 + 2716235 * 2 ^ 59
def prefixEnd_2716235 : Nat := 4983230072969 + 3 ^ 40 * 2716235 * 2
def baseEnd_2716235 : Nat := 929822750376856967847179

theorem tailTrace_2716235 : CollatzResearch.WordTrace tailWord_2716235 prefixEnd_2716235 929822750376856967847179 := by
  unfold tailWord_2716235
  simp only [CollatzResearch.WordTrace]
  refine ⟨99069229314551965850462159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66046152876367977233641439 99069229314551965850462159)
  ·
    refine ⟨148603843971827948775693239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99069229314551965850462159 148603843971827948775693239)
    ·
      refine ⟨222905765957741923163539859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148603843971827948775693239 222905765957741923163539859)
      ·
        refine ⟨334358648936612884745309789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222905765957741923163539859 334358648936612884745309789)
        ·
          refine ⟨125384493351229831779491171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334358648936612884745309789 125384493351229831779491171)
          ·
            refine ⟨188076740026844747669236757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125384493351229831779491171 188076740026844747669236757)
            ·
              refine ⟨8816097188758347546995473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188076740026844747669236757 8816097188758347546995473)
              ·
                refine ⟨6612072891568760660246605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8816097188758347546995473 6612072891568760660246605)
                ·
                  refine ⟨2479527334338285247592477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6612072891568760660246605 2479527334338285247592477)
                  ·
                    refine ⟨929822750376856967847179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2479527334338285247592477 929822750376856967847179)
                    ·
                      rfl

theorem cell22_2716235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 3].length) (baseStart_2716235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716235 prefixEnd_2716235 := by exact prefixLift 2716235
  have htrace : WordTrace (prefixWord ++ tailWord_2716235) baseStart_2716235 baseEnd_2716235 := by
    simpa [prefixWord, tailWord_2716235, baseEnd_2716235] using wordTrace_append hprefix tailTrace_2716235
  have hstable : (prefixWord ++ tailWord_2716235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716235).length < 2 ^ (prefixWord ++ tailWord_2716235).sum := by decide
  have hdescent : baseEnd_2716235 < baseStart_2716235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716237 : List Nat := [1, 6, 1, 1, 2, 1, 4, 6]
def baseStart_2716237 : Nat := 118140960795 + 2716237 * 2 ^ 59
def prefixEnd_2716237 : Nat := 4983230072969 + 3 ^ 40 * 2716237 * 2
def baseEnd_2716237 : Nat := 103313715001969958810797

theorem tailTrace_2716237 : CollatzResearch.WordTrace tailWord_2716237 prefixEnd_2716237 103313715001969958810797 := by
  unfold tailWord_2716237
  simp only [CollatzResearch.WordTrace]
  refine ⟨99069302260544720192034965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66046201507029813461356643 99069302260544720192034965)
  ·
    refine ⟨4643873543463033759001639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99069302260544720192034965 4643873543463033759001639)
    ·
      refine ⟨6965810315194550638502459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643873543463033759001639 6965810315194550638502459)
      ·
        refine ⟨10448715472791825957753689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6965810315194550638502459 10448715472791825957753689)
        ·
          refine ⟨7836536604593869468315267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10448715472791825957753689 7836536604593869468315267)
          ·
            refine ⟨11754804906890804202472901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7836536604593869468315267 11754804906890804202472901)
            ·
              refine ⟨2204025920042025787963669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11754804906890804202472901 2204025920042025787963669)
              ·
                refine ⟨103313715001969958810797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2204025920042025787963669 103313715001969958810797)
                ·
                  rfl

theorem cell22_2716237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 6].length) (baseStart_2716237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716237 prefixEnd_2716237 := by exact prefixLift 2716237
  have htrace : WordTrace (prefixWord ++ tailWord_2716237) baseStart_2716237 baseEnd_2716237 := by
    simpa [prefixWord, tailWord_2716237, baseEnd_2716237] using wordTrace_append hprefix tailTrace_2716237
  have hstable : (prefixWord ++ tailWord_2716237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716237).length < 2 ^ (prefixWord ++ tailWord_2716237).sum := by decide
  have hdescent : baseEnd_2716237 < baseStart_2716237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716248 : List Nat := [2, 1, 2, 2, 1, 2, 3, 2, 7]
def baseStart_2716248 : Nat := 118140960795 + 2716248 * 2 ^ 59
def prefixEnd_2716248 : Nat := 4983230072969 + 3 ^ 40 * 2716248 * 2
def baseEnd_2716248 : Nat := 309942400180843089090713

theorem tailTrace_2716248 : CollatzResearch.WordTrace tailWord_2716248 prefixEnd_2716248 309942400180843089090713 := by
  unfold tailWord_2716248
  simp only [CollatzResearch.WordTrace]
  refine ⟨49534851731752434535342699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66046468975669912713790265 49534851731752434535342699)
  ·
    refine ⟨74302277597628651803014049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49534851731752434535342699 74302277597628651803014049)
    ·
      refine ⟨55726708198221488852260537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74302277597628651803014049 55726708198221488852260537)
      ·
        refine ⟨41795031148666116639195403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55726708198221488852260537 41795031148666116639195403)
        ·
          refine ⟨62692546722999174958793105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41795031148666116639195403 62692546722999174958793105)
          ·
            refine ⟨47019410042249381219094829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62692546722999174958793105 47019410042249381219094829)
            ·
              refine ⟨17632278765843517957160561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47019410042249381219094829 17632278765843517957160561)
              ·
                refine ⟨13224209074382638467870421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17632278765843517957160561 13224209074382638467870421)
                ·
                  refine ⟨309942400180843089090713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13224209074382638467870421 309942400180843089090713)
                  ·
                    rfl

theorem cell22_2716248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 2, 7].length) (baseStart_2716248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716248 prefixEnd_2716248 := by exact prefixLift 2716248
  have htrace : WordTrace (prefixWord ++ tailWord_2716248) baseStart_2716248 baseEnd_2716248 := by
    simpa [prefixWord, tailWord_2716248, baseEnd_2716248] using wordTrace_append hprefix tailTrace_2716248
  have hstable : (prefixWord ++ tailWord_2716248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716248).length < 2 ^ (prefixWord ++ tailWord_2716248).sum := by decide
  have hdescent : baseEnd_2716248 < baseStart_2716248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716269 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 3, 3]
def baseStart_2716269 : Nat := 118140960795 + 2716269 * 2 ^ 59
def prefixEnd_2716269 : Nat := 4983230072969 + 3 ^ 40 * 2716269 * 2
def baseEnd_2716269 : Nat := 929834389271692212497075

theorem tailTrace_2716269 : CollatzResearch.WordTrace tailWord_2716269 prefixEnd_2716269 929834389271692212497075 := by
  unfold tailWord_2716269
  simp only [CollatzResearch.WordTrace]
  refine ⟨99070469396428789657199861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66046979597619193104799907 99070469396428789657199861)
  ·
    refine ⟨9287856505915199030362487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99070469396428789657199861 9287856505915199030362487)
    ·
      refine ⟨13931784758872798545543731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9287856505915199030362487 13931784758872798545543731)
      ·
        refine ⟨20897677138309197818315597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13931784758872798545543731 20897677138309197818315597)
        ·
          refine ⟨7836628926865949181868349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20897677138309197818315597 7836628926865949181868349)
          ·
            refine ⟨2938735847574730943200631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7836628926865949181868349 2938735847574730943200631)
            ·
              refine ⟨4408103771362096414800947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2938735847574730943200631 4408103771362096414800947)
              ·
                refine ⟨6612155657043144622201421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408103771362096414800947 6612155657043144622201421)
                ·
                  refine ⟨2479558371391179233325533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6612155657043144622201421 2479558371391179233325533)
                  ·
                    refine ⟨929834389271692212497075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2479558371391179233325533 929834389271692212497075)
                    ·
                      rfl

theorem cell22_2716269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_2716269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716269 prefixEnd_2716269 := by exact prefixLift 2716269
  have htrace : WordTrace (prefixWord ++ tailWord_2716269) baseStart_2716269 baseEnd_2716269 := by
    simpa [prefixWord, tailWord_2716269, baseEnd_2716269] using wordTrace_append hprefix tailTrace_2716269
  have hstable : (prefixWord ++ tailWord_2716269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716269).length < 2 ^ (prefixWord ++ tailWord_2716269).sum := by decide
  have hdescent : baseEnd_2716269 < baseStart_2716269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716295 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 3, 4]
def baseStart_2716295 : Nat := 118140960795 + 2716295 * 2 ^ 59
def prefixEnd_2716295 : Nat := 4983230072969 + 3 ^ 40 * 2716295 * 2
def baseEnd_2716295 : Nat := 929843289603036811346995

theorem tailTrace_2716295 : CollatzResearch.WordTrace tailWord_2716295 prefixEnd_2716295 929843289603036811346995 := by
  unfold tailWord_2716295
  simp only [CollatzResearch.WordTrace]
  refine ⟨99071417694334596097646339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66047611796223064065097559 99071417694334596097646339)
  ·
    refine ⟨148607126541501894146469509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99071417694334596097646339 148607126541501894146469509)
    ·
      refine ⟨27863836226531605152463033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148607126541501894146469509 27863836226531605152463033)
      ·
        refine ⟨20897877169898703864347275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27863836226531605152463033 20897877169898703864347275)
        ·
          refine ⟨31346815754848055796520913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20897877169898703864347275 31346815754848055796520913)
          ·
            refine ⟨23510111816136041847390685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31346815754848055796520913 23510111816136041847390685)
            ·
              refine ⟨8816291931051015692771507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23510111816136041847390685 8816291931051015692771507)
              ·
                refine ⟨13224437896576523539157261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8816291931051015692771507 13224437896576523539157261)
                ·
                  refine ⟨4959164211216196327183973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13224437896576523539157261 4959164211216196327183973)
                  ·
                    refine ⟨929843289603036811346995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959164211216196327183973 929843289603036811346995)
                    ·
                      rfl

theorem cell22_2716295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_2716295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716295 prefixEnd_2716295 := by exact prefixLift 2716295
  have htrace : WordTrace (prefixWord ++ tailWord_2716295) baseStart_2716295 baseEnd_2716295 := by
    simpa [prefixWord, tailWord_2716295, baseEnd_2716295] using wordTrace_append hprefix tailTrace_2716295
  have hstable : (prefixWord ++ tailWord_2716295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716295).length < 2 ^ (prefixWord ++ tailWord_2716295).sum := by decide
  have hdescent : baseEnd_2716295 < baseStart_2716295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716372 : List Nat := [2, 4, 1, 3, 2, 1, 9]
def baseStart_2716372 : Nat := 118140960795 + 2716372 * 2 ^ 59
def prefixEnd_2716372 : Nat := 4983230072969 + 3 ^ 40 * 2716372 * 2
def baseEnd_2716372 : Nat := 34439616602838306561917

theorem tailTrace_2716372 : CollatzResearch.WordTrace tailWord_2716372 prefixEnd_2716372 34439616602838306561917 := by
  unfold tailWord_2716372
  simp only [CollatzResearch.WordTrace]
  refine ⟨49537113057527819124099685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66049484076703758832132913 49537113057527819124099685)
  ·
    refine ⟨9288208698286466085768691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49537113057527819124099685 9288208698286466085768691)
    ·
      refine ⟨13932313047429699128653037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9288208698286466085768691 13932313047429699128653037)
      ·
        refine ⟨5224617392786137173244889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13932313047429699128653037 5224617392786137173244889)
        ·
          refine ⟨3918463044589602879933667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5224617392786137173244889 3918463044589602879933667)
          ·
            refine ⟨5877694566884404319900501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918463044589602879933667 5877694566884404319900501)
            ·
              refine ⟨34439616602838306561917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5877694566884404319900501 34439616602838306561917)
              ·
                rfl

theorem cell22_2716372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 9].length) (baseStart_2716372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716372 prefixEnd_2716372 := by exact prefixLift 2716372
  have htrace : WordTrace (prefixWord ++ tailWord_2716372) baseStart_2716372 baseEnd_2716372 := by
    simpa [prefixWord, tailWord_2716372, baseEnd_2716372] using wordTrace_append hprefix tailTrace_2716372
  have hstable : (prefixWord ++ tailWord_2716372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716372).length < 2 ^ (prefixWord ++ tailWord_2716372).sum := by decide
  have hdescent : baseEnd_2716372 < baseStart_2716372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716556 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 1, 3]
def baseStart_2716556 : Nat := 118140960795 + 2716556 * 2 ^ 59
def prefixEnd_2716556 : Nat := 4983230072969 + 3 ^ 40 * 2716556 * 2
def baseEnd_2716556 : Nat := 929932635236919130571195

theorem tailTrace_2716556 : CollatzResearch.WordTrace tailWord_2716556 prefixEnd_2716556 929932635236919130571195 := by
  unfold tailWord_2716556
  simp only [CollatzResearch.WordTrace]
  refine ⟨49540468573194518836448761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66053958097592691781931681 49540468573194518836448761)
  ·
    refine ⟨37155351429895889127336571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49540468573194518836448761 37155351429895889127336571)
    ·
      refine ⟨55733027144843833691004857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37155351429895889127336571 55733027144843833691004857)
      ·
        refine ⟨41799770358632875268253643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55733027144843833691004857 41799770358632875268253643)
        ·
          refine ⟨62699655537949312902380465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41799770358632875268253643 62699655537949312902380465)
          ·
            refine ⟨47024741653461984676785349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62699655537949312902380465 47024741653461984676785349)
            ·
              refine ⟨8817139060024122126897253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47024741653461984676785349 8817139060024122126897253)
              ·
                refine ⟨1653213573754522898793235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8817139060024122126897253 1653213573754522898793235)
                ·
                  refine ⟨2479820360631784348189853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653213573754522898793235 2479820360631784348189853)
                  ·
                    refine ⟨929932635236919130571195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2479820360631784348189853 929932635236919130571195)
                    ·
                      rfl

theorem cell22_2716556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 3].length) (baseStart_2716556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716556 prefixEnd_2716556 := by exact prefixLift 2716556
  have htrace : WordTrace (prefixWord ++ tailWord_2716556) baseStart_2716556 baseEnd_2716556 := by
    simpa [prefixWord, tailWord_2716556, baseEnd_2716556] using wordTrace_append hprefix tailTrace_2716556
  have hstable : (prefixWord ++ tailWord_2716556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716556).length < 2 ^ (prefixWord ++ tailWord_2716556).sum := by decide
  have hdescent : baseEnd_2716556 < baseStart_2716556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716567 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 2, 5]
def baseStart_2716567 : Nat := 118140960795 + 2716567 * 2 ^ 59
def prefixEnd_2716567 : Nat := 4983230072969 + 3 ^ 40 * 2716567 * 2
def baseEnd_2716567 : Nat := 929936400761718768546161

theorem tailTrace_2716567 : CollatzResearch.WordTrace tailWord_2716567 prefixEnd_2716567 929936400761718768546161 := by
  unfold tailWord_2716567
  simp only [CollatzResearch.WordTrace]
  refine ⟨99081338349349186551547955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66054225566232791034365303 99081338349349186551547955)
  ·
    refine ⟨148622007524023779827321933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99081338349349186551547955 148622007524023779827321933)
    ·
      refine ⟨55733252821508917435245725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148622007524023779827321933 55733252821508917435245725)
      ·
        refine ⟨20899969808065844038217147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55733252821508917435245725 20899969808065844038217147)
        ·
          refine ⟨31349954712098766057325721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20899969808065844038217147 31349954712098766057325721)
          ·
            refine ⟨23512466034074074542994291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31349954712098766057325721 23512466034074074542994291)
            ·
              refine ⟨35268699051111111814491437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23512466034074074542994291 35268699051111111814491437)
              ·
                refine ⟨13225762144166666930434289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35268699051111111814491437 13225762144166666930434289)
                ·
                  refine ⟨9919321608125000197825717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13225762144166666930434289 9919321608125000197825717)
                  ·
                    refine ⟨929936400761718768546161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9919321608125000197825717 929936400761718768546161)
                    ·
                      rfl

theorem cell22_2716567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_2716567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716567 prefixEnd_2716567 := by exact prefixLift 2716567
  have htrace : WordTrace (prefixWord ++ tailWord_2716567) baseStart_2716567 baseEnd_2716567 := by
    simpa [prefixWord, tailWord_2716567, baseEnd_2716567] using wordTrace_append hprefix tailTrace_2716567
  have hstable : (prefixWord ++ tailWord_2716567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716567).length < 2 ^ (prefixWord ++ tailWord_2716567).sum := by decide
  have hdescent : baseEnd_2716567 < baseStart_2716567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716599 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 1, 4]
def baseStart_2716599 : Nat := 118140960795 + 2716599 * 2 ^ 59
def prefixEnd_2716599 : Nat := 4983230072969 + 3 ^ 40 * 2716599 * 2
def baseEnd_2716599 : Nat := 929947355015681351746063

theorem tailTrace_2716599 : CollatzResearch.WordTrace tailWord_2716599 prefixEnd_2716599 929947355015681351746063 := by
  unfold tailWord_2716599
  simp only [CollatzResearch.WordTrace]
  refine ⟨99082505485233256016712851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66055003656822170677808567 99082505485233256016712851)
  ·
    refine ⟨148623758227849884025069277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99082505485233256016712851 148623758227849884025069277)
    ·
      refine ⟨55733909335443706509400979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148623758227849884025069277 55733909335443706509400979)
      ·
        refine ⟨83600864003165559764101469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55733909335443706509400979 83600864003165559764101469)
        ·
          refine ⟨31350324001187084911538051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83600864003165559764101469 31350324001187084911538051)
          ·
            refine ⟨47025486001780627367307077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31350324001187084911538051 47025486001780627367307077)
            ·
              refine ⟨8817278625333867631370077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47025486001780627367307077 8817278625333867631370077)
              ·
                refine ⟨3306479484500200361763779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8817278625333867631370077 3306479484500200361763779)
                ·
                  refine ⟨4959719226750300542645669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306479484500200361763779 4959719226750300542645669)
                  ·
                    refine ⟨929947355015681351746063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959719226750300542645669 929947355015681351746063)
                    ·
                      rfl

theorem cell22_2716599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 4].length) (baseStart_2716599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716599 prefixEnd_2716599 := by exact prefixLift 2716599
  have htrace : WordTrace (prefixWord ++ tailWord_2716599) baseStart_2716599 baseEnd_2716599 := by
    simpa [prefixWord, tailWord_2716599, baseEnd_2716599] using wordTrace_append hprefix tailTrace_2716599
  have hstable : (prefixWord ++ tailWord_2716599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716599).length < 2 ^ (prefixWord ++ tailWord_2716599).sum := by decide
  have hdescent : baseEnd_2716599 < baseStart_2716599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716783 : List Nat := [1, 1, 2, 1, 3, 3, 5, 2, 4]
def baseStart_2716783 : Nat := 118140960795 + 2716783 * 2 ^ 59
def prefixEnd_2716783 : Nat := 4983230072969 + 3 ^ 40 * 2716783 * 2
def baseEnd_2716783 : Nat := 310003447325322068381833

theorem tailTrace_2716783 : CollatzResearch.WordTrace tailWord_2716783 prefixEnd_2716783 310003447325322068381833 := by
  unfold tailWord_2716783
  simp only [CollatzResearch.WordTrace]
  refine ⟨99089216516566655441411003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66059477677711103627607335 99089216516566655441411003)
  ·
    refine ⟨148633824774849983162116505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99089216516566655441411003 148633824774849983162116505)
    ·
      refine ⟨111475368581137487371587379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148633824774849983162116505 111475368581137487371587379)
      ·
        refine ⟨167213052871706231057381069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111475368581137487371587379 167213052871706231057381069)
        ·
          refine ⟨62704894826889836646517901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167213052871706231057381069 62704894826889836646517901)
          ·
            refine ⟨23514335560083688742444213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62704894826889836646517901 23514335560083688742444213)
            ·
              refine ⟨2204468958757845819604145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23514335560083688742444213 2204468958757845819604145)
              ·
                refine ⟨1653351719068384364703109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204468958757845819604145 1653351719068384364703109)
                ·
                  refine ⟨310003447325322068381833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653351719068384364703109 310003447325322068381833)
                  ·
                    rfl

theorem cell22_2716783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2, 4].length) (baseStart_2716783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716783 prefixEnd_2716783 := by exact prefixLift 2716783
  have htrace : WordTrace (prefixWord ++ tailWord_2716783) baseStart_2716783 baseEnd_2716783 := by
    simpa [prefixWord, tailWord_2716783, baseEnd_2716783] using wordTrace_append hprefix tailTrace_2716783
  have hstable : (prefixWord ++ tailWord_2716783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716783).length < 2 ^ (prefixWord ++ tailWord_2716783).sum := by decide
  have hdescent : baseEnd_2716783 < baseStart_2716783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716834 : List Nat := [3, 3, 1, 3, 3, 1, 2, 2, 4]
def baseStart_2716834 : Nat := 118140960795 + 2716834 * 2 ^ 59
def prefixEnd_2716834 : Nat := 4983230072969 + 3 ^ 40 * 2716834 * 2
def baseEnd_2716834 : Nat := 310009266772739690706781

theorem tailTrace_2716834 : CollatzResearch.WordTrace tailWord_2716834 prefixEnd_2716834 310009266772739690706781 := by
  unfold tailWord_2716834
  simp only [CollatzResearch.WordTrace]
  refine ⟨24772769159845472787879389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66060717759587927434345037 24772769159845472787879389)
  ·
    refine ⟨9289788434942052295454771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24772769159845472787879389 9289788434942052295454771)
    ·
      refine ⟨13934682652413078443182157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9289788434942052295454771 13934682652413078443182157)
      ·
        refine ⟨5225505994654904416193309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13934682652413078443182157 5225505994654904416193309)
        ·
          refine ⟨1959564747995589156072491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5225505994654904416193309 1959564747995589156072491)
          ·
            refine ⟨2939347121993383734108737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959564747995589156072491 2939347121993383734108737)
            ·
              refine ⟨2204510341495037800581553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2939347121993383734108737 2204510341495037800581553)
              ·
                refine ⟨1653382756121278350436165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204510341495037800581553 1653382756121278350436165)
                ·
                  refine ⟨310009266772739690706781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653382756121278350436165 310009266772739690706781)
                  ·
                    rfl

theorem cell22_2716834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_2716834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716834 prefixEnd_2716834 := by exact prefixLift 2716834
  have htrace : WordTrace (prefixWord ++ tailWord_2716834) baseStart_2716834 baseEnd_2716834 := by
    simpa [prefixWord, tailWord_2716834, baseEnd_2716834] using wordTrace_append hprefix tailTrace_2716834
  have hstable : (prefixWord ++ tailWord_2716834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716834).length < 2 ^ (prefixWord ++ tailWord_2716834).sum := by decide
  have hdescent : baseEnd_2716834 < baseStart_2716834 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716845 : List Nat := [1, 5, 2, 1, 4, 1, 1, 7]
def baseStart_2716845 : Nat := 118140960795 + 2716845 * 2 ^ 59
def prefixEnd_2716845 : Nat := 4983230072969 + 3 ^ 40 * 2716845 * 2
def baseEnd_2716845 : Nat := 103336840649224301121701

theorem tailTrace_2716845 : CollatzResearch.WordTrace tailWord_2716845 prefixEnd_2716845 103336840649224301121701 := by
  unfold tailWord_2716845
  simp only [CollatzResearch.WordTrace]
  refine ⟨99091477842342040030167989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66060985228228026686778659 99091477842342040030167989)
  ·
    refine ⟨9289826047719566252828249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99091477842342040030167989 9289826047719566252828249)
    ·
      refine ⟨6967369535789674689621187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9289826047719566252828249 6967369535789674689621187)
      ·
        refine ⟨10451054303684512034431781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6967369535789674689621187 10451054303684512034431781)
        ·
          refine ⟨1959572681940846006455959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10451054303684512034431781 1959572681940846006455959)
          ·
            refine ⟨2939359022911269009683939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959572681940846006455959 2939359022911269009683939)
            ·
              refine ⟨4409038534366903514525909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2939359022911269009683939 4409038534366903514525909)
              ·
                refine ⟨103336840649224301121701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4409038534366903514525909 103336840649224301121701)
                ·
                  rfl

theorem cell22_2716845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 7].length) (baseStart_2716845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716845 prefixEnd_2716845 := by exact prefixLift 2716845
  have htrace : WordTrace (prefixWord ++ tailWord_2716845) baseStart_2716845 baseEnd_2716845 := by
    simpa [prefixWord, tailWord_2716845, baseEnd_2716845] using wordTrace_append hprefix tailTrace_2716845
  have hstable : (prefixWord ++ tailWord_2716845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716845).length < 2 ^ (prefixWord ++ tailWord_2716845).sum := by decide
  have hdescent : baseEnd_2716845 < baseStart_2716845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716931 : List Nat := [1, 1, 1, 3, 2, 4, 2, 1, 1, 6]
def baseStart_2716931 : Nat := 118140960795 + 2716931 * 2 ^ 59
def prefixEnd_2716931 : Nat := 4983230072969 + 3 ^ 40 * 2716931 * 2
def baseEnd_2716931 : Nat := 930061005400543152445045

theorem tailTrace_2716931 : CollatzResearch.WordTrace tailWord_2716931 prefixEnd_2716931 930061005400543152445045 := by
  unfold tailWord_2716931
  simp only [CollatzResearch.WordTrace]
  refine ⟨99094614520030476717798647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66063076346686984478532431 99094614520030476717798647)
  ·
    refine ⟨148641921780045715076697971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99094614520030476717798647 148641921780045715076697971)
    ·
      refine ⟨222962882670068572615046957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148641921780045715076697971 222962882670068572615046957)
      ·
        refine ⟨83611081001275714730642609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222962882670068572615046957 83611081001275714730642609)
        ·
          refine ⟨62708310750956786047981957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83611081001275714730642609 62708310750956786047981957)
          ·
            refine ⟨11757808265804397383996617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62708310750956786047981957 11757808265804397383996617)
            ·
              refine ⟨8818356199353298037997463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11757808265804397383996617 8818356199353298037997463)
              ·
                refine ⟨13227534299029947056996195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8818356199353298037997463 13227534299029947056996195)
                ·
                  refine ⟨19841301448544920585494293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13227534299029947056996195 19841301448544920585494293)
                  ·
                    refine ⟨930061005400543152445045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19841301448544920585494293 930061005400543152445045)
                    ·
                      rfl

theorem cell22_2716931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 6].length) (baseStart_2716931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716931 prefixEnd_2716931 := by exact prefixLift 2716931
  have htrace : WordTrace (prefixWord ++ tailWord_2716931) baseStart_2716931 baseEnd_2716931 := by
    simpa [prefixWord, tailWord_2716931, baseEnd_2716931] using wordTrace_append hprefix tailTrace_2716931
  have hstable : (prefixWord ++ tailWord_2716931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716931).length < 2 ^ (prefixWord ++ tailWord_2716931).sum := by decide
  have hdescent : baseEnd_2716931 < baseStart_2716931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2716995 : List Nat := [1, 1, 1, 3, 1, 3, 1, 7, 1, 3]
def baseStart_2716995 : Nat := 118140960795 + 2716995 * 2 ^ 59
def prefixEnd_2716995 : Nat := 4983230072969 + 3 ^ 40 * 2716995 * 2
def baseEnd_2716995 : Nat := 930082913908468318844849

theorem tailTrace_2716995 : CollatzResearch.WordTrace tailWord_2716995 prefixEnd_2716995 930082913908468318844849 := by
  unfold tailWord_2716995
  simp only [CollatzResearch.WordTrace]
  refine ⟨99096948791798615648128439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66064632527865743765418959 99096948791798615648128439)
  ·
    refine ⟨148645423187697923472192659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99096948791798615648128439 148645423187697923472192659)
    ·
      refine ⟨222968134781546885208288989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148645423187697923472192659 222968134781546885208288989)
      ·
        refine ⟨83613050543080081953108371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222968134781546885208288989 83613050543080081953108371)
        ·
          refine ⟨125419575814620122929662557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83613050543080081953108371 125419575814620122929662557)
          ·
            refine ⟨47032340930482546098623459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125419575814620122929662557 47032340930482546098623459)
            ·
              refine ⟨70548511395723819147935189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47032340930482546098623459 70548511395723819147935189)
              ·
                refine ⟨1653480735837277011279731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 70548511395723819147935189 1653480735837277011279731)
                ·
                  refine ⟨2480221103755915516919597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653480735837277011279731 2480221103755915516919597)
                  ·
                    refine ⟨930082913908468318844849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480221103755915516919597 930082913908468318844849)
                    ·
                      rfl

theorem cell22_2716995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 7, 1, 3].length) (baseStart_2716995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2716995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2716995 prefixEnd_2716995 := by exact prefixLift 2716995
  have htrace : WordTrace (prefixWord ++ tailWord_2716995) baseStart_2716995 baseEnd_2716995 := by
    simpa [prefixWord, tailWord_2716995, baseEnd_2716995] using wordTrace_append hprefix tailTrace_2716995
  have hstable : (prefixWord ++ tailWord_2716995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2716995).length < 2 ^ (prefixWord ++ tailWord_2716995).sum := by decide
  have hdescent : baseEnd_2716995 < baseStart_2716995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2716995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717008 : List Nat := [2, 1, 1, 1, 1, 5, 4, 2, 5]
def baseStart_2717008 : Nat := 118140960795 + 2717008 * 2 ^ 59
def prefixEnd_2717008 : Nat := 4983230072969 + 3 ^ 40 * 2717008 * 2
def baseEnd_2717008 : Nat := 310029121358046872756603

theorem tailTrace_2717008 : CollatzResearch.WordTrace tailWord_2717008 prefixEnd_2717008 310029121358046872756603 := by
  unfold tailWord_2717008
  simp only [CollatzResearch.WordTrace]
  refine ⟨49548711470375759434175839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66064948627167679245567785 49548711470375759434175839)
  ·
    refine ⟨74323067205563639151263759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49548711470375759434175839 74323067205563639151263759)
    ·
      refine ⟨111484600808345458726895639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74323067205563639151263759 111484600808345458726895639)
      ·
        refine ⟨167226901212518188090343459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111484600808345458726895639 167226901212518188090343459)
        ·
          refine ⟨250840351818777282135515189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167226901212518188090343459 250840351818777282135515189)
          ·
            refine ⟨23516282983010370200204549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 250840351818777282135515189 23516282983010370200204549)
            ·
              refine ⟨4409303059314444412538353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23516282983010370200204549 4409303059314444412538353)
              ·
                refine ⟨3306977294485833309403765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409303059314444412538353 3306977294485833309403765)
                ·
                  refine ⟨310029121358046872756603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3306977294485833309403765 310029121358046872756603)
                  ·
                    rfl

theorem cell22_2717008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 2, 5].length) (baseStart_2717008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717008 prefixEnd_2717008 := by exact prefixLift 2717008
  have htrace : WordTrace (prefixWord ++ tailWord_2717008) baseStart_2717008 baseEnd_2717008 := by
    simpa [prefixWord, tailWord_2717008, baseEnd_2717008] using wordTrace_append hprefix tailTrace_2717008
  have hstable : (prefixWord ++ tailWord_2717008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717008).length < 2 ^ (prefixWord ++ tailWord_2717008).sum := by decide
  have hdescent : baseEnd_2717008 < baseStart_2717008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717012 : List Nat := [2, 4, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_2717012 : Nat := 118140960795 + 2717012 * 2 ^ 59
def prefixEnd_2717012 : Nat := 4983230072969 + 3 ^ 40 * 2717012 * 2
def baseEnd_2717012 : Nat := 930088733355885941169797

theorem tailTrace_2717012 : CollatzResearch.WordTrace tailWord_2717012 prefixEnd_2717012 930088733355885941169797 := by
  unfold tailWord_2717012
  simp only [CollatzResearch.WordTrace]
  refine ⟨49548784416368513775748645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66065045888491351700998193 49548784416368513775748645)
  ·
    refine ⟨9290397078069096332952871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49548784416368513775748645 9290397078069096332952871)
    ·
      refine ⟨13935595617103644499429307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9290397078069096332952871 13935595617103644499429307)
      ·
        refine ⟨20903393425655466749143961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13935595617103644499429307 20903393425655466749143961)
        ·
          refine ⟨15677545069241600061857971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20903393425655466749143961 15677545069241600061857971)
          ·
            refine ⟨23516317603862400092786957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15677545069241600061857971 23516317603862400092786957)
            ·
              refine ⟨8818619101448400034795109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23516317603862400092786957 8818619101448400034795109)
              ·
                refine ⟨1653491081521575006524083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8818619101448400034795109 1653491081521575006524083)
                ·
                  refine ⟨2480236622282362509786125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653491081521575006524083 2480236622282362509786125)
                  ·
                    refine ⟨930088733355885941169797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480236622282362509786125 930088733355885941169797)
                    ·
                      rfl

theorem cell22_2717012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_2717012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717012 prefixEnd_2717012 := by exact prefixLift 2717012
  have htrace : WordTrace (prefixWord ++ tailWord_2717012) baseStart_2717012 baseEnd_2717012 := by
    simpa [prefixWord, tailWord_2717012, baseEnd_2717012] using wordTrace_append hprefix tailTrace_2717012
  have hstable : (prefixWord ++ tailWord_2717012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717012).length < 2 ^ (prefixWord ++ tailWord_2717012).sum := by decide
  have hdescent : baseEnd_2717012 < baseStart_2717012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717085 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 1, 5]
def baseStart_2717085 : Nat := 118140960795 + 2717085 * 2 ^ 59
def prefixEnd_2717085 : Nat := 4983230072969 + 3 ^ 40 * 2717085 * 2
def baseEnd_2717085 : Nat := 930113722747738084094573

theorem tailTrace_2717085 : CollatzResearch.WordTrace tailWord_2717085 prefixEnd_2717085 930113722747738084094573 := by
  unfold tailWord_2717085
  simp only [CollatzResearch.WordTrace]
  refine ⟨99100231361472561018904709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66066820907648374012603139 99100231361472561018904709)
  ·
    refine ⟨18581293380276105191044633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99100231361472561018904709 18581293380276105191044633)
    ·
      refine ⟨13935970035207078893283475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18581293380276105191044633 13935970035207078893283475)
      ·
        refine ⟨20903955052810618339925213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13935970035207078893283475 20903955052810618339925213)
        ·
          refine ⟨7838983144803981877471955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20903955052810618339925213 7838983144803981877471955)
          ·
            refine ⟨11758474717205972816207933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7838983144803981877471955 11758474717205972816207933)
            ·
              refine ⟨4409428018952239806077975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11758474717205972816207933 4409428018952239806077975)
              ·
                refine ⟨6614142028428359709116963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4409428018952239806077975 6614142028428359709116963)
                ·
                  refine ⟨9921213042642539563675445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6614142028428359709116963 9921213042642539563675445)
                  ·
                    refine ⟨930113722747738084094573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9921213042642539563675445 930113722747738084094573)
                    ·
                      rfl

theorem cell22_2717085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_2717085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717085 prefixEnd_2717085 := by exact prefixLift 2717085
  have htrace : WordTrace (prefixWord ++ tailWord_2717085) baseStart_2717085 baseEnd_2717085 := by
    simpa [prefixWord, tailWord_2717085, baseEnd_2717085] using wordTrace_append hprefix tailTrace_2717085
  have hstable : (prefixWord ++ tailWord_2717085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717085).length < 2 ^ (prefixWord ++ tailWord_2717085).sum := by decide
  have hdescent : baseEnd_2717085 < baseStart_2717085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717128 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 2, 6]
def baseStart_2717128 : Nat := 118140960795 + 2717128 * 2 ^ 59
def prefixEnd_2717128 : Nat := 4983230072969 + 3 ^ 40 * 2717128 * 2
def baseEnd_2717128 : Nat := 930128442526500305269441

theorem tailTrace_2717128 : CollatzResearch.WordTrace tailWord_2717128 prefixEnd_2717128 930128442526500305269441 := by
  unfold tailWord_2717128
  simp only [CollatzResearch.WordTrace]
  refine ⟨49550899850158389681360019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66067866466877852908480025 49550899850158389681360019)
  ·
    refine ⟨74326349775237584522040029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49550899850158389681360019 74326349775237584522040029)
    ·
      refine ⟨27872381165714094195765011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74326349775237584522040029 27872381165714094195765011)
      ·
        refine ⟨41808571748571141293647517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27872381165714094195765011 41808571748571141293647517)
        ·
          refine ⟨15678214405714177985117819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41808571748571141293647517 15678214405714177985117819)
          ·
            refine ⟨23517321608571266977676729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15678214405714177985117819 23517321608571266977676729)
            ·
              refine ⟨17637991206428450233257547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23517321608571266977676729 17637991206428450233257547)
              ·
                refine ⟨26456986809642675349886321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17637991206428450233257547 26456986809642675349886321)
                ·
                  refine ⟨19842740107232006512414741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26456986809642675349886321 19842740107232006512414741)
                  ·
                    refine ⟨930128442526500305269441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19842740107232006512414741 930128442526500305269441)
                    ·
                      rfl

theorem cell22_2717128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_2717128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717128 prefixEnd_2717128 := by exact prefixLift 2717128
  have htrace : WordTrace (prefixWord ++ tailWord_2717128) baseStart_2717128 baseEnd_2717128 := by
    simpa [prefixWord, tailWord_2717128, baseEnd_2717128] using wordTrace_append hprefix tailTrace_2717128
  have hstable : (prefixWord ++ tailWord_2717128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717128).length < 2 ^ (prefixWord ++ tailWord_2717128).sum := by decide
  have hdescent : baseEnd_2717128 < baseStart_2717128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717181 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 1, 3]
def baseStart_2717181 : Nat := 118140960795 + 2717181 * 2 ^ 59
def prefixEnd_2717181 : Nat := 4983230072969 + 3 ^ 40 * 2717181 * 2
def baseEnd_2717181 : Nat := 930146585509625833694279

theorem tailTrace_2717181 : CollatzResearch.WordTrace tailWord_2717181 prefixEnd_2717181 930146585509625833694279 := by
  unfold tailWord_2717181
  simp only [CollatzResearch.WordTrace]
  refine ⟨99103732769124769414399397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66069155179416512942932931 99103732769124769414399397)
  ·
    refine ⟨18581949894210894265199887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99103732769124769414399397 18581949894210894265199887)
    ·
      refine ⟨27872924841316341397799831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18581949894210894265199887 27872924841316341397799831)
      ·
        refine ⟨41809387261974512096699747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27872924841316341397799831 41809387261974512096699747)
        ·
          refine ⟨62714080892961768145049621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41809387261974512096699747 62714080892961768145049621)
          ·
            refine ⟨2939722541857582881799201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62714080892961768145049621 2939722541857582881799201)
            ·
              refine ⟨2204791906393187161349401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2939722541857582881799201 2204791906393187161349401)
              ·
                refine ⟨1653593929794890371012051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204791906393187161349401 1653593929794890371012051)
                ·
                  refine ⟨2480390894692335556518077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653593929794890371012051 2480390894692335556518077)
                  ·
                    refine ⟨930146585509625833694279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480390894692335556518077 930146585509625833694279)
                    ·
                      rfl

theorem cell22_2717181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 3].length) (baseStart_2717181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717181 prefixEnd_2717181 := by exact prefixLift 2717181
  have htrace : WordTrace (prefixWord ++ tailWord_2717181) baseStart_2717181 baseEnd_2717181 := by
    simpa [prefixWord, tailWord_2717181, baseEnd_2717181] using wordTrace_append hprefix tailTrace_2717181
  have hstable : (prefixWord ++ tailWord_2717181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717181).length < 2 ^ (prefixWord ++ tailWord_2717181).sum := by decide
  have hdescent : baseEnd_2717181 < baseStart_2717181 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717205 : List Nat := [1, 3, 2, 1, 3, 3, 1, 2, 6]
def baseStart_2717205 : Nat := 118140960795 + 2717205 * 2 ^ 59
def prefixEnd_2717205 : Nat := 4983230072969 + 3 ^ 40 * 2717205 * 2
def baseEnd_2717205 : Nat := 310051600400032590364735

theorem tailTrace_2717205 : CollatzResearch.WordTrace tailWord_2717205 prefixEnd_2717205 310051600400032590364735 := by
  unfold tailWord_2717205
  simp only [CollatzResearch.WordTrace]
  refine ⟨99104608121037821513273069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66069738747358547675515379 99104608121037821513273069)
  ·
    refine ⟨37164228045389183067477401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99104608121037821513273069 37164228045389183067477401)
    ·
      refine ⟨27873171034041887300608051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37164228045389183067477401 27873171034041887300608051)
      ·
        refine ⟨41809756551062830950912077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27873171034041887300608051 41809756551062830950912077)
        ·
          refine ⟨15678658706648561606592029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41809756551062830950912077 15678658706648561606592029)
          ·
            refine ⟨5879497014993210602472011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15678658706648561606592029 5879497014993210602472011)
            ·
              refine ⟨8819245522489815903708017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879497014993210602472011 8819245522489815903708017)
              ·
                refine ⟨6614434141867361927781013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8819245522489815903708017 6614434141867361927781013)
                ·
                  refine ⟨310051600400032590364735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6614434141867361927781013 310051600400032590364735)
                  ·
                    rfl

theorem cell22_2717205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_2717205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717205 prefixEnd_2717205 := by exact prefixLift 2717205
  have htrace : WordTrace (prefixWord ++ tailWord_2717205) baseStart_2717205 baseEnd_2717205 := by
    simpa [prefixWord, tailWord_2717205, baseEnd_2717205] using wordTrace_append hprefix tailTrace_2717205
  have hstable : (prefixWord ++ tailWord_2717205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717205).length < 2 ^ (prefixWord ++ tailWord_2717205).sum := by decide
  have hdescent : baseEnd_2717205 < baseStart_2717205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717224 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 1, 4]
def baseStart_2717224 : Nat := 118140960795 + 2717224 * 2 ^ 59
def prefixEnd_2717224 : Nat := 4983230072969 + 3 ^ 40 * 2717224 * 2
def baseEnd_2717224 : Nat := 930161305288388054869147

theorem tailTrace_2717224 : CollatzResearch.WordTrace tailWord_2717224 prefixEnd_2717224 930161305288388054869147 := by
  unfold tailWord_2717224
  simp only [CollatzResearch.WordTrace]
  refine ⟨49552650553984493879107363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66070200738645991838809817 49552650553984493879107363)
  ·
    refine ⟨74328975830976740818661045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49552650553984493879107363 74328975830976740818661045)
    ·
      refine ⟨6968341484154069451749473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74328975830976740818661045 6968341484154069451749473)
      ·
        refine ⟨5226256113115552088812105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6968341484154069451749473 5226256113115552088812105)
        ·
          refine ⟨3919692084836664066609079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5226256113115552088812105 3919692084836664066609079)
          ·
            refine ⟨5879538127254996099913619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919692084836664066609079 5879538127254996099913619)
            ·
              refine ⟨8819307190882494149870429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879538127254996099913619 8819307190882494149870429)
              ·
                refine ⟨3307240196580935306201411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8819307190882494149870429 3307240196580935306201411)
                ·
                  refine ⟨4960860294871402959302117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307240196580935306201411 4960860294871402959302117)
                  ·
                    refine ⟨930161305288388054869147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4960860294871402959302117 930161305288388054869147)
                    ·
                      rfl

theorem cell22_2717224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_2717224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717224 prefixEnd_2717224 := by exact prefixLift 2717224
  have htrace : WordTrace (prefixWord ++ tailWord_2717224) baseStart_2717224 baseEnd_2717224 := by
    simpa [prefixWord, tailWord_2717224, baseEnd_2717224] using wordTrace_append hprefix tailTrace_2717224
  have hstable : (prefixWord ++ tailWord_2717224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717224).length < 2 ^ (prefixWord ++ tailWord_2717224).sum := by decide
  have hdescent : baseEnd_2717224 < baseStart_2717224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717237 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 4, 3]
def baseStart_2717237 : Nat := 118140960795 + 2717237 * 2 ^ 59
def prefixEnd_2717237 : Nat := 4983230072969 + 3 ^ 40 * 2717237 * 2
def baseEnd_2717237 : Nat := 930165755454060354294107

theorem tailTrace_2717237 : CollatzResearch.WordTrace tailWord_2717237 prefixEnd_2717237 930165755454060354294107 := by
  unfold tailWord_2717237
  simp only [CollatzResearch.WordTrace]
  refine ⟨99105775256921890978437965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66070516837947927318958643 99105775256921890978437965)
  ·
    refine ⟨37164665721345709116914237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99105775256921890978437965 37164665721345709116914237)
    ·
      refine ⟨13936749645504640918842839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37164665721345709116914237 13936749645504640918842839)
      ·
        refine ⟨20905124468256961378264259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13936749645504640918842839 20905124468256961378264259)
        ·
          refine ⟨31357686702385442067396389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20905124468256961378264259 31357686702385442067396389)
          ·
            refine ⟨5879566256697270387636823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31357686702385442067396389 5879566256697270387636823)
            ·
              refine ⟨8819349385045905581455235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5879566256697270387636823 8819349385045905581455235)
              ·
                refine ⟨13229024077568858372182853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8819349385045905581455235 13229024077568858372182853)
                ·
                  refine ⟨2480442014544160944784285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13229024077568858372182853 2480442014544160944784285)
                  ·
                    refine ⟨930165755454060354294107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480442014544160944784285 930165755454060354294107)
                    ·
                      rfl

theorem cell22_2717237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_2717237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717237 prefixEnd_2717237 := by exact prefixLift 2717237
  have htrace : WordTrace (prefixWord ++ tailWord_2717237) baseStart_2717237 baseEnd_2717237 := by
    simpa [prefixWord, tailWord_2717237, baseEnd_2717237] using wordTrace_append hprefix tailTrace_2717237
  have hstable : (prefixWord ++ tailWord_2717237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717237).length < 2 ^ (prefixWord ++ tailWord_2717237).sum := by decide
  have hdescent : baseEnd_2717237 < baseStart_2717237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717295 : List Nat := [1, 1, 2, 1, 3, 2, 1, 6, 5]
def baseStart_2717295 : Nat := 118140960795 + 2717295 * 2 ^ 59
def prefixEnd_2717295 : Nat := 4983230072969 + 3 ^ 40 * 2717295 * 2
def baseEnd_2717295 : Nat := 310061870013122512114643

theorem tailTrace_2717295 : CollatzResearch.WordTrace tailWord_2717295 prefixEnd_2717295 310061870013122512114643 := by
  unfold tailWord_2717295
  simp only [CollatzResearch.WordTrace]
  refine ⟨99107890690711766884049339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66071927127141177922699559 99107890690711766884049339)
  ·
    refine ⟨148661836036067650326074009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99107890690711766884049339 148661836036067650326074009)
    ·
      refine ⟨111496377027050737744555507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148661836036067650326074009 111496377027050737744555507)
      ·
        refine ⟨167244565540576106616833261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111496377027050737744555507 167244565540576106616833261)
        ·
          refine ⟨62716712077716039981312473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167244565540576106616833261 62716712077716039981312473)
          ·
            refine ⟨47037534058287029985984355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62716712077716039981312473 47037534058287029985984355)
            ·
              refine ⟨70556301087430544978976533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47037534058287029985984355 70556301087430544978976533)
              ·
                refine ⟨3307326613473306795889525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70556301087430544978976533 3307326613473306795889525)
                ·
                  refine ⟨310061870013122512114643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3307326613473306795889525 310061870013122512114643)
                  ·
                    rfl

theorem cell22_2717295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6, 5].length) (baseStart_2717295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717295 prefixEnd_2717295 := by exact prefixLift 2717295
  have htrace : WordTrace (prefixWord ++ tailWord_2717295) baseStart_2717295 baseEnd_2717295 := by
    simpa [prefixWord, tailWord_2717295, baseEnd_2717295] using wordTrace_append hprefix tailTrace_2717295
  have hstable : (prefixWord ++ tailWord_2717295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717295).length < 2 ^ (prefixWord ++ tailWord_2717295).sum := by decide
  have hdescent : baseEnd_2717295 < baseStart_2717295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717346 : List Nat := [3, 3, 1, 4, 1, 1, 2, 2, 5]
def baseStart_2717346 : Nat := 118140960795 + 2717346 * 2 ^ 59
def prefixEnd_2717346 : Nat := 4983230072969 + 3 ^ 40 * 2717346 * 2
def baseEnd_2717346 : Nat := 310067689460540134439591

theorem tailTrace_2717346 : CollatzResearch.WordTrace tailWord_2717346 prefixEnd_2717346 310067689460540134439591 := by
  unfold tailWord_2717346
  simp only [CollatzResearch.WordTrace]
  refine ⟨24777437703381750648538973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66073167209018001729437261 24777437703381750648538973)
  ·
    refine ⟨9291539138768156493202115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24777437703381750648538973 9291539138768156493202115)
    ·
      refine ⟨13937308708152234739803173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9291539138768156493202115 13937308708152234739803173)
      ·
        refine ⟨2613245382778544013713095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13937308708152234739803173 2613245382778544013713095)
        ·
          refine ⟨3919868074167816020569643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2613245382778544013713095 3919868074167816020569643)
          ·
            refine ⟨5879802111251724030854465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3919868074167816020569643 5879802111251724030854465)
            ·
              refine ⟨4409851583438793023140849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5879802111251724030854465 4409851583438793023140849)
              ·
                refine ⟨3307388687579094767355637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4409851583438793023140849 3307388687579094767355637)
                ·
                  refine ⟨310067689460540134439591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3307388687579094767355637 310067689460540134439591)
                  ·
                    rfl

theorem cell22_2717346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_2717346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717346 prefixEnd_2717346 := by exact prefixLift 2717346
  have htrace : WordTrace (prefixWord ++ tailWord_2717346) baseStart_2717346 baseEnd_2717346 := by
    simpa [prefixWord, tailWord_2717346, baseEnd_2717346] using wordTrace_append hprefix tailTrace_2717346
  have hstable : (prefixWord ++ tailWord_2717346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717346).length < 2 ^ (prefixWord ++ tailWord_2717346).sum := by decide
  have hdescent : baseEnd_2717346 < baseStart_2717346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717357 : List Nat := [1, 5, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2717357 : Nat := 118140960795 + 2717357 * 2 ^ 59
def prefixEnd_2717357 : Nat := 4983230072969 + 3 ^ 40 * 2717357 * 2
def baseEnd_2717357 : Nat := 310068944635473347097913

theorem tailTrace_2717357 : CollatzResearch.WordTrace tailWord_2717357 prefixEnd_2717357 310068944635473347097913 := by
  unfold tailWord_2717357
  simp only [CollatzResearch.WordTrace]
  refine ⟨99110152016487151472806325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66073434677658100981870883 99110152016487151472806325)
  ·
    refine ⟨9291576751545670450575593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99110152016487151472806325 9291576751545670450575593)
    ·
      refine ⟨6968682563659252837931695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9291576751545670450575593 6968682563659252837931695)
      ·
        refine ⟨10453023845488879256897543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6968682563659252837931695 10453023845488879256897543)
        ·
          refine ⟨15679535768233318885346315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10453023845488879256897543 15679535768233318885346315)
          ·
            refine ⟨23519303652349978328019473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15679535768233318885346315 23519303652349978328019473)
            ·
              refine ⟨17639477739262483746014605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23519303652349978328019473 17639477739262483746014605)
              ·
                refine ⟨6614804152223431404755477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17639477739262483746014605 6614804152223431404755477)
                ·
                  refine ⟨310068944635473347097913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6614804152223431404755477 310068944635473347097913)
                  ·
                    rfl

theorem cell22_2717357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2717357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717357 prefixEnd_2717357 := by exact prefixLift 2717357
  have htrace : WordTrace (prefixWord ++ tailWord_2717357) baseStart_2717357 baseEnd_2717357 := by
    simpa [prefixWord, tailWord_2717357, baseEnd_2717357] using wordTrace_append hprefix tailTrace_2717357
  have hstable : (prefixWord ++ tailWord_2717357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717357).length < 2 ^ (prefixWord ++ tailWord_2717357).sum := by decide
  have hdescent : baseEnd_2717357 < baseStart_2717357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717372 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 1, 5]
def baseStart_2717372 : Nat := 118140960795 + 2717372 * 2 ^ 59
def prefixEnd_2717372 : Nat := 4983230072969 + 3 ^ 40 * 2717372 * 2
def baseEnd_2717372 : Nat := 930211968712965002168693

theorem tailTrace_2717372 : CollatzResearch.WordTrace tailWord_2717372 prefixEnd_2717372 930211968712965002168693 := by
  unfold tailWord_2717372
  simp only [CollatzResearch.WordTrace]
  refine ⟨49555349555716404517301185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66073799407621872689734913 49555349555716404517301185)
  ·
    refine ⟨37166512166787303387975889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49555349555716404517301185 37166512166787303387975889)
    ·
      refine ⟨27874884125090477540981917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37166512166787303387975889 27874884125090477540981917)
      ·
        refine ⟨10453081546908929077868219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27874884125090477540981917 10453081546908929077868219)
        ·
          refine ⟨15679622320363393616802329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10453081546908929077868219 15679622320363393616802329)
          ·
            refine ⟨11759716740272545212601747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15679622320363393616802329 11759716740272545212601747)
            ·
              refine ⟨17639575110408817818902621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11759716740272545212601747 17639575110408817818902621)
              ·
                refine ⟨6614840666403306682088483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17639575110408817818902621 6614840666403306682088483)
                ·
                  refine ⟨9922260999604960023132725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6614840666403306682088483 9922260999604960023132725)
                  ·
                    refine ⟨930211968712965002168693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9922260999604960023132725 930211968712965002168693)
                    ·
                      rfl

theorem cell22_2717372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 1, 5].length) (baseStart_2717372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717372 prefixEnd_2717372 := by exact prefixLift 2717372
  have htrace : WordTrace (prefixWord ++ tailWord_2717372) baseStart_2717372 baseEnd_2717372 := by
    simpa [prefixWord, tailWord_2717372, baseEnd_2717372] using wordTrace_append hprefix tailTrace_2717372
  have hstable : (prefixWord ++ tailWord_2717372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717372).length < 2 ^ (prefixWord ++ tailWord_2717372).sum := by decide
  have hdescent : baseEnd_2717372 < baseStart_2717372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717451 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 1, 3]
def baseStart_2717451 : Nat := 118140960795 + 2717451 * 2 ^ 59
def prefixEnd_2717451 : Nat := 4983230072969 + 3 ^ 40 * 2717451 * 2
def baseEnd_2717451 : Nat := 930239012027435129443451

theorem tailTrace_2717451 : CollatzResearch.WordTrace tailWord_2717451 prefixEnd_2717451 930239012027435129443451 := by
  unfold tailWord_2717451
  simp only [CollatzResearch.WordTrace]
  refine ⟨99113580478146605526728207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66075720318764403684485471 99113580478146605526728207)
  ·
    refine ⟨148670370717219908290092311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99113580478146605526728207 148670370717219908290092311)
    ·
      refine ⟨223005556075829862435138467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148670370717219908290092311 223005556075829862435138467)
      ·
        refine ⟨334508334113744793652707701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223005556075829862435138467 334508334113744793652707701)
        ·
          refine ⟨31360156323163574404941347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334508334113744793652707701 31360156323163574404941347)
          ·
            refine ⟨47040234484745361607412021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31360156323163574404941347 47040234484745361607412021)
            ·
              refine ⟨4410021982944877650694877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47040234484745361607412021 4410021982944877650694877)
              ·
                refine ⟨1653758243604329119010579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4410021982944877650694877 1653758243604329119010579)
                ·
                  refine ⟨2480637365406493678515869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653758243604329119010579 2480637365406493678515869)
                  ·
                    refine ⟨930239012027435129443451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480637365406493678515869 930239012027435129443451)
                    ·
                      rfl

theorem cell22_2717451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 3].length) (baseStart_2717451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717451 prefixEnd_2717451 := by exact prefixLift 2717451
  have htrace : WordTrace (prefixWord ++ tailWord_2717451) baseStart_2717451 baseEnd_2717451 := by
    simpa [prefixWord, tailWord_2717451, baseEnd_2717451] using wordTrace_append hprefix tailTrace_2717451
  have hstable : (prefixWord ++ tailWord_2717451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717451).length < 2 ^ (prefixWord ++ tailWord_2717451).sum := by decide
  have hdescent : baseEnd_2717451 < baseStart_2717451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717468 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 1, 3]
def baseStart_2717468 : Nat := 118140960795 + 2717468 * 2 ^ 59
def prefixEnd_2717468 : Nat := 4983230072969 + 3 ^ 40 * 2717468 * 2
def baseEnd_2717468 : Nat := 930244831474852751768399

theorem tailTrace_2717468 : CollatzResearch.WordTrace tailWord_2717468 prefixEnd_2717468 930244831474852751768399 := by
  unfold tailWord_2717468
  simp only [CollatzResearch.WordTrace]
  refine ⟨49557100259542508715048529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66076133679390011620064705 49557100259542508715048529)
  ·
    refine ⟨37167825194656881536286397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49557100259542508715048529 37167825194656881536286397)
    ·
      refine ⟨13937934447996330576107399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37167825194656881536286397 13937934447996330576107399)
      ·
        refine ⟨20906901671994495864161099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13937934447996330576107399 20906901671994495864161099)
        ·
          refine ⟨31360352507991743796241649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20906901671994495864161099 31360352507991743796241649)
          ·
            refine ⟨23520264380993807847181237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31360352507991743796241649 23520264380993807847181237)
            ·
              refine ⟨2205024785718169485673241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23520264380993807847181237 2205024785718169485673241)
              ·
                refine ⟨1653768589288627114254931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205024785718169485673241 1653768589288627114254931)
                ·
                  refine ⟨2480652883932940671382397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653768589288627114254931 2480652883932940671382397)
                  ·
                    refine ⟨930244831474852751768399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480652883932940671382397 930244831474852751768399)
                    ·
                      rfl

theorem cell22_2717468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_2717468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717468 prefixEnd_2717468 := by exact prefixLift 2717468
  have htrace : WordTrace (prefixWord ++ tailWord_2717468) baseStart_2717468 baseEnd_2717468 := by
    simpa [prefixWord, tailWord_2717468, baseEnd_2717468] using wordTrace_append hprefix tailTrace_2717468
  have hstable : (prefixWord ++ tailWord_2717468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717468).length < 2 ^ (prefixWord ++ tailWord_2717468).sum := by decide
  have hdescent : baseEnd_2717468 < baseStart_2717468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717507 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 3, 5]
def baseStart_2717507 : Nat := 118140960795 + 2717507 * 2 ^ 59
def prefixEnd_2717507 : Nat := 4983230072969 + 3 ^ 40 * 2717507 * 2
def baseEnd_2717507 : Nat := 930258181971869650043279

theorem tailTrace_2717507 : CollatzResearch.WordTrace tailWord_2717507 prefixEnd_2717507 930258181971869650043279 := by
  unfold tailWord_2717507
  simp only [CollatzResearch.WordTrace]
  refine ⟨99115622965943727090766775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66077081977295818060511183 99115622965943727090766775)
  ·
    refine ⟨148673434448915590636150163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99115622965943727090766775 148673434448915590636150163)
    ·
      refine ⟨223010151673373385954225245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148673434448915590636150163 223010151673373385954225245)
      ·
        refine ⟨83628806877515019732834467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 223010151673373385954225245 83628806877515019732834467)
        ·
          refine ⟨125443210316272529599251701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83628806877515019732834467 125443210316272529599251701)
          ·
            refine ⟨11760300967150549649929847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125443210316272529599251701 11760300967150549649929847)
            ·
              refine ⟨17640451450725824474894771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11760300967150549649929847 17640451450725824474894771)
              ·
                refine ⟨26460677176088736712342157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17640451450725824474894771 26460677176088736712342157)
                ·
                  refine ⟨9922753941033276267128309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26460677176088736712342157 9922753941033276267128309)
                  ·
                    refine ⟨930258181971869650043279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9922753941033276267128309 930258181971869650043279)
                    ·
                      rfl

theorem cell22_2717507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 5].length) (baseStart_2717507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717507 prefixEnd_2717507 := by exact prefixLift 2717507
  have htrace : WordTrace (prefixWord ++ tailWord_2717507) baseStart_2717507 baseEnd_2717507 := by
    simpa [prefixWord, tailWord_2717507, baseEnd_2717507] using wordTrace_append hprefix tailTrace_2717507
  have hstable : (prefixWord ++ tailWord_2717507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717507).length < 2 ^ (prefixWord ++ tailWord_2717507).sum := by decide
  have hdescent : baseEnd_2717507 < baseStart_2717507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717509 : List Nat := [1, 3, 1, 1, 1, 2, 4, 5, 4]
def baseStart_2717509 : Nat := 118140960795 + 2717509 * 2 ^ 59
def prefixEnd_2717509 : Nat := 4983230072969 + 3 ^ 40 * 2717509 * 2
def baseEnd_2717509 : Nat := 310086288870914103831091

theorem tailTrace_2717509 : CollatzResearch.WordTrace tailWord_2717509 prefixEnd_2717509 310086288870914103831091 := by
  unfold tailWord_2717509
  simp only [CollatzResearch.WordTrace]
  refine ⟨99115695911936481432339581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66077130607957654288226387 99115695911936481432339581)
  ·
    refine ⟨37168385966976180537127343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99115695911936481432339581 37168385966976180537127343)
    ·
      refine ⟨55752578950464270805691015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37168385966976180537127343 55752578950464270805691015)
      ·
        refine ⟨83628868425696406208536523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55752578950464270805691015 83628868425696406208536523)
        ·
          refine ⟨125443302638544609312804785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83628868425696406208536523 125443302638544609312804785)
          ·
            refine ⟨94082476978908456984603589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125443302638544609312804785 94082476978908456984603589)
            ·
              refine ⟨17640464433545335684613173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94082476978908456984603589 17640464433545335684613173)
              ·
                refine ⟨1653793540644875220432485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17640464433545335684613173 1653793540644875220432485)
                ·
                  refine ⟨310086288870914103831091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1653793540644875220432485 310086288870914103831091)
                  ·
                    rfl

theorem cell22_2717509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_2717509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717509 prefixEnd_2717509 := by exact prefixLift 2717509
  have htrace : WordTrace (prefixWord ++ tailWord_2717509) baseStart_2717509 baseEnd_2717509 := by
    simpa [prefixWord, tailWord_2717509, baseEnd_2717509] using wordTrace_append hprefix tailTrace_2717509
  have hstable : (prefixWord ++ tailWord_2717509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717509).length < 2 ^ (prefixWord ++ tailWord_2717509).sum := by decide
  have hdescent : baseEnd_2717509 < baseStart_2717509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717575 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 2, 3]
def baseStart_2717575 : Nat := 118140960795 + 2717575 * 2 ^ 59
def prefixEnd_2717575 : Nat := 4983230072969 + 3 ^ 40 * 2717575 * 2
def baseEnd_2717575 : Nat := 930281459761540139343071

theorem tailTrace_2717575 : CollatzResearch.WordTrace tailWord_2717575 prefixEnd_2717575 930281459761540139343071 := by
  unfold tailWord_2717575
  simp only [CollatzResearch.WordTrace]
  refine ⟨99118103129697374704242179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66078735419798249802828119 99118103129697374704242179)
  ·
    refine ⟨148677154694546062056363269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99118103129697374704242179 148677154694546062056363269)
    ·
      refine ⟨27876966505227386635568113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148677154694546062056363269 27876966505227386635568113)
      ·
        refine ⟨20907724878920539976676085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27876966505227386635568113 20907724878920539976676085)
        ·
          refine ⟨1960099207398800622813383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20907724878920539976676085 1960099207398800622813383)
          ·
            refine ⟨2940148811098200934220075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960099207398800622813383 2940148811098200934220075)
            ·
              refine ⟨4410223216647301401330113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940148811098200934220075 4410223216647301401330113)
              ·
                refine ⟨3307667412485476050997585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4410223216647301401330113 3307667412485476050997585)
                ·
                  refine ⟨2480750559364107038248189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3307667412485476050997585 2480750559364107038248189)
                  ·
                    refine ⟨930281459761540139343071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480750559364107038248189 930281459761540139343071)
                    ·
                      rfl

theorem cell22_2717575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_2717575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717575 prefixEnd_2717575 := by exact prefixLift 2717575
  have htrace : WordTrace (prefixWord ++ tailWord_2717575) baseStart_2717575 baseEnd_2717575 := by
    simpa [prefixWord, tailWord_2717575, baseEnd_2717575] using wordTrace_append hprefix tailTrace_2717575
  have hstable : (prefixWord ++ tailWord_2717575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717575).length < 2 ^ (prefixWord ++ tailWord_2717575).sum := by decide
  have hdescent : baseEnd_2717575 < baseStart_2717575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717627 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 10]
def baseStart_2717627 : Nat := 118140960795 + 2717627 * 2 ^ 59
def prefixEnd_2717627 : Nat := 4983230072969 + 3 ^ 40 * 2717627 * 2
def baseEnd_2717627 : Nat := 310099753474743112347637

theorem tailTrace_2717627 : CollatzResearch.WordTrace tailWord_2717627 prefixEnd_2717627 310099753474743112347637 := by
  unfold tailWord_2717627
  simp only [CollatzResearch.WordTrace]
  refine ⟨99119999725508987585135135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66079999817005991723423423 99119999725508987585135135)
  ·
    refine ⟨148679999588263481377702703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99119999725508987585135135 148679999588263481377702703)
    ·
      refine ⟨223019999382395222066554055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148679999588263481377702703 223019999382395222066554055)
      ·
        refine ⟨334529999073592833099831083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223019999382395222066554055 334529999073592833099831083)
        ·
          refine ⟨501794998610389249649746625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334529999073592833099831083 501794998610389249649746625)
          ·
            refine ⟨376346248957791937237309969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501794998610389249649746625 376346248957791937237309969)
            ·
              refine ⟨282259686718343952927982477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376346248957791937237309969 282259686718343952927982477)
              ·
                refine ⟨105847382519378982347993429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 282259686718343952927982477 105847382519378982347993429)
                ·
                  refine ⟨310099753474743112347637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 105847382519378982347993429 310099753474743112347637)
                  ·
                    rfl

theorem cell22_2717627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 10].length) (baseStart_2717627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717627 prefixEnd_2717627 := by exact prefixLift 2717627
  have htrace : WordTrace (prefixWord ++ tailWord_2717627) baseStart_2717627 baseEnd_2717627 := by
    simpa [prefixWord, tailWord_2717627, baseEnd_2717627] using wordTrace_append hprefix tailTrace_2717627
  have hstable : (prefixWord ++ tailWord_2717627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717627).length < 2 ^ (prefixWord ++ tailWord_2717627).sum := by decide
  have hdescent : baseEnd_2717627 < baseStart_2717627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717650 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 5]
def baseStart_2717650 : Nat := 118140960795 + 2717650 * 2 ^ 59
def prefixEnd_2717650 : Nat := 4983230072969 + 3 ^ 40 * 2717650 * 2
def baseEnd_2717650 : Nat := 310102377931421647905947

theorem tailTrace_2717650 : CollatzResearch.WordTrace tailWord_2717650 prefixEnd_2717650 310102377931421647905947 := by
  unfold tailWord_2717650
  simp only [CollatzResearch.WordTrace]
  refine ⟨24780209651106415628305601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66080559069617108342148269 24780209651106415628305601)
  ·
    refine ⟨18585157238329811721229201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24780209651106415628305601 18585157238329811721229201)
    ·
      refine ⟨13938867928747358790921901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18585157238329811721229201 13938867928747358790921901)
      ·
        refine ⟨5227075473280259546595713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13938867928747358790921901 5227075473280259546595713)
        ·
          refine ⟨3920306604960194659946785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5227075473280259546595713 3920306604960194659946785)
          ·
            refine ⟨2940229953720145994960089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3920306604960194659946785 2940229953720145994960089)
            ·
              refine ⟨2205172465290109496220067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2940229953720145994960089 2205172465290109496220067)
              ·
                refine ⟨3307758697935164244330101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2205172465290109496220067 3307758697935164244330101)
                ·
                  refine ⟨310102377931421647905947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3307758697935164244330101 310102377931421647905947)
                  ·
                    rfl

theorem cell22_2717650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_2717650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717650 prefixEnd_2717650 := by exact prefixLift 2717650
  have htrace : WordTrace (prefixWord ++ tailWord_2717650) baseStart_2717650 baseEnd_2717650 := by
    simpa [prefixWord, tailWord_2717650, baseEnd_2717650] using wordTrace_append hprefix tailTrace_2717650
  have hstable : (prefixWord ++ tailWord_2717650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717650).length < 2 ^ (prefixWord ++ tailWord_2717650).sum := by decide
  have hdescent : baseEnd_2717650 < baseStart_2717650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717663 : List Nat := [1, 1, 2, 3, 4, 3, 1, 2, 1, 4]
def baseStart_2717663 : Nat := 118140960795 + 2717663 * 2 ^ 59
def prefixEnd_2717663 : Nat := 4983230072969 + 3 ^ 40 * 2717663 * 2
def baseEnd_2717663 : Nat := 930311583959937243142801

theorem tailTrace_2717663 : CollatzResearch.WordTrace tailWord_2717663 prefixEnd_2717663 930311583959937243142801 := by
  unfold tailWord_2717663
  simp only [CollatzResearch.WordTrace]
  refine ⟨99121312753378565733445643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66080875168919043822297095 99121312753378565733445643)
  ·
    refine ⟨148681969130067848600168465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99121312753378565733445643 148681969130067848600168465)
    ·
      refine ⟨111511476847550886450126349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148681969130067848600168465 111511476847550886450126349)
      ·
        refine ⟨41816803817831582418797381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111511476847550886450126349 41816803817831582418797381)
        ·
          refine ⟨7840650715843421703524509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41816803817831582418797381 7840650715843421703524509)
          ·
            refine ⟨2940244018441283138821691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7840650715843421703524509 2940244018441283138821691)
            ·
              refine ⟨4410366027661924708232537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940244018441283138821691 4410366027661924708232537)
              ·
                refine ⟨3307774520746443531174403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4410366027661924708232537 3307774520746443531174403)
                ·
                  refine ⟨4961661781119665296761605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3307774520746443531174403 4961661781119665296761605)
                  ·
                    refine ⟨930311583959937243142801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4961661781119665296761605 930311583959937243142801)
                    ·
                      rfl

theorem cell22_2717663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 4].length) (baseStart_2717663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717663 prefixEnd_2717663 := by exact prefixLift 2717663
  have htrace : WordTrace (prefixWord ++ tailWord_2717663) baseStart_2717663 baseEnd_2717663 := by
    simpa [prefixWord, tailWord_2717663, baseEnd_2717663] using wordTrace_append hprefix tailTrace_2717663
  have hstable : (prefixWord ++ tailWord_2717663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717663).length < 2 ^ (prefixWord ++ tailWord_2717663).sum := by decide
  have hdescent : baseEnd_2717663 < baseStart_2717663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717751 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 5]
def baseStart_2717751 : Nat := 118140960795 + 2717751 * 2 ^ 59
def prefixEnd_2717751 : Nat := 4983230072969 + 3 ^ 40 * 2717751 * 2
def baseEnd_2717751 : Nat := 310113902719444782314177

theorem tailTrace_2717751 : CollatzResearch.WordTrace tailWord_2717751 prefixEnd_2717751 310113902719444782314177 := by
  unfold tailWord_2717751
  simp only [CollatzResearch.WordTrace]
  refine ⟨99124522377059756762649107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66083014918039837841766071 99124522377059756762649107)
  ·
    refine ⟨148686783565589635143973661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99124522377059756762649107 148686783565589635143973661)
    ·
      refine ⟨55757543837096113178990123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148686783565589635143973661 55757543837096113178990123)
      ·
        refine ⟨83636315755644169768485185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55757543837096113178990123 83636315755644169768485185)
        ·
          refine ⟨62727236816733127326363889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83636315755644169768485185 62727236816733127326363889)
          ·
            refine ⟨47045427612549845494772917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62727236816733127326363889 47045427612549845494772917)
            ·
              refine ⟨4410508838676548015134961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47045427612549845494772917 4410508838676548015134961)
              ·
                refine ⟨3307881629007411011351221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4410508838676548015134961 3307881629007411011351221)
                ·
                  refine ⟨310113902719444782314177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3307881629007411011351221 310113902719444782314177)
                  ·
                    rfl

theorem cell22_2717751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 5].length) (baseStart_2717751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717751 prefixEnd_2717751 := by exact prefixLift 2717751
  have htrace : WordTrace (prefixWord ++ tailWord_2717751) baseStart_2717751 baseEnd_2717751 := by
    simpa [prefixWord, tailWord_2717751, baseEnd_2717751] using wordTrace_append hprefix tailTrace_2717751
  have hstable : (prefixWord ++ tailWord_2717751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717751).length < 2 ^ (prefixWord ++ tailWord_2717751).sum := by decide
  have hdescent : baseEnd_2717751 < baseStart_2717751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717789 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2717789 : Nat := 118140960795 + 2717789 * 2 ^ 59
def prefixEnd_2717789 : Nat := 4983230072969 + 3 ^ 40 * 2717789 * 2
def baseEnd_2717789 : Nat := 930354716334914914492415

theorem tailTrace_2717789 : CollatzResearch.WordTrace tailWord_2717789 prefixEnd_2717789 930354716334914914492415 := by
  unfold tailWord_2717789
  simp only [CollatzResearch.WordTrace]
  refine ⟨99125908350922089252532421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66083938900614726168354947 99125908350922089252532421)
  ·
    refine ⟨18586107815797891734849829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99125908350922089252532421 18586107815797891734849829)
    ·
      refine ⟨3484895215462104700284343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18586107815797891734849829 3484895215462104700284343)
      ·
        refine ⟨5227342823193157050426515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484895215462104700284343 5227342823193157050426515)
        ·
          refine ⟨7841014234789735575639773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227342823193157050426515 7841014234789735575639773)
          ·
            refine ⟨2940380338046150840864915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7841014234789735575639773 2940380338046150840864915)
            ·
              refine ⟨4410570507069226261297373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940380338046150840864915 4410570507069226261297373)
              ·
                refine ⟨1653963940150959847986515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4410570507069226261297373 1653963940150959847986515)
                ·
                  refine ⟨2480945910226439771979773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1653963940150959847986515 2480945910226439771979773)
                  ·
                    refine ⟨930354716334914914492415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2480945910226439771979773 930354716334914914492415)
                    ·
                      rfl

theorem cell22_2717789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2717789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717789 prefixEnd_2717789 := by exact prefixLift 2717789
  have htrace : WordTrace (prefixWord ++ tailWord_2717789) baseStart_2717789 baseEnd_2717789 := by
    simpa [prefixWord, tailWord_2717789, baseEnd_2717789] using wordTrace_append hprefix tailTrace_2717789
  have hstable : (prefixWord ++ tailWord_2717789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717789).length < 2 ^ (prefixWord ++ tailWord_2717789).sum := by decide
  have hdescent : baseEnd_2717789 < baseStart_2717789 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717948 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 6]
def baseStart_2717948 : Nat := 118140960795 + 2717948 * 2 ^ 59
def prefixEnd_2717948 : Nat := 4983230072969 + 3 ^ 40 * 2717948 * 2
def baseEnd_2717948 : Nat := 310136381761430499922309

theorem tailTrace_2717948 : CollatzResearch.WordTrace tailWord_2717948 prefixEnd_2717948 310136381761430499922309 := by
  unfold tailWord_2717948
  simp only [CollatzResearch.WordTrace]
  refine ⟨49565853778673029703785249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66087805038230706271713665 49565853778673029703785249)
  ·
    refine ⟨37174390334004772277838937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49565853778673029703785249 37174390334004772277838937)
    ·
      refine ⟨27880792750503579208379203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37174390334004772277838937 27880792750503579208379203)
      ·
        refine ⟨41821189125755368812568805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27880792750503579208379203 41821189125755368812568805)
        ·
          refine ⟨7841472961079131652356651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41821189125755368812568805 7841472961079131652356651)
          ·
            refine ⟨11762209441618697478534977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7841472961079131652356651 11762209441618697478534977)
            ·
              refine ⟨8821657081214023108901233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11762209441618697478534977 8821657081214023108901233)
              ·
                refine ⟨6616242810910517331675925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8821657081214023108901233 6616242810910517331675925)
                ·
                  refine ⟨310136381761430499922309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6616242810910517331675925 310136381761430499922309)
                  ·
                    rfl

theorem cell22_2717948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 6].length) (baseStart_2717948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717948 prefixEnd_2717948 := by exact prefixLift 2717948
  have htrace : WordTrace (prefixWord ++ tailWord_2717948) baseStart_2717948 baseEnd_2717948 := by
    simpa [prefixWord, tailWord_2717948, baseEnd_2717948] using wordTrace_append hprefix tailTrace_2717948
  have hstable : (prefixWord ++ tailWord_2717948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717948).length < 2 ^ (prefixWord ++ tailWord_2717948).sum := by decide
  have hdescent : baseEnd_2717948 < baseStart_2717948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717963 : List Nat := [1, 1, 1, 1, 5, 2, 1, 1, 6, 3]
def baseStart_2717963 : Nat := 118140960795 + 2717963 * 2 ^ 59
def prefixEnd_2717963 : Nat := 4983230072969 + 3 ^ 40 * 2717963 * 2
def baseEnd_2717963 : Nat := 930414280090836460641881

theorem tailTrace_2717963 : CollatzResearch.WordTrace tailWord_2717963 prefixEnd_2717963 930414280090836460641881 := by
  unfold tailWord_2717963
  simp only [CollatzResearch.WordTrace]
  refine ⟨99132254652291716969366543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66088169768194477979577695 99132254652291716969366543)
  ·
    refine ⟨148698381978437575454049815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99132254652291716969366543 148698381978437575454049815)
    ·
      refine ⟨223047572967656363181074723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148698381978437575454049815 223047572967656363181074723)
      ·
        refine ⟨334571359451484544771612085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223047572967656363181074723 334571359451484544771612085)
        ·
          refine ⟨31366064948576676072338633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334571359451484544771612085 31366064948576676072338633)
          ·
            refine ⟨23524548711432507054253975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31366064948576676072338633 23524548711432507054253975)
            ·
              refine ⟨35286823067148760581380963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23524548711432507054253975 35286823067148760581380963)
              ·
                refine ⟨52930234600723140872071445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35286823067148760581380963 52930234600723140872071445)
                ·
                  refine ⟨2481104746908897228378349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 52930234600723140872071445 2481104746908897228378349)
                  ·
                    refine ⟨930414280090836460641881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481104746908897228378349 930414280090836460641881)
                    ·
                      rfl

theorem cell22_2717963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 6, 3].length) (baseStart_2717963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717963 prefixEnd_2717963 := by exact prefixLift 2717963
  have htrace : WordTrace (prefixWord ++ tailWord_2717963) baseStart_2717963 baseEnd_2717963 := by
    simpa [prefixWord, tailWord_2717963, baseEnd_2717963] using wordTrace_append hprefix tailTrace_2717963
  have hstable : (prefixWord ++ tailWord_2717963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717963).length < 2 ^ (prefixWord ++ tailWord_2717963).sum := by decide
  have hdescent : baseEnd_2717963 < baseStart_2717963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717980 : List Nat := [2, 2, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_2717980 : Nat := 118140960795 + 2717980 * 2 ^ 59
def prefixEnd_2717980 : Nat := 4983230072969 + 3 ^ 40 * 2717980 * 2
def baseEnd_2717980 : Nat := 930420099538254082966829

theorem tailTrace_2717980 : CollatzResearch.WordTrace tailWord_2717980 prefixEnd_2717980 930420099538254082966829 := by
  unfold tailWord_2717980
  simp only [CollatzResearch.WordTrace]
  refine ⟨49566437346615064436367697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66088583128820085915156929 49566437346615064436367697)
  ·
    refine ⟨37174828009961298327275773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49566437346615064436367697 37174828009961298327275773)
    ·
      refine ⟨13940560503735486872728415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37174828009961298327275773 13940560503735486872728415)
      ·
        refine ⟨20910840755603230309092623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940560503735486872728415 20910840755603230309092623)
        ·
          refine ⟨31366261133404845463638935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20910840755603230309092623 31366261133404845463638935)
          ·
            refine ⟨47049391700107268195458403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31366261133404845463638935 47049391700107268195458403)
            ·
              refine ⟨70574087550160902293187605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47049391700107268195458403 70574087550160902293187605)
              ·
                refine ⟨3308160353913792294993169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70574087550160902293187605 3308160353913792294993169)
                ·
                  refine ⟨2481120265435344221244877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308160353913792294993169 2481120265435344221244877)
                  ·
                    refine ⟨930420099538254082966829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481120265435344221244877 930420099538254082966829)
                    ·
                      rfl

theorem cell22_2717980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_2717980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717980 prefixEnd_2717980 := by exact prefixLift 2717980
  have htrace : WordTrace (prefixWord ++ tailWord_2717980) baseStart_2717980 baseEnd_2717980 := by
    simpa [prefixWord, tailWord_2717980, baseEnd_2717980] using wordTrace_append hprefix tailTrace_2717980
  have hstable : (prefixWord ++ tailWord_2717980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717980).length < 2 ^ (prefixWord ++ tailWord_2717980).sum := by decide
  have hdescent : baseEnd_2717980 < baseStart_2717980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2717982 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 6]
def baseStart_2717982 : Nat := 118140960795 + 2717982 * 2 ^ 59
def prefixEnd_2717982 : Nat := 4983230072969 + 3 ^ 40 * 2717982 * 2
def baseEnd_2717982 : Nat := 310140261393042248138941

theorem tailTrace_2717982 : CollatzResearch.WordTrace tailWord_2717982 prefixEnd_2717982 310140261393042248138941 := by
  unfold tailWord_2717982
  simp only [CollatzResearch.WordTrace]
  refine ⟨12391618454902860401788525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66088631759481922142872133 12391618454902860401788525)
  ·
    refine ⟨4646856920588572650670697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12391618454902860401788525 4646856920588572650670697)
    ·
      refine ⟨3485142690441429488003023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4646856920588572650670697 3485142690441429488003023)
      ·
        refine ⟨5227714035662144232004535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485142690441429488003023 5227714035662144232004535)
        ·
          refine ⟨7841571053493216348006803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5227714035662144232004535 7841571053493216348006803)
          ·
            refine ⟨11762356580239824522010205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7841571053493216348006803 11762356580239824522010205)
            ·
              refine ⟨4410883717589934195753827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11762356580239824522010205 4410883717589934195753827)
              ·
                refine ⟨6616325576384901293630741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4410883717589934195753827 6616325576384901293630741)
                ·
                  refine ⟨310140261393042248138941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6616325576384901293630741 310140261393042248138941)
                  ·
                    rfl

theorem cell22_2717982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_2717982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2717982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2717982 prefixEnd_2717982 := by exact prefixLift 2717982
  have htrace : WordTrace (prefixWord ++ tailWord_2717982) baseStart_2717982 baseEnd_2717982 := by
    simpa [prefixWord, tailWord_2717982, baseEnd_2717982] using wordTrace_append hprefix tailTrace_2717982
  have hstable : (prefixWord ++ tailWord_2717982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2717982).length < 2 ^ (prefixWord ++ tailWord_2717982).sum := by decide
  have hdescent : baseEnd_2717982 < baseStart_2717982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2717982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718044 : List Nat := [2, 2, 4, 3, 2, 1, 1, 7]
def baseStart_2718044 : Nat := 118140960795 + 2718044 * 2 ^ 59
def prefixEnd_2718044 : Nat := 4983230072969 + 3 ^ 40 * 2718044 * 2
def baseEnd_2718044 : Nat := 103382445338464361040737

theorem tailTrace_2718044 : CollatzResearch.WordTrace tailWord_2718044 prefixEnd_2718044 103382445338464361040737 := by
  unfold tailWord_2718044
  simp only [CollatzResearch.WordTrace]
  refine ⟨49567604482499133901532593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66090139309998845202043457 49567604482499133901532593)
  ·
    refine ⟨37175703361874350426149445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49567604482499133901532593 37175703361874350426149445)
    ·
      refine ⟨6970444380351440704903021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37175703361874350426149445 6970444380351440704903021)
      ·
        refine ⟨2613916642631790264338633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6970444380351440704903021 2613916642631790264338633)
        ·
          refine ⟨1960437481973842698253975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2613916642631790264338633 1960437481973842698253975)
          ·
            refine ⟨2940656222960764047380963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1960437481973842698253975 2940656222960764047380963)
            ·
              refine ⟨4410984334441146071071445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2940656222960764047380963 4410984334441146071071445)
              ·
                refine ⟨103382445338464361040737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4410984334441146071071445 103382445338464361040737)
                ·
                  rfl

theorem cell22_2718044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 7].length) (baseStart_2718044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718044 prefixEnd_2718044 := by exact prefixLift 2718044
  have htrace : WordTrace (prefixWord ++ tailWord_2718044) baseStart_2718044 baseEnd_2718044 := by
    simpa [prefixWord, tailWord_2718044, baseEnd_2718044] using wordTrace_append hprefix tailTrace_2718044
  have hstable : (prefixWord ++ tailWord_2718044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718044).length < 2 ^ (prefixWord ++ tailWord_2718044).sum := by decide
  have hdescent : baseEnd_2718044 < baseStart_2718044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718053 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 1, 7]
def baseStart_2718053 : Nat := 118140960795 + 2718053 * 2 ^ 59
def prefixEnd_2718053 : Nat := 4983230072969 + 3 ^ 40 * 2718053 * 2
def baseEnd_2718053 : Nat := 930445088930106225891605

theorem tailTrace_2718053 : CollatzResearch.WordTrace tailWord_2718053 prefixEnd_2718053 930445088930106225891605 := by
  unfold tailWord_2718053
  simp only [CollatzResearch.WordTrace]
  refine ⟨99135537221965662340142813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66090358147977108226761875 99135537221965662340142813)
  ·
    refine ⟨37175826458237123377553555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99135537221965662340142813 37175826458237123377553555)
    ·
      refine ⟨55763739687355685066330333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37175826458237123377553555 55763739687355685066330333)
      ·
        refine ⟨20911402382758381899873875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55763739687355685066330333 20911402382758381899873875)
        ·
          refine ⟨31367103574137572849810813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20911402382758381899873875 31367103574137572849810813)
          ·
            refine ⟨11762663840301589818679055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31367103574137572849810813 11762663840301589818679055)
            ·
              refine ⟨17643995760452384728018583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11762663840301589818679055 17643995760452384728018583)
              ·
                refine ⟨26465993640678577092027875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17643995760452384728018583 26465993640678577092027875)
                ·
                  refine ⟨39698990461017865638041813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26465993640678577092027875 39698990461017865638041813)
                  ·
                    refine ⟨930445088930106225891605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39698990461017865638041813 930445088930106225891605)
                    ·
                      rfl

theorem cell22_2718053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 7].length) (baseStart_2718053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718053 prefixEnd_2718053 := by exact prefixLift 2718053
  have htrace : WordTrace (prefixWord ++ tailWord_2718053) baseStart_2718053 baseEnd_2718053 := by
    simpa [prefixWord, tailWord_2718053, baseEnd_2718053] using wordTrace_append hprefix tailTrace_2718053
  have hstable : (prefixWord ++ tailWord_2718053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718053).length < 2 ^ (prefixWord ++ tailWord_2718053).sum := by decide
  have hdescent : baseEnd_2718053 < baseStart_2718053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718055 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 5]
def baseStart_2718055 : Nat := 118140960795 + 2718055 * 2 ^ 59
def prefixEnd_2718055 : Nat := 4983230072969 + 3 ^ 40 * 2718055 * 2
def baseEnd_2718055 : Nat := 310148591190326295780533

theorem tailTrace_2718055 : CollatzResearch.WordTrace tailWord_2718055 prefixEnd_2718055 310148591190326295780533 := by
  unfold tailWord_2718055
  simp only [CollatzResearch.WordTrace]
  refine ⟨99135610167958416681715619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66090406778638944454477079 99135610167958416681715619)
  ·
    refine ⟨148703415251937625022573429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99135610167958416681715619 148703415251937625022573429)
    ·
      refine ⟨13940945179869152345866259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148703415251937625022573429 13940945179869152345866259)
      ·
        refine ⟨20911417769803728518799389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13940945179869152345866259 20911417769803728518799389)
        ·
          refine ⟨7841781663676398194549771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20911417769803728518799389 7841781663676398194549771)
          ·
            refine ⟨11762672495514597291824657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7841781663676398194549771 11762672495514597291824657)
            ·
              refine ⟨8822004371635947968868493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11762672495514597291824657 8822004371635947968868493)
              ·
                refine ⟨3308251639363480488325685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8822004371635947968868493 3308251639363480488325685)
                ·
                  refine ⟨310148591190326295780533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3308251639363480488325685 310148591190326295780533)
                  ·
                    rfl

theorem cell22_2718055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 5].length) (baseStart_2718055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718055 prefixEnd_2718055 := by exact prefixLift 2718055
  have htrace : WordTrace (prefixWord ++ tailWord_2718055) baseStart_2718055 baseEnd_2718055 := by
    simpa [prefixWord, tailWord_2718055, baseEnd_2718055] using wordTrace_append hprefix tailTrace_2718055
  have hstable : (prefixWord ++ tailWord_2718055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718055).length < 2 ^ (prefixWord ++ tailWord_2718055).sum := by decide
  have hdescent : baseEnd_2718055 < baseStart_2718055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718115 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 1, 5]
def baseStart_2718115 : Nat := 118140960795 + 2718115 * 2 ^ 59
def prefixEnd_2718115 : Nat := 4983230072969 + 3 ^ 40 * 2718115 * 2
def baseEnd_2718115 : Nat := 930466312797158730841415

theorem tailTrace_2718115 : CollatzResearch.WordTrace tailWord_2718115 prefixEnd_2718115 930466312797158730841415 := by
  unfold tailWord_2718115
  simp only [CollatzResearch.WordTrace]
  refine ⟨99137798547741046928899799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66091865698494031285933199 99137798547741046928899799)
  ·
    refine ⟨148706697821611570393349699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99137798547741046928899799 148706697821611570393349699)
    ·
      refine ⟨223060046732417355590024549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148706697821611570393349699 223060046732417355590024549)
      ·
        refine ⟨41823758762328254173129603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223060046732417355590024549 41823758762328254173129603)
        ·
          refine ⟨62735638143492381259694405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41823758762328254173129603 62735638143492381259694405)
          ·
            refine ⟨11762932151904821486192701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62735638143492381259694405 11762932151904821486192701)
            ·
              refine ⟨4411099556964308057322263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11762932151904821486192701 4411099556964308057322263)
              ·
                refine ⟨6616649335446462085983395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411099556964308057322263 6616649335446462085983395)
                ·
                  refine ⟨9924974003169693128975093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6616649335446462085983395 9924974003169693128975093)
                  ·
                    refine ⟨930466312797158730841415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9924974003169693128975093 930466312797158730841415)
                    ·
                      rfl

theorem cell22_2718115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 5].length) (baseStart_2718115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718115 prefixEnd_2718115 := by exact prefixLift 2718115
  have htrace : WordTrace (prefixWord ++ tailWord_2718115) baseStart_2718115 baseEnd_2718115 := by
    simpa [prefixWord, tailWord_2718115, baseEnd_2718115] using wordTrace_append hprefix tailTrace_2718115
  have hstable : (prefixWord ++ tailWord_2718115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718115).length < 2 ^ (prefixWord ++ tailWord_2718115).sum := by decide
  have hdescent : baseEnd_2718115 < baseStart_2718115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718130 : List Nat := [3, 2, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_2718130 : Nat := 118140960795 + 2718130 * 2 ^ 59
def prefixEnd_2718130 : Nat := 4983230072969 + 3 ^ 40 * 2718130 * 2
def baseEnd_2718130 : Nat := 930471447603703691716369

theorem tailTrace_2718130 : CollatzResearch.WordTrace tailWord_2718130 prefixEnd_2718130 930471447603703691716369 := by
  unfold tailWord_2718130
  simp only [CollatzResearch.WordTrace]
  refine ⟨24784586410671676122673961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66092230428457802993797229 24784586410671676122673961)
  ·
    refine ⟨18588439808003757092005471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24784586410671676122673961 18588439808003757092005471)
    ·
      refine ⟨27882659712005635638008207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18588439808003757092005471 27882659712005635638008207)
      ·
        refine ⟨41823989568008453457012311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27882659712005635638008207 41823989568008453457012311)
        ·
          refine ⟨62735984352012680185518467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41823989568008453457012311 62735984352012680185518467)
          ·
            refine ⟨94103976528019020278277701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62735984352012680185518467 94103976528019020278277701)
            ·
              refine ⟨17644495599003566302177069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94103976528019020278277701 17644495599003566302177069)
              ·
                refine ⟨6616685849626337363316401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17644495599003566302177069 6616685849626337363316401)
                ·
                  refine ⟨4962514387219753022487301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6616685849626337363316401 4962514387219753022487301)
                  ·
                    refine ⟨930471447603703691716369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4962514387219753022487301 930471447603703691716369)
                    ·
                      rfl

theorem cell22_2718130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_2718130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718130 prefixEnd_2718130 := by exact prefixLift 2718130
  have htrace : WordTrace (prefixWord ++ tailWord_2718130) baseStart_2718130 baseEnd_2718130 := by
    simpa [prefixWord, tailWord_2718130, baseEnd_2718130] using wordTrace_append hprefix tailTrace_2718130
  have hstable : (prefixWord ++ tailWord_2718130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718130).length < 2 ^ (prefixWord ++ tailWord_2718130).sum := by decide
  have hdescent : baseEnd_2718130 < baseStart_2718130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718205 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2718205 : Nat := 118140960795 + 2718205 * 2 ^ 59
def prefixEnd_2718205 : Nat := 4983230072969 + 3 ^ 40 * 2718205 * 2
def baseEnd_2718205 : Nat := 930497121636428496091139

theorem tailTrace_2718205 : CollatzResearch.WordTrace tailWord_2718205 prefixEnd_2718205 930497121636428496091139 := by
  unfold tailWord_2718205
  simp only [CollatzResearch.WordTrace]
  refine ⟨99141081117414992299676069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66094054078276661533117379 99141081117414992299676069)
  ·
    refine ⟨18588952709515311056189263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99141081117414992299676069 18588952709515311056189263)
    ·
      refine ⟨27883429064272966584283895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18588952709515311056189263 27883429064272966584283895)
      ·
        refine ⟨41825143596409449876425843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27883429064272966584283895 41825143596409449876425843)
        ·
          refine ⟨62737715394614174814638765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41825143596409449876425843 62737715394614174814638765)
          ·
            refine ⟨23526643272980315555489537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62737715394614174814638765 23526643272980315555489537)
            ·
              refine ⟨17644982454735236666617153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23526643272980315555489537 17644982454735236666617153)
              ·
                refine ⟨13233736841051427499962865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17644982454735236666617153 13233736841051427499962865)
                ·
                  refine ⟨9925302630788570624972149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13233736841051427499962865 9925302630788570624972149)
                  ·
                    refine ⟨930497121636428496091139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9925302630788570624972149 930497121636428496091139)
                    ·
                      rfl

theorem cell22_2718205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2718205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718205 prefixEnd_2718205 := by exact prefixLift 2718205
  have htrace : WordTrace (prefixWord ++ tailWord_2718205) baseStart_2718205 baseEnd_2718205 := by
    simpa [prefixWord, tailWord_2718205, baseEnd_2718205] using wordTrace_append hprefix tailTrace_2718205
  have hstable : (prefixWord ++ tailWord_2718205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718205).length < 2 ^ (prefixWord ++ tailWord_2718205).sum := by decide
  have hdescent : baseEnd_2718205 < baseStart_2718205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718222 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 2, 5]
def baseStart_2718222 : Nat := 118140960795 + 2718222 * 2 ^ 59
def prefixEnd_2718222 : Nat := 4983230072969 + 3 ^ 40 * 2718222 * 2
def baseEnd_2718222 : Nat := 930502941083846118416087

theorem tailTrace_2718222 : CollatzResearch.WordTrace tailWord_2718222 prefixEnd_2718222 930502941083846118416087 := by
  unfold tailWord_2718222
  simp only [CollatzResearch.WordTrace]
  refine ⟨12392712644794175525380615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66094467438902269468696613 12392712644794175525380615)
  ·
    refine ⟨18589068967191263288070923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12392712644794175525380615 18589068967191263288070923)
    ·
      refine ⟨27883603450786894932106385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18589068967191263288070923 27883603450786894932106385)
      ·
        refine ⟨20912702588090171199079789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27883603450786894932106385 20912702588090171199079789)
        ·
          refine ⟨7842263470533814199654921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20912702588090171199079789 7842263470533814199654921)
          ·
            refine ⟨5881697602900360649741191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7842263470533814199654921 5881697602900360649741191)
            ·
              refine ⟨8822546404350540974611787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5881697602900360649741191 8822546404350540974611787)
              ·
                refine ⟨13233819606525811461917681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8822546404350540974611787 13233819606525811461917681)
                ·
                  refine ⟨9925364704894358596438261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13233819606525811461917681 9925364704894358596438261)
                  ·
                    refine ⟨930502941083846118416087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9925364704894358596438261 930502941083846118416087)
                    ·
                      rfl

theorem cell22_2718222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 5].length) (baseStart_2718222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718222 prefixEnd_2718222 := by exact prefixLift 2718222
  have htrace : WordTrace (prefixWord ++ tailWord_2718222) baseStart_2718222 baseEnd_2718222 := by
    simpa [prefixWord, tailWord_2718222, baseEnd_2718222] using wordTrace_append hprefix tailTrace_2718222
  have hstable : (prefixWord ++ tailWord_2718222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718222).length < 2 ^ (prefixWord ++ tailWord_2718222).sum := by decide
  have hdescent : baseEnd_2718222 < baseStart_2718222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718237 : List Nat := [1, 4, 2, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2718237 : Nat := 118140960795 + 2718237 * 2 ^ 59
def prefixEnd_2718237 : Nat := 4983230072969 + 3 ^ 40 * 2718237 * 2
def baseEnd_2718237 : Nat := 930508075890391079291041

theorem tailTrace_2718237 : CollatzResearch.WordTrace tailWord_2718237 prefixEnd_2718237 930508075890391079291041 := by
  unfold tailWord_2718237
  simp only [CollatzResearch.WordTrace]
  refine ⟨99142248253299061764840965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66094832168866041176560643 99142248253299061764840965)
  ·
    refine ⟨18589171547493574080907681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99142248253299061764840965 18589171547493574080907681)
    ·
      refine ⟨13941878660620180560680761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18589171547493574080907681 13941878660620180560680761)
      ·
        refine ⟨10456408995465135420510571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13941878660620180560680761 10456408995465135420510571)
        ·
          refine ⟨15684613493197703130765857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10456408995465135420510571 15684613493197703130765857)
          ·
            refine ⟨11763460119898277348074393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15684613493197703130765857 11763460119898277348074393)
            ·
              refine ⟨8822595089923708011055795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11763460119898277348074393 8822595089923708011055795)
              ·
                refine ⟨13233892634885562016583693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8822595089923708011055795 13233892634885562016583693)
                ·
                  refine ⟨4962709738082085756218885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13233892634885562016583693 4962709738082085756218885)
                  ·
                    refine ⟨930508075890391079291041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4962709738082085756218885 930508075890391079291041)
                    ·
                      rfl

theorem cell22_2718237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2718237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718237 prefixEnd_2718237 := by exact prefixLift 2718237
  have htrace : WordTrace (prefixWord ++ tailWord_2718237) baseStart_2718237 baseEnd_2718237 := by
    simpa [prefixWord, tailWord_2718237, baseEnd_2718237] using wordTrace_append hprefix tailTrace_2718237
  have hstable : (prefixWord ++ tailWord_2718237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718237).length < 2 ^ (prefixWord ++ tailWord_2718237).sum := by decide
  have hdescent : baseEnd_2718237 < baseStart_2718237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718269 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 4]
def baseStart_2718269 : Nat := 118140960795 + 2718269 * 2 ^ 59
def prefixEnd_2718269 : Nat := 4983230072969 + 3 ^ 40 * 2718269 * 2
def baseEnd_2718269 : Nat := 310173010048117887496981

theorem tailTrace_2718269 : CollatzResearch.WordTrace tailWord_2718269 prefixEnd_2718269 310173010048117887496981 := by
  unfold tailWord_2718269
  simp only [CollatzResearch.WordTrace]
  refine ⟨99143415389183131230005861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66095610259455420820003907 99143415389183131230005861)
  ·
    refine ⟨18589390385471837105626099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99143415389183131230005861 18589390385471837105626099)
    ·
      refine ⟨27884085578207755658439149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18589390385471837105626099 27884085578207755658439149)
      ·
        refine ⟨10456532091827908371914681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27884085578207755658439149 10456532091827908371914681)
        ·
          refine ⟨7842399068870931278936011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10456532091827908371914681 7842399068870931278936011)
          ·
            refine ⟨11763598603306396918404017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842399068870931278936011 11763598603306396918404017)
            ·
              refine ⟨8822698952479797688803013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11763598603306396918404017 8822698952479797688803013)
              ·
                refine ⟨1654256053589962066650565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8822698952479797688803013 1654256053589962066650565)
                ·
                  refine ⟨310173010048117887496981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654256053589962066650565 310173010048117887496981)
                  ·
                    rfl

theorem cell22_2718269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_2718269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718269 prefixEnd_2718269 := by exact prefixLift 2718269
  have htrace : WordTrace (prefixWord ++ tailWord_2718269) baseStart_2718269 baseEnd_2718269 := by
    simpa [prefixWord, tailWord_2718269, baseEnd_2718269] using wordTrace_append hprefix tailTrace_2718269
  have hstable : (prefixWord ++ tailWord_2718269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718269).length < 2 ^ (prefixWord ++ tailWord_2718269).sum := by decide
  have hdescent : baseEnd_2718269 < baseStart_2718269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718295 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 7]
def baseStart_2718295 : Nat := 118140960795 + 2718295 * 2 ^ 59
def prefixEnd_2718295 : Nat := 4983230072969 + 3 ^ 40 * 2718295 * 2
def baseEnd_2718295 : Nat := 930527930475698261340863

theorem tailTrace_2718295 : CollatzResearch.WordTrace tailWord_2718295 prefixEnd_2718295 930527930475698261340863 := by
  unfold tailWord_2718295
  simp only [CollatzResearch.WordTrace]
  refine ⟨99144363687088937670452339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66096242458059291780301559 99144363687088937670452339)
  ·
    refine ⟨148716545530633406505678509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99144363687088937670452339 148716545530633406505678509)
    ·
      refine ⟨55768704573987527439629441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148716545530633406505678509 55768704573987527439629441)
      ·
        refine ⟨41826528430490645579722081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55768704573987527439629441 41826528430490645579722081)
        ·
          refine ⟨31369896322867984184791561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41826528430490645579722081 31369896322867984184791561)
          ·
            refine ⟨23527422242150988138593671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31369896322867984184791561 23527422242150988138593671)
            ·
              refine ⟨35291133363226482207890507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23527422242150988138593671 35291133363226482207890507)
              ·
                refine ⟨52936700044839723311835761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35291133363226482207890507 52936700044839723311835761)
                ·
                  refine ⟨39702525033629792483876821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52936700044839723311835761 39702525033629792483876821)
                  ·
                    refine ⟨930527930475698261340863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39702525033629792483876821 930527930475698261340863)
                    ·
                      rfl

theorem cell22_2718295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_2718295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718295 prefixEnd_2718295 := by exact prefixLift 2718295
  have htrace : WordTrace (prefixWord ++ tailWord_2718295) baseStart_2718295 baseEnd_2718295 := by
    simpa [prefixWord, tailWord_2718295, baseEnd_2718295] using wordTrace_append hprefix tailTrace_2718295
  have hstable : (prefixWord ++ tailWord_2718295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718295).length < 2 ^ (prefixWord ++ tailWord_2718295).sum := by decide
  have hdescent : baseEnd_2718295 < baseStart_2718295 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718329 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 3, 3]
def baseStart_2718329 : Nat := 118140960795 + 2718329 * 2 ^ 59
def prefixEnd_2718329 : Nat := 4983230072969 + 3 ^ 40 * 2718329 * 2
def baseEnd_2718329 : Nat := 930539569370533505990759

theorem tailTrace_2718329 : CollatzResearch.WordTrace tailWord_2718329 prefixEnd_2718329 930539569370533505990759 := by
  unfold tailWord_2718329
  simp only [CollatzResearch.WordTrace]
  refine ⟨99145603768965761477190041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66097069179310507651460027 99145603768965761477190041)
  ·
    refine ⟨74359202826724321107892531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99145603768965761477190041 74359202826724321107892531)
    ·
      refine ⟨111538804240086481661838797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74359202826724321107892531 111538804240086481661838797)
      ·
        refine ⟨41827051590032430623189549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111538804240086481661838797 41827051590032430623189549)
        ·
          refine ⟨15685144346262161483696081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41827051590032430623189549 15685144346262161483696081)
          ·
            refine ⟨11763858259696621112772061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15685144346262161483696081 11763858259696621112772061)
            ·
              refine ⟨4411446847386232917289523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11763858259696621112772061 4411446847386232917289523)
              ·
                refine ⟨6617170271079349375934285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411446847386232917289523 6617170271079349375934285)
                ·
                  refine ⟨2481438851654756015975357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6617170271079349375934285 2481438851654756015975357)
                  ·
                    refine ⟨930539569370533505990759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481438851654756015975357 930539569370533505990759)
                    ·
                      rfl

theorem cell22_2718329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 3].length) (baseStart_2718329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718329 prefixEnd_2718329 := by exact prefixLift 2718329
  have htrace : WordTrace (prefixWord ++ tailWord_2718329) baseStart_2718329 baseEnd_2718329 := by
    simpa [prefixWord, tailWord_2718329, baseEnd_2718329] using wordTrace_append hprefix tailTrace_2718329
  have hstable : (prefixWord ++ tailWord_2718329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718329).length < 2 ^ (prefixWord ++ tailWord_2718329).sum := by decide
  have hdescent : baseEnd_2718329 < baseStart_2718329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718355 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 8]
def baseStart_2718355 : Nat := 118140960795 + 2718355 * 2 ^ 59
def prefixEnd_2718355 : Nat := 4983230072969 + 3 ^ 40 * 2718355 * 2
def baseEnd_2718355 : Nat := 930548469701878104840679

theorem tailTrace_2718355 : CollatzResearch.WordTrace tailWord_2718355 prefixEnd_2718355 930548469701878104840679 := by
  unfold tailWord_2718355
  simp only [CollatzResearch.WordTrace]
  refine ⟨99146552066871567917636519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66097701377914378611757679 99146552066871567917636519)
  ·
    refine ⟨148719828100307351876454779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99146552066871567917636519 148719828100307351876454779)
    ·
      refine ⟨223079742150461027814682169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148719828100307351876454779 223079742150461027814682169)
      ·
        refine ⟨167309806612845770861011627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223079742150461027814682169 167309806612845770861011627)
        ·
          refine ⟨250964709919268656291517441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167309806612845770861011627 250964709919268656291517441)
          ·
            refine ⟨188223532439451492218638081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250964709919268656291517441 188223532439451492218638081)
            ·
              refine ⟨141167649329588619163978561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188223532439451492218638081 141167649329588619163978561)
              ·
                refine ⟨105875736997191464372983921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141167649329588619163978561 105875736997191464372983921)
                ·
                  refine ⟨79406802747893598279737941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105875736997191464372983921 79406802747893598279737941)
                  ·
                    refine ⟨930548469701878104840679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79406802747893598279737941 930548469701878104840679)
                    ·
                      rfl

theorem cell22_2718355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 8].length) (baseStart_2718355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718355 prefixEnd_2718355 := by exact prefixLift 2718355
  have htrace : WordTrace (prefixWord ++ tailWord_2718355) baseStart_2718355 baseEnd_2718355 := by
    simpa [prefixWord, tailWord_2718355, baseEnd_2718355] using wordTrace_append hprefix tailTrace_2718355
  have hstable : (prefixWord ++ tailWord_2718355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718355).length < 2 ^ (prefixWord ++ tailWord_2718355).sum := by decide
  have hdescent : baseEnd_2718355 < baseStart_2718355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718389 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 3, 4]
def baseStart_2718389 : Nat := 118140960795 + 2718389 * 2 ^ 59
def prefixEnd_2718389 : Nat := 4983230072969 + 3 ^ 40 * 2718389 * 2
def baseEnd_2718389 : Nat := 930560108596713349490575

theorem tailTrace_2718389 : CollatzResearch.WordTrace tailWord_2718389 prefixEnd_2718389 930560108596713349490575 := by
  unfold tailWord_2718389
  simp only [CollatzResearch.WordTrace]
  refine ⟨99147792148748391724374221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66098528099165594482916147 99147792148748391724374221)
  ·
    refine ⟨37180422055780646896640333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99147792148748391724374221 37180422055780646896640333)
    ·
      refine ⟨13942658270917742586240125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37180422055780646896640333 13942658270917742586240125)
      ·
        refine ⟨5228496851594153469840047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13942658270917742586240125 5228496851594153469840047)
        ·
          refine ⟨7842745277391230204760071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228496851594153469840047 7842745277391230204760071)
          ·
            refine ⟨11764117916086845307140107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7842745277391230204760071 11764117916086845307140107)
            ·
              refine ⟨17646176874130267960710161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11764117916086845307140107 17646176874130267960710161)
              ·
                refine ⟨13234632655597700970532621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17646176874130267960710161 13234632655597700970532621)
                ·
                  refine ⟨4962987245849137863949733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13234632655597700970532621 4962987245849137863949733)
                  ·
                    refine ⟨930560108596713349490575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4962987245849137863949733 930560108596713349490575)
                    ·
                      rfl

theorem cell22_2718389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 4].length) (baseStart_2718389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718389 prefixEnd_2718389 := by exact prefixLift 2718389
  have htrace : WordTrace (prefixWord ++ tailWord_2718389) baseStart_2718389 baseEnd_2718389 := by
    simpa [prefixWord, tailWord_2718389, baseEnd_2718389] using wordTrace_append hprefix tailTrace_2718389
  have hstable : (prefixWord ++ tailWord_2718389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718389).length < 2 ^ (prefixWord ++ tailWord_2718389).sum := by decide
  have hdescent : baseEnd_2718389 < baseStart_2718389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718404 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 6]
def baseStart_2718404 : Nat := 118140960795 + 2718404 * 2 ^ 59
def prefixEnd_2718404 : Nat := 4983230072969 + 3 ^ 40 * 2718404 * 2
def baseEnd_2718404 : Nat := 310188414467752770121843

theorem tailTrace_2718404 : CollatzResearch.WordTrace tailWord_2718404 prefixEnd_2718404 310188414467752770121843 := by
  unfold tailWord_2718404
  simp only [CollatzResearch.WordTrace]
  refine ⟨49574169621847024643085133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66098892829129366190780177 49574169621847024643085133)
  ·
    refine ⟨18590313608192634241156925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49574169621847024643085133 18590313608192634241156925)
    ·
      refine ⟨6971367603072237840433847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18590313608192634241156925 6971367603072237840433847)
      ·
        refine ⟨10457051404608356760650771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971367603072237840433847 10457051404608356760650771)
        ·
          refine ⟨15685577106912535140976157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10457051404608356760650771 15685577106912535140976157)
          ·
            refine ⟨5882091415092200677866059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15685577106912535140976157 5882091415092200677866059)
            ·
              refine ⟨8823137122638301016799089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882091415092200677866059 8823137122638301016799089)
              ·
                refine ⟨6617352841978725762599317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8823137122638301016799089 6617352841978725762599317)
                ·
                  refine ⟨310188414467752770121843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6617352841978725762599317 310188414467752770121843)
                  ·
                    rfl

theorem cell22_2718404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_2718404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718404 prefixEnd_2718404 := by exact prefixLift 2718404
  have htrace : WordTrace (prefixWord ++ tailWord_2718404) baseStart_2718404 baseEnd_2718404 := by
    simpa [prefixWord, tailWord_2718404, baseEnd_2718404] using wordTrace_append hprefix tailTrace_2718404
  have hstable : (prefixWord ++ tailWord_2718404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718404).length < 2 ^ (prefixWord ++ tailWord_2718404).sum := by decide
  have hdescent : baseEnd_2718404 < baseStart_2718404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718417 : List Nat := [1, 2, 2, 1, 2, 3, 3, 1, 1, 6]
def baseStart_2718417 : Nat := 118140960795 + 2718417 * 2 ^ 59
def prefixEnd_2718417 : Nat := 4983230072969 + 3 ^ 40 * 2718417 * 2
def baseEnd_2718417 : Nat := 930569693568930609790489

theorem tailTrace_2718417 : CollatzResearch.WordTrace tailWord_2718417 prefixEnd_2718417 930569693568930609790489 := by
  unfold tailWord_2718417
  simp only [CollatzResearch.WordTrace]
  refine ⟨99148813392646952506393505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66099208928431301670929003 99148813392646952506393505)
  ·
    refine ⟨74361610044485214379795129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99148813392646952506393505 74361610044485214379795129)
    ·
      refine ⟨55771207533363910784846347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74361610044485214379795129 55771207533363910784846347)
      ·
        refine ⟨83656811300045866177269521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55771207533363910784846347 83656811300045866177269521)
        ·
          refine ⟨62742608475034399632952141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83656811300045866177269521 62742608475034399632952141)
          ·
            refine ⟨23528478178137899862357053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62742608475034399632952141 23528478178137899862357053)
            ·
              refine ⟨8823179316801712448383895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23528478178137899862357053 8823179316801712448383895)
              ·
                refine ⟨13234768975202568672575843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8823179316801712448383895 13234768975202568672575843)
                ·
                  refine ⟨19852153462803853008863765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13234768975202568672575843 19852153462803853008863765)
                  ·
                    refine ⟨930569693568930609790489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19852153462803853008863765 930569693568930609790489)
                    ·
                      rfl

theorem cell22_2718417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 6].length) (baseStart_2718417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718417 prefixEnd_2718417 := by exact prefixLift 2718417
  have htrace : WordTrace (prefixWord ++ tailWord_2718417) baseStart_2718417 baseEnd_2718417 := by
    simpa [prefixWord, tailWord_2718417, baseEnd_2718417] using wordTrace_append hprefix tailTrace_2718417
  have hstable : (prefixWord ++ tailWord_2718417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718417).length < 2 ^ (prefixWord ++ tailWord_2718417).sum := by decide
  have hdescent : baseEnd_2718417 < baseStart_2718417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718436 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_2718436 : Nat := 118140960795 + 2718436 * 2 ^ 59
def prefixEnd_2718436 : Nat := 4983230072969 + 3 ^ 40 * 2718436 * 2
def baseEnd_2718436 : Nat := 930576197657220893565431

theorem tailTrace_2718436 : CollatzResearch.WordTrace tailWord_2718436 prefixEnd_2718436 930576197657220893565431 := by
  unfold tailWord_2718436
  simp only [CollatzResearch.WordTrace]
  refine ⟨49574753189789059375667581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66099670919718745834223441 49574753189789059375667581)
  ·
    refine ⟨18590532446170897265875343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49574753189789059375667581 18590532446170897265875343)
    ·
      refine ⟨27885798669256345898813015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18590532446170897265875343 27885798669256345898813015)
      ·
        refine ⟨41828698003884518848219523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27885798669256345898813015 41828698003884518848219523)
        ·
          refine ⟨62743047005826778272329285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41828698003884518848219523 62743047005826778272329285)
          ·
            refine ⟨11764321313592520926061741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62743047005826778272329285 11764321313592520926061741)
            ·
              refine ⟨4411620492597195347273153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11764321313592520926061741 4411620492597195347273153)
              ·
                refine ⟨3308715369447896510454865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4411620492597195347273153 3308715369447896510454865)
                ·
                  refine ⟨2481536527085922382841149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308715369447896510454865 2481536527085922382841149)
                  ·
                    refine ⟨930576197657220893565431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481536527085922382841149 930576197657220893565431)
                    ·
                      rfl

theorem cell22_2718436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_2718436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718436 prefixEnd_2718436 := by exact prefixLift 2718436
  have htrace : WordTrace (prefixWord ++ tailWord_2718436) baseStart_2718436 baseEnd_2718436 := by
    simpa [prefixWord, tailWord_2718436, baseEnd_2718436] using wordTrace_append hprefix tailTrace_2718436
  have hstable : (prefixWord ++ tailWord_2718436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718436).length < 2 ^ (prefixWord ++ tailWord_2718436).sum := by decide
  have hdescent : baseEnd_2718436 < baseStart_2718436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718466 : List Nat := [3, 4, 1, 1, 1, 2, 4, 6]
def baseStart_2718466 : Nat := 118140960795 + 2718466 * 2 ^ 59
def prefixEnd_2718466 : Nat := 4983230072969 + 3 ^ 40 * 2718466 * 2
def baseEnd_2718466 : Nat := 103398496363367868368371

theorem tailTrace_2718466 : CollatzResearch.WordTrace tailWord_2718466 prefixEnd_2718466 103398496363367868368371 := by
  unfold tailWord_2718466
  simp only [CollatzResearch.WordTrace]
  refine ⟨24787650142367358468731813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66100400379646289249951501 24787650142367358468731813)
  ·
    refine ⟨4647684401693879712887215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24787650142367358468731813 4647684401693879712887215)
    ·
      refine ⟨6971526602540819569330823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4647684401693879712887215 6971526602540819569330823)
      ·
        refine ⟨10457289903811229353996235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971526602540819569330823 10457289903811229353996235)
        ·
          refine ⟨15685934855716844030994353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10457289903811229353996235 15685934855716844030994353)
          ·
            refine ⟨11764451141787633023245765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15685934855716844030994353 11764451141787633023245765)
            ·
              refine ⟨2205834589085181191858581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11764451141787633023245765 2205834589085181191858581)
              ·
                refine ⟨103398496363367868368371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2205834589085181191858581 103398496363367868368371)
                ·
                  rfl

theorem cell22_2718466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 6].length) (baseStart_2718466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718466 prefixEnd_2718466 := by exact prefixLift 2718466
  have htrace : WordTrace (prefixWord ++ tailWord_2718466) baseStart_2718466 baseEnd_2718466 := by
    simpa [prefixWord, tailWord_2718466, baseEnd_2718466] using wordTrace_append hprefix tailTrace_2718466
  have hstable : (prefixWord ++ tailWord_2718466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718466).length < 2 ^ (prefixWord ++ tailWord_2718466).sum := by decide
  have hdescent : baseEnd_2718466 < baseStart_2718466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718498 : List Nat := [3, 3, 1, 1, 2, 4, 1, 1, 3, 3]
def baseStart_2718498 : Nat := 118140960795 + 2718498 * 2 ^ 59
def prefixEnd_2718498 : Nat := 4983230072969 + 3 ^ 40 * 2718498 * 2
def baseEnd_2718498 : Nat := 930597421524273398515241

theorem tailTrace_2718498 : CollatzResearch.WordTrace tailWord_2718498 prefixEnd_2718498 930597421524273398515241 := by
  unfold tailWord_2718498
  simp only [CollatzResearch.WordTrace]
  refine ⟨24787941926338375835023037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66101178470235668893394765 24787941926338375835023037)
  ·
    refine ⟨9295478222376890938133639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24787941926338375835023037 9295478222376890938133639)
    ·
      refine ⟨13943217333565336407200459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9295478222376890938133639 13943217333565336407200459)
      ·
        refine ⟨20914826000348004610800689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13943217333565336407200459 20914826000348004610800689)
        ·
          refine ⟨15686119500261003458100517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20914826000348004610800689 15686119500261003458100517)
          ·
            refine ⟨2941147406298938148393847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15686119500261003458100517 2941147406298938148393847)
            ·
              refine ⟨4411721109448407222590771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941147406298938148393847 4411721109448407222590771)
              ·
                refine ⟨6617581664172610833886157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4411721109448407222590771 6617581664172610833886157)
                ·
                  refine ⟨2481593124064729062707309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6617581664172610833886157 2481593124064729062707309)
                  ·
                    refine ⟨930597421524273398515241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481593124064729062707309 930597421524273398515241)
                    ·
                      rfl

theorem cell22_2718498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 4, 1, 1, 3, 3].length) (baseStart_2718498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718498 prefixEnd_2718498 := by exact prefixLift 2718498
  have htrace : WordTrace (prefixWord ++ tailWord_2718498) baseStart_2718498 baseEnd_2718498 := by
    simpa [prefixWord, tailWord_2718498, baseEnd_2718498] using wordTrace_append hprefix tailTrace_2718498
  have hstable : (prefixWord ++ tailWord_2718498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718498).length < 2 ^ (prefixWord ++ tailWord_2718498).sum := by decide
  have hdescent : baseEnd_2718498 < baseStart_2718498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718571 : List Nat := [1, 1, 1, 1, 2, 2, 6, 3, 2, 3]
def baseStart_2718571 : Nat := 118140960795 + 2718571 * 2 ^ 59
def prefixEnd_2718571 : Nat := 4983230072969 + 3 ^ 40 * 2718571 * 2
def baseEnd_2718571 : Nat := 930622410916125541440017

theorem tailTrace_2718571 : CollatzResearch.WordTrace tailWord_2718571 prefixEnd_2718571 930622410916125541440017 := by
  unfold tailWord_2718571
  simp only [CollatzResearch.WordTrace]
  refine ⟨99154430234089036807499567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66102953489392691204999711 99154430234089036807499567)
  ·
    refine ⟨148731645351133555211249351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99154430234089036807499567 148731645351133555211249351)
    ·
      refine ⟨223097468026700332816874027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148731645351133555211249351 223097468026700332816874027)
      ·
        refine ⟨334646202040050499225311041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223097468026700332816874027 334646202040050499225311041)
        ·
          refine ⟨250984651530037874418983281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334646202040050499225311041 250984651530037874418983281)
          ·
            refine ⟨188238488647528405814237461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250984651530037874418983281 188238488647528405814237461)
            ·
              refine ⟨8823679155352894022542381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188238488647528405814237461 8823679155352894022542381)
              ·
                refine ⟨3308879683257335258453393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8823679155352894022542381 3308879683257335258453393)
                ·
                  refine ⟨2481659762443001443840045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3308879683257335258453393 2481659762443001443840045)
                  ·
                    refine ⟨930622410916125541440017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2481659762443001443840045 930622410916125541440017)
                    ·
                      rfl

theorem cell22_2718571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 3, 2, 3].length) (baseStart_2718571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718571 prefixEnd_2718571 := by exact prefixLift 2718571
  have htrace : WordTrace (prefixWord ++ tailWord_2718571) baseStart_2718571 baseEnd_2718571 := by
    simpa [prefixWord, tailWord_2718571, baseEnd_2718571] using wordTrace_append hprefix tailTrace_2718571
  have hstable : (prefixWord ++ tailWord_2718571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718571).length < 2 ^ (prefixWord ++ tailWord_2718571).sum := by decide
  have hdescent : baseEnd_2718571 < baseStart_2718571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718753 : List Nat := [1, 2, 3, 2, 3, 2, 3, 6]
def baseStart_2718753 : Nat := 118140960795 + 2718753 * 2 ^ 59
def prefixEnd_2718753 : Nat := 4983230072969 + 3 ^ 40 * 2718753 * 2
def baseEnd_2718753 : Nat := 103409412581726414821051

theorem tailTrace_2718753 : CollatzResearch.WordTrace tailWord_2718753 prefixEnd_2718753 103409412581726414821051 := by
  unfold tailWord_2718753
  simp only [CollatzResearch.WordTrace]
  refine ⟨99161068319429681890624913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66107378879619787927083275 99161068319429681890624913)
  ·
    refine ⟨74370801239572261417968685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99161068319429681890624913 74370801239572261417968685)
    ·
      refine ⟨27889050464839598031738257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74370801239572261417968685 27889050464839598031738257)
      ·
        refine ⟨20916787848629698523803693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27889050464839598031738257 20916787848629698523803693)
        ·
          refine ⟨7843795443236136946426385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20916787848629698523803693 7843795443236136946426385)
          ·
            refine ⟨5882846582427102709819789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7843795443236136946426385 5882846582427102709819789)
            ·
              refine ⟨2206067468410163516182421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5882846582427102709819789 2206067468410163516182421)
              ·
                refine ⟨103409412581726414821051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2206067468410163516182421 103409412581726414821051)
                ·
                  rfl

theorem cell22_2718753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 6].length) (baseStart_2718753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718753 prefixEnd_2718753 := by exact prefixLift 2718753
  have htrace : WordTrace (prefixWord ++ tailWord_2718753) baseStart_2718753 baseEnd_2718753 := by
    simpa [prefixWord, tailWord_2718753, baseEnd_2718753] using wordTrace_append hprefix tailTrace_2718753
  have hstable : (prefixWord ++ tailWord_2718753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718753).length < 2 ^ (prefixWord ++ tailWord_2718753).sum := by decide
  have hdescent : baseEnd_2718753 < baseStart_2718753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718828 : List Nat := [2, 2, 1, 1, 3, 2, 1, 5, 1, 4]
def baseStart_2718828 : Nat := 118140960795 + 2718828 * 2 ^ 59
def prefixEnd_2718828 : Nat := 4983230072969 + 3 ^ 40 * 2718828 * 2
def baseEnd_2718828 : Nat := 930710387268262537764229

theorem tailTrace_2718828 : CollatzResearch.WordTrace tailWord_2718828 prefixEnd_2718828 930710387268262537764229 := by
  unfold tailWord_2718828
  simp only [CollatzResearch.WordTrace]
  refine ⟨49581901897078984849802569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66109202529438646466403425 49581901897078984849802569)
  ·
    refine ⟨37186426422809238637351927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49581901897078984849802569 37186426422809238637351927)
    ·
      refine ⟨55779639634213857956027891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37186426422809238637351927 55779639634213857956027891)
      ·
        refine ⟨83669459451320786934041837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55779639634213857956027891 83669459451320786934041837)
        ·
          refine ⟨31376047294245295100265689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83669459451320786934041837 31376047294245295100265689)
          ·
            refine ⟨23532035470683971325199267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31376047294245295100265689 23532035470683971325199267)
            ·
              refine ⟨35298053206025956987798901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23532035470683971325199267 35298053206025956987798901)
              ·
                refine ⟨3309192488064933467606147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35298053206025956987798901 3309192488064933467606147)
                ·
                  refine ⟨4963788732097400201409221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309192488064933467606147 4963788732097400201409221)
                  ·
                    refine ⟨930710387268262537764229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963788732097400201409221 930710387268262537764229)
                    ·
                      rfl

theorem cell22_2718828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 4].length) (baseStart_2718828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718828 prefixEnd_2718828 := by exact prefixLift 2718828
  have htrace : WordTrace (prefixWord ++ tailWord_2718828) baseStart_2718828 baseEnd_2718828 := by
    simpa [prefixWord, tailWord_2718828, baseEnd_2718828] using wordTrace_append hprefix tailTrace_2718828
  have hstable : (prefixWord ++ tailWord_2718828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718828).length < 2 ^ (prefixWord ++ tailWord_2718828).sum := by decide
  have hdescent : baseEnd_2718828 < baseStart_2718828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718843 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 4]
def baseStart_2718843 : Nat := 118140960795 + 2718843 * 2 ^ 59
def prefixEnd_2718843 : Nat := 4983230072969 + 3 ^ 40 * 2718843 * 2
def baseEnd_2718843 : Nat := 310238507358269166213061

theorem tailTrace_2718843 : CollatzResearch.WordTrace tailWord_2718843 prefixEnd_2718843 310238507358269166213061 := by
  unfold tailWord_2718843
  simp only [CollatzResearch.WordTrace]
  refine ⟨99164350889103627261401183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66109567259402418174267455 99164350889103627261401183)
  ·
    refine ⟨148746526333655440892101775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99164350889103627261401183 148746526333655440892101775)
    ·
      refine ⟨223119789500483161338152663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148746526333655440892101775 223119789500483161338152663)
      ·
        refine ⟨334679684250724742007228995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223119789500483161338152663 334679684250724742007228995)
        ·
          refine ⟨502019526376087113010843493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334679684250724742007228995 502019526376087113010843493)
          ·
            refine ⟨94128661195516333689533155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 502019526376087113010843493 94128661195516333689533155)
            ·
              refine ⟨141192991793274500534299733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94128661195516333689533155 141192991793274500534299733)
              ·
                refine ⟨1654605372577435553136325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 141192991793274500534299733 1654605372577435553136325)
                ·
                  refine ⟨310238507358269166213061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1654605372577435553136325 310238507358269166213061)
                  ·
                    rfl

theorem cell22_2718843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 4].length) (baseStart_2718843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718843 prefixEnd_2718843 := by exact prefixLift 2718843
  have htrace : WordTrace (prefixWord ++ tailWord_2718843) baseStart_2718843 baseEnd_2718843 := by
    simpa [prefixWord, tailWord_2718843, baseEnd_2718843] using wordTrace_append hprefix tailTrace_2718843
  have hstable : (prefixWord ++ tailWord_2718843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718843).length < 2 ^ (prefixWord ++ tailWord_2718843).sum := by decide
  have hdescent : baseEnd_2718843 < baseStart_2718843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718858 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 1, 5]
def baseStart_2718858 : Nat := 118140960795 + 2718858 * 2 ^ 59
def prefixEnd_2718858 : Nat := 4983230072969 + 3 ^ 40 * 2718858 * 2
def baseEnd_2718858 : Nat := 930720656881352459514137

theorem tailTrace_2718858 : CollatzResearch.WordTrace tailWord_2718858 prefixEnd_2718858 930720656881352459514137 := by
  unfold tailWord_2718858
  simp only [CollatzResearch.WordTrace]
  refine ⟨24791224496012321205799307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66109931989366189882131485 24791224496012321205799307)
  ·
    refine ⟨37186836744018481808698961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24791224496012321205799307 37186836744018481808698961)
    ·
      refine ⟨27890127558013861356524221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37186836744018481808698961 27890127558013861356524221)
      ·
        refine ⟨10458797834255198008696583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27890127558013861356524221 10458797834255198008696583)
        ·
          refine ⟨15688196751382797013044875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10458797834255198008696583 15688196751382797013044875)
          ·
            refine ⟨23532295127074195519567313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15688196751382797013044875 23532295127074195519567313)
            ·
              refine ⟨17649221345305646639675485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23532295127074195519567313 17649221345305646639675485)
              ·
                refine ⟨6618458004489617489878307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17649221345305646639675485 6618458004489617489878307)
                ·
                  refine ⟨9927687006734426234817461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6618458004489617489878307 9927687006734426234817461)
                  ·
                    refine ⟨930720656881352459514137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9927687006734426234817461 930720656881352459514137)
                    ·
                      rfl

theorem cell22_2718858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_2718858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718858 prefixEnd_2718858 := by exact prefixLift 2718858
  have htrace : WordTrace (prefixWord ++ tailWord_2718858) baseStart_2718858 baseEnd_2718858 := by
    simpa [prefixWord, tailWord_2718858, baseEnd_2718858] using wordTrace_append hprefix tailTrace_2718858
  have hstable : (prefixWord ++ tailWord_2718858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718858).length < 2 ^ (prefixWord ++ tailWord_2718858).sum := by decide
  have hdescent : baseEnd_2718858 < baseStart_2718858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718862 : List Nat := [4, 1, 1, 3, 2, 3, 1, 2, 1, 4]
def baseStart_2718862 : Nat := 118140960795 + 2718862 * 2 ^ 59
def prefixEnd_2718862 : Nat := 4983230072969 + 3 ^ 40 * 2718862 * 2
def baseEnd_2718862 : Nat := 930722026163097782414125

theorem tailTrace_2718862 : CollatzResearch.WordTrace tailWord_2718862 prefixEnd_2718862 930722026163097782414125 := by
  unfold tailWord_2718862
  simp only [CollatzResearch.WordTrace]
  refine ⟨12395630484504349188292855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66110029250689862337561893 12395630484504349188292855)
  ·
    refine ⟨18593445726756523782439283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12395630484504349188292855 18593445726756523782439283)
    ·
      refine ⟨27890168590134785673658925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18593445726756523782439283 27890168590134785673658925)
      ·
        refine ⟨10458813221300544627622097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27890168590134785673658925 10458813221300544627622097)
        ·
          refine ⟨7844109915975408470716573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10458813221300544627622097 7844109915975408470716573)
          ·
            refine ⟨2941541218490778176518715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7844109915975408470716573 2941541218490778176518715)
            ·
              refine ⟨4412311827736167264778073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941541218490778176518715 4412311827736167264778073)
              ·
                refine ⟨3309233870802125448583555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4412311827736167264778073 3309233870802125448583555)
                ·
                  refine ⟨4963850806203188172875333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309233870802125448583555 4963850806203188172875333)
                  ·
                    refine ⟨930722026163097782414125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4963850806203188172875333 930722026163097782414125)
                    ·
                      rfl

theorem cell22_2718862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 1, 4].length) (baseStart_2718862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718862 prefixEnd_2718862 := by exact prefixLift 2718862
  have htrace : WordTrace (prefixWord ++ tailWord_2718862) baseStart_2718862 baseEnd_2718862 := by
    simpa [prefixWord, tailWord_2718862, baseEnd_2718862] using wordTrace_append hprefix tailTrace_2718862
  have hstable : (prefixWord ++ tailWord_2718862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718862).length < 2 ^ (prefixWord ++ tailWord_2718862).sum := by decide
  have hdescent : baseEnd_2718862 < baseStart_2718862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718948 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2718948 : Nat := 118140960795 + 2718948 * 2 ^ 59
def prefixEnd_2718948 : Nat := 4983230072969 + 3 ^ 40 * 2718948 * 2
def baseEnd_2718948 : Nat := 930751465720622224763861

theorem tailTrace_2718948 : CollatzResearch.WordTrace tailWord_2718948 prefixEnd_2718948 930751465720622224763861 := by
  unfold tailWord_2718948
  simp only [CollatzResearch.WordTrace]
  refine ⟨49584090276861615096986749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66112120369148820129315665 49584090276861615096986749)
  ·
    refine ⟨18594033853823105661370031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49584090276861615096986749 18594033853823105661370031)
    ·
      refine ⟨27891050780734658492055047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18594033853823105661370031 27891050780734658492055047)
      ·
        refine ⟨41836576171101987738082571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27891050780734658492055047 41836576171101987738082571)
        ·
          refine ⟨62754864256652981607123857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41836576171101987738082571 62754864256652981607123857)
          ·
            refine ⟨47066148192489736205342893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62754864256652981607123857 47066148192489736205342893)
            ·
              refine ⟨17649805572183651077003585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47066148192489736205342893 17649805572183651077003585)
              ·
                refine ⟨13237354179137738307752689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17649805572183651077003585 13237354179137738307752689)
                ·
                  refine ⟨9928015634353303730814517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13237354179137738307752689 9928015634353303730814517)
                  ·
                    refine ⟨930751465720622224763861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9928015634353303730814517 930751465720622224763861)
                    ·
                      rfl

theorem cell22_2718948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2718948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718948 prefixEnd_2718948 := by exact prefixLift 2718948
  have htrace : WordTrace (prefixWord ++ tailWord_2718948) baseStart_2718948 baseEnd_2718948 := by
    simpa [prefixWord, tailWord_2718948, baseEnd_2718948] using wordTrace_append hprefix tailTrace_2718948
  have hstable : (prefixWord ++ tailWord_2718948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718948).length < 2 ^ (prefixWord ++ tailWord_2718948).sum := by decide
  have hdescent : baseEnd_2718948 < baseStart_2718948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2718993 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 3, 5]
def baseStart_2718993 : Nat := 118140960795 + 2718993 * 2 ^ 59
def prefixEnd_2718993 : Nat := 4983230072969 + 3 ^ 40 * 2718993 * 2
def baseEnd_2718993 : Nat := 930766870140257107388723

theorem tailTrace_2718993 : CollatzResearch.WordTrace tailWord_2718993 prefixEnd_2718993 930766870140257107388723 := by
  unfold tailWord_2718993
  simp only [CollatzResearch.WordTrace]
  refine ⟨99169821838560202879361633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66113214559040135252907755 99169821838560202879361633)
  ·
    refine ⟨74377366378920152159521225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99169821838560202879361633 74377366378920152159521225)
    ·
      refine ⟨55783024784190114119640919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74377366378920152159521225 55783024784190114119640919)
      ·
        refine ⟨83674537176285171179461379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55783024784190114119640919 83674537176285171179461379)
        ·
          refine ⟨125511805764427756769192069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83674537176285171179461379 125511805764427756769192069)
          ·
            refine ⟨23533463580830204394223513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125511805764427756769192069 23533463580830204394223513)
            ·
              refine ⟨17650097685622653295667635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23533463580830204394223513 17650097685622653295667635)
              ·
                refine ⟨26475146528433979943501453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17650097685622653295667635 26475146528433979943501453)
                ·
                  refine ⟨9928179948162742478813045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26475146528433979943501453 9928179948162742478813045)
                  ·
                    refine ⟨930766870140257107388723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9928179948162742478813045 930766870140257107388723)
                    ·
                      rfl

theorem cell22_2718993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 5].length) (baseStart_2718993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2718993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2718993 prefixEnd_2718993 := by exact prefixLift 2718993
  have htrace : WordTrace (prefixWord ++ tailWord_2718993) baseStart_2718993 baseEnd_2718993 := by
    simpa [prefixWord, tailWord_2718993, baseEnd_2718993] using wordTrace_append hprefix tailTrace_2718993
  have hstable : (prefixWord ++ tailWord_2718993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2718993).length < 2 ^ (prefixWord ++ tailWord_2718993).sum := by decide
  have hdescent : baseEnd_2718993 < baseStart_2718993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2718993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719027 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 2, 3]
def baseStart_2719027 : Nat := 118140960795 + 2719027 * 2 ^ 59
def prefixEnd_2719027 : Nat := 4983230072969 + 3 ^ 40 * 2719027 * 2
def baseEnd_2719027 : Nat := 930778509035092352038619

theorem tailTrace_2719027 : CollatzResearch.WordTrace tailWord_2719027 prefixEnd_2719027 930778509035092352038619 := by
  unfold tailWord_2719027
  simp only [CollatzResearch.WordTrace]
  refine ⟨99171061920437026686099335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66114041280291351124066223 99171061920437026686099335)
  ·
    refine ⟨148756592880655540029149003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99171061920437026686099335 148756592880655540029149003)
    ·
      refine ⟨223134889320983310043723505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148756592880655540029149003 223134889320983310043723505)
      ·
        refine ⟨167351166990737482532792629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223134889320983310043723505 167351166990737482532792629)
        ·
          refine ⟨15689171905381638987449309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167351166990737482532792629 15689171905381638987449309)
          ·
            refine ⟨5883439464518114620293491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15689171905381638987449309 5883439464518114620293491)
            ·
              refine ⟨8825159196777171930440237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5883439464518114620293491 8825159196777171930440237)
              ·
                refine ⟨3309434698791439473915089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8825159196777171930440237 3309434698791439473915089)
                ·
                  refine ⟨2482076024093579605436317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3309434698791439473915089 2482076024093579605436317)
                  ·
                    refine ⟨930778509035092352038619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482076024093579605436317 930778509035092352038619)
                    ·
                      rfl

theorem cell22_2719027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 3].length) (baseStart_2719027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719027 prefixEnd_2719027 := by exact prefixLift 2719027
  have htrace : WordTrace (prefixWord ++ tailWord_2719027) baseStart_2719027 baseEnd_2719027 := by
    simpa [prefixWord, tailWord_2719027, baseEnd_2719027] using wordTrace_append hprefix tailTrace_2719027
  have hstable : (prefixWord ++ tailWord_2719027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719027).length < 2 ^ (prefixWord ++ tailWord_2719027).sum := by decide
  have hdescent : baseEnd_2719027 < baseStart_2719027 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719149 : List Nat := [1, 5, 2, 2, 1, 1, 1, 4, 1, 4]
def baseStart_2719149 : Nat := 118140960795 + 2719149 * 2 ^ 59
def prefixEnd_2719149 : Nat := 4983230072969 + 3 ^ 40 * 2719149 * 2
def baseEnd_2719149 : Nat := 930820272128324700488245

theorem tailTrace_2719149 : CollatzResearch.WordTrace tailWord_2719149 prefixEnd_2719149 930820272128324700488245 := by
  unfold tailWord_2719149
  simp only [CollatzResearch.WordTrace]
  refine ⟨99175511625995041522040501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66117007750663361014693667 99175511625995041522040501)
  ·
    refine ⟨9297704214937035142691297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99175511625995041522040501 9297704214937035142691297)
    ·
      refine ⟨6973278161202776357018473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9297704214937035142691297 6973278161202776357018473)
      ·
        refine ⟨5229958620902082267763855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6973278161202776357018473 5229958620902082267763855)
        ·
          refine ⟨7844937931353123401645783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229958620902082267763855 7844937931353123401645783)
          ·
            refine ⟨11767406897029685102468675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7844937931353123401645783 11767406897029685102468675)
            ·
              refine ⟨17651110345544527653703013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11767406897029685102468675 17651110345544527653703013)
              ·
                refine ⟨3309583189789598935069315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17651110345544527653703013 3309583189789598935069315)
                ·
                  refine ⟨4964374784684398402603973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3309583189789598935069315 4964374784684398402603973)
                  ·
                    refine ⟨930820272128324700488245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4964374784684398402603973 930820272128324700488245)
                    ·
                      rfl

theorem cell22_2719149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_2719149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719149 prefixEnd_2719149 := by exact prefixLift 2719149
  have htrace : WordTrace (prefixWord ++ tailWord_2719149) baseStart_2719149 baseEnd_2719149 := by
    simpa [prefixWord, tailWord_2719149, baseEnd_2719149] using wordTrace_append hprefix tailTrace_2719149
  have hstable : (prefixWord ++ tailWord_2719149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719149).length < 2 ^ (prefixWord ++ tailWord_2719149).sum := by decide
  have hdescent : baseEnd_2719149 < baseStart_2719149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719160 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 1, 6]
def baseStart_2719160 : Nat := 118140960795 + 2719160 * 2 ^ 59
def prefixEnd_2719160 : Nat := 4983230072969 + 3 ^ 40 * 2719160 * 2
def baseEnd_2719160 : Nat := 930824037653124338463211

theorem tailTrace_2719160 : CollatzResearch.WordTrace tailWord_2719160 prefixEnd_2719160 930824037653124338463211 := by
  unfold tailWord_2719160
  simp only [CollatzResearch.WordTrace]
  refine ⟨49587956414477595200345467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66117275219303460267127289 49587956414477595200345467)
  ·
    refine ⟨74381934621716392800518201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49587956414477595200345467 74381934621716392800518201)
    ·
      refine ⟨55786450966287294600388651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74381934621716392800518201 55786450966287294600388651)
      ·
        refine ⟨83679676449430941900582977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55786450966287294600388651 83679676449430941900582977)
        ·
          refine ⟨62759757337073206425437233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83679676449430941900582977 62759757337073206425437233)
          ·
            refine ⟨47069818002804904819077925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62759757337073206425437233 47069818002804904819077925)
            ·
              refine ⟨8825590875525919653577111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47069818002804904819077925 8825590875525919653577111)
              ·
                refine ⟨13238386313288879480365667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8825590875525919653577111 13238386313288879480365667)
                ·
                  refine ⟨19857579469933319220548501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13238386313288879480365667 19857579469933319220548501)
                  ·
                    refine ⟨930824037653124338463211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19857579469933319220548501 930824037653124338463211)
                    ·
                      rfl

theorem cell22_2719160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 6].length) (baseStart_2719160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719160 prefixEnd_2719160 := by exact prefixLift 2719160
  have htrace : WordTrace (prefixWord ++ tailWord_2719160) baseStart_2719160 baseEnd_2719160 := by
    simpa [prefixWord, tailWord_2719160, baseEnd_2719160] using wordTrace_append hprefix tailTrace_2719160
  have hstable : (prefixWord ++ tailWord_2719160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719160).length < 2 ^ (prefixWord ++ tailWord_2719160).sum := by decide
  have hdescent : baseEnd_2719160 < baseStart_2719160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719262 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2719262 : Nat := 118140960795 + 2719262 * 2 ^ 59
def prefixEnd_2719262 : Nat := 4983230072969 + 3 ^ 40 * 2719262 * 2
def baseEnd_2719262 : Nat := 930858954337630072412899

theorem tailTrace_2719262 : CollatzResearch.WordTrace tailWord_2719262 prefixEnd_2719262 930858954337630072412899 := by
  unfold tailWord_2719262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12397454134323207727613005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66119755383057107880602693 12397454134323207727613005)
  ·
    refine ⟨4649045300371202897854877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12397454134323207727613005 4649045300371202897854877)
    ·
      refine ⟨1743391987639201086695579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4649045300371202897854877 1743391987639201086695579)
      ·
        refine ⟨2615087981458801630043369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1743391987639201086695579 2615087981458801630043369)
        ·
          refine ⟨1961315986094101222532527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615087981458801630043369 1961315986094101222532527)
          ·
            refine ⟨2941973979141151833798791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961315986094101222532527 2941973979141151833798791)
            ·
              refine ⟨4412960968711727750698187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2941973979141151833798791 4412960968711727750698187)
              ·
                refine ⟨6619441453067591626047281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4412960968711727750698187 6619441453067591626047281)
                ·
                  refine ⟨4964581089800693719535461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6619441453067591626047281 4964581089800693719535461)
                  ·
                    refine ⟨930858954337630072412899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4964581089800693719535461 930858954337630072412899)
                    ·
                      rfl

theorem cell22_2719262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2719262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719262 prefixEnd_2719262 := by exact prefixLift 2719262
  have htrace : WordTrace (prefixWord ++ tailWord_2719262) baseStart_2719262 baseEnd_2719262 := by
    simpa [prefixWord, tailWord_2719262, baseEnd_2719262] using wordTrace_append hprefix tailTrace_2719262
  have hstable : (prefixWord ++ tailWord_2719262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719262).length < 2 ^ (prefixWord ++ tailWord_2719262).sum := by decide
  have hdescent : baseEnd_2719262 < baseStart_2719262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719314 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 1, 5]
def baseStart_2719314 : Nat := 118140960795 + 2719314 * 2 ^ 59
def prefixEnd_2719314 : Nat := 4983230072969 + 3 ^ 40 * 2719314 * 2
def baseEnd_2719314 : Nat := 930876755000319270112739

theorem tailTrace_2719314 : CollatzResearch.WordTrace tailWord_2719314 prefixEnd_2719314 930876755000319270112739 := by
  unfold tailWord_2719314
  simp only [CollatzResearch.WordTrace]
  refine ⟨24795382417599318675449249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66121019780264849801197997 24795382417599318675449249)
  ·
    refine ⟨18596536813199489006586937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24795382417599318675449249 18596536813199489006586937)
    ·
      refine ⟨13947402609899616754940203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18596536813199489006586937 13947402609899616754940203)
      ·
        refine ⟨20921103914849425132410305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13947402609899616754940203 20921103914849425132410305)
        ·
          refine ⟨15690827936137068849307729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20921103914849425132410305 15690827936137068849307729)
          ·
            refine ⟨11768120952102801636980797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15690827936137068849307729 11768120952102801636980797)
            ·
              refine ⟨4413045357038550613867799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11768120952102801636980797 4413045357038550613867799)
              ·
                refine ⟨6619568035557825920801699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413045357038550613867799 6619568035557825920801699)
                ·
                  refine ⟨9929352053336738881202549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6619568035557825920801699 9929352053336738881202549)
                  ·
                    refine ⟨930876755000319270112739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9929352053336738881202549 930876755000319270112739)
                    ·
                      rfl

theorem cell22_2719314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_2719314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719314 prefixEnd_2719314 := by exact prefixLift 2719314
  have htrace : WordTrace (prefixWord ++ tailWord_2719314) baseStart_2719314 baseEnd_2719314 := by
    simpa [prefixWord, tailWord_2719314, baseEnd_2719314] using wordTrace_append hprefix tailTrace_2719314
  have hstable : (prefixWord ++ tailWord_2719314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719314).length < 2 ^ (prefixWord ++ tailWord_2719314).sum := by decide
  have hdescent : baseEnd_2719314 < baseStart_2719314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719449 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 1, 5]
def baseStart_2719449 : Nat := 118140960795 + 2719449 * 2 ^ 59
def prefixEnd_2719449 : Nat := 4983230072969 + 3 ^ 40 * 2719449 * 2
def baseEnd_2719449 : Nat := 930922968259223917987325

theorem tailTrace_2719449 : CollatzResearch.WordTrace tailWord_2719449 prefixEnd_2719449 930922968259223917987325 := by
  unfold tailWord_2719449
  simp only [CollatzResearch.WordTrace]
  refine ⟨99186453524908192757961401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66124302349938795171974267 99186453524908192757961401)
  ·
    refine ⟨74389840143681144568471051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99186453524908192757961401 74389840143681144568471051)
    ·
      refine ⟨111584760215521716852706577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74389840143681144568471051 111584760215521716852706577)
      ·
        refine ⟨83688570161641287639529933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111584760215521716852706577 83688570161641287639529933)
        ·
          refine ⟨31383213810615482864823725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83688570161641287639529933 31383213810615482864823725)
          ·
            refine ⟨11768705178980806074308897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31383213810615482864823725 11768705178980806074308897)
            ·
              refine ⟨8826528884235604555731673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11768705178980806074308897 8826528884235604555731673)
              ·
                refine ⟨6619896663176703416798755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8826528884235604555731673 6619896663176703416798755)
                ·
                  refine ⟨9929844994765055125198133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6619896663176703416798755 9929844994765055125198133)
                  ·
                    refine ⟨930922968259223917987325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9929844994765055125198133 930922968259223917987325)
                    ·
                      rfl

theorem cell22_2719449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 1, 5].length) (baseStart_2719449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719449 prefixEnd_2719449 := by exact prefixLift 2719449
  have htrace : WordTrace (prefixWord ++ tailWord_2719449) baseStart_2719449 baseEnd_2719449 := by
    simpa [prefixWord, tailWord_2719449, baseEnd_2719449] using wordTrace_append hprefix tailTrace_2719449
  have hstable : (prefixWord ++ tailWord_2719449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719449).length < 2 ^ (prefixWord ++ tailWord_2719449).sum := by decide
  have hdescent : baseEnd_2719449 < baseStart_2719449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719528 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 3, 3]
def baseStart_2719528 : Nat := 118140960795 + 2719528 * 2 ^ 59
def prefixEnd_2719528 : Nat := 4983230072969 + 3 ^ 40 * 2719528 * 2
def baseEnd_2719528 : Nat := 930950011573694045262083

theorem tailTrace_2719528 : CollatzResearch.WordTrace tailWord_2719528 prefixEnd_2719528 930950011573694045262083 := by
  unfold tailWord_2719528
  simp only [CollatzResearch.WordTrace]
  refine ⟨49594667445810994625043619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66126223261081326166724825 49594667445810994625043619)
  ·
    refine ⟨74392001168716491937565429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49594667445810994625043619 74392001168716491937565429)
    ·
      refine ⟨6974250109567171119146759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74392001168716491937565429 6974250109567171119146759)
      ·
        refine ⟨10461375164350756678720139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6974250109567171119146759 10461375164350756678720139)
        ·
          refine ⟨15692062746526135018080209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10461375164350756678720139 15692062746526135018080209)
          ·
            refine ⟨11769047059894601263560157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15692062746526135018080209 11769047059894601263560157)
            ·
              refine ⟨4413392647460475473835059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11769047059894601263560157 4413392647460475473835059)
              ·
                refine ⟨6620088971190713210752589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413392647460475473835059 6620088971190713210752589)
                ·
                  refine ⟨2482533364196517454032221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6620088971190713210752589 2482533364196517454032221)
                  ·
                    refine ⟨930950011573694045262083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482533364196517454032221 930950011573694045262083)
                    ·
                      rfl

theorem cell22_2719528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_2719528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719528 prefixEnd_2719528 := by exact prefixLift 2719528
  have htrace : WordTrace (prefixWord ++ tailWord_2719528) baseStart_2719528 baseEnd_2719528 := by
    simpa [prefixWord, tailWord_2719528, baseEnd_2719528] using wordTrace_append hprefix tailTrace_2719528
  have hstable : (prefixWord ++ tailWord_2719528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719528).length < 2 ^ (prefixWord ++ tailWord_2719528).sum := by decide
  have hdescent : baseEnd_2719528 < baseStart_2719528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719534 : List Nat := [4, 1, 3, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2719534 : Nat := 118140960795 + 2719534 * 2 ^ 59
def prefixEnd_2719534 : Nat := 4983230072969 + 3 ^ 40 * 2719534 * 2
def baseEnd_2719534 : Nat := 930952065496312029612065

theorem tailTrace_2719534 : CollatzResearch.WordTrace tailWord_2719534 prefixEnd_2719534 930952065496312029612065 := by
  unfold tailWord_2719534
  simp only [CollatzResearch.WordTrace]
  refine ⟨12398694216200031534350707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 66126369153066834849870437 12398694216200031534350707)
  ·
    refine ⟨18598041324300047301526061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12398694216200031534350707 18598041324300047301526061)
    ·
      refine ⟨6974265496612517738072273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18598041324300047301526061 6974265496612517738072273)
      ·
        refine ⟨5230699122459388303554205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6974265496612517738072273 5230699122459388303554205)
        ·
          refine ⟨1961512170922270613832827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5230699122459388303554205 1961512170922270613832827)
          ·
            refine ⟨2942268256383405920749241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961512170922270613832827 2942268256383405920749241)
            ·
              refine ⟨2206701192287554440561931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2942268256383405920749241 2206701192287554440561931)
              ·
                refine ⟨3310051788431331660842897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206701192287554440561931 3310051788431331660842897)
                ·
                  refine ⟨2482538841323498745632173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310051788431331660842897 2482538841323498745632173)
                  ·
                    refine ⟨930952065496312029612065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482538841323498745632173 930952065496312029612065)
                    ·
                      rfl

theorem cell22_2719534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2719534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719534 prefixEnd_2719534 := by exact prefixLift 2719534
  have htrace : WordTrace (prefixWord ++ tailWord_2719534) baseStart_2719534 baseEnd_2719534 := by
    simpa [prefixWord, tailWord_2719534, baseEnd_2719534] using wordTrace_append hprefix tailTrace_2719534
  have hstable : (prefixWord ++ tailWord_2719534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719534).length < 2 ^ (prefixWord ++ tailWord_2719534).sum := by decide
  have hdescent : baseEnd_2719534 < baseStart_2719534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719601 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 1, 5]
def baseStart_2719601 : Nat := 118140960795 + 2719601 * 2 ^ 59
def prefixEnd_2719601 : Nat := 4983230072969 + 3 ^ 40 * 2719601 * 2
def baseEnd_2719601 : Nat := 930975000965546188186859

theorem tailTrace_2719601 : CollatzResearch.WordTrace tailWord_2719601 prefixEnd_2719601 930975000965546188186859 := by
  unfold tailWord_2719601
  simp only [CollatzResearch.WordTrace]
  refine ⟨99191997420357522717494657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66127998280238348478329771 99191997420357522717494657)
  ·
    refine ⟨74393998065268142038120993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99191997420357522717494657 74393998065268142038120993)
    ·
      refine ⟨55795498548951106528590745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74393998065268142038120993 55795498548951106528590745)
      ·
        refine ⟨41846623911713329896443059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55795498548951106528590745 41846623911713329896443059)
        ·
          refine ⟨62769935867569994844664589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41846623911713329896443059 62769935867569994844664589)
          ·
            refine ⟨23538725950338748066749221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62769935867569994844664589 23538725950338748066749221)
            ·
              refine ⟨4413511115688515262515479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23538725950338748066749221 4413511115688515262515479)
              ·
                refine ⟨6620266673532772893773219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413511115688515262515479 6620266673532772893773219)
                ·
                  refine ⟨9930400010299159340659829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620266673532772893773219 9930400010299159340659829)
                  ·
                    refine ⟨930975000965546188186859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9930400010299159340659829 930975000965546188186859)
                    ·
                      rfl

theorem cell22_2719601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_2719601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719601 prefixEnd_2719601 := by exact prefixLift 2719601
  have htrace : WordTrace (prefixWord ++ tailWord_2719601) baseStart_2719601 baseEnd_2719601 := by
    simpa [prefixWord, tailWord_2719601, baseEnd_2719601] using wordTrace_append hprefix tailTrace_2719601
  have hstable : (prefixWord ++ tailWord_2719601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719601).length < 2 ^ (prefixWord ++ tailWord_2719601).sum := by decide
  have hdescent : baseEnd_2719601 < baseStart_2719601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719659 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 11]
def baseStart_2719659 : Nat := 118140960795 + 2719659 * 2 ^ 59
def prefixEnd_2719659 : Nat := 4983230072969 + 3 ^ 40 * 2719659 * 2
def baseEnd_2719659 : Nat := 310331618516951123412227

theorem tailTrace_2719659 : CollatzResearch.WordTrace tailWord_2719659 prefixEnd_2719659 310331618516951123412227 := by
  unfold tailWord_2719659
  simp only [CollatzResearch.WordTrace]
  refine ⟨99194112854147398623106031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66129408569431599082070687 99194112854147398623106031)
  ·
    refine ⟨148791169281221097934659047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99194112854147398623106031 148791169281221097934659047)
    ·
      refine ⟨223186753921831646901988571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148791169281221097934659047 223186753921831646901988571)
      ·
        refine ⟨334780130882747470352982857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223186753921831646901988571 334780130882747470352982857)
        ·
          refine ⟨251085098162060602764737143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334780130882747470352982857 251085098162060602764737143)
          ·
            refine ⟨376627647243090904147105715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251085098162060602764737143 376627647243090904147105715)
            ·
              refine ⟨564941470864636356220658573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376627647243090904147105715 564941470864636356220658573)
              ·
                refine ⟨211853051574238633582746965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 564941470864636356220658573 211853051574238633582746965)
                ·
                  refine ⟨310331618516951123412227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 211853051574238633582746965 310331618516951123412227)
                  ·
                    rfl

theorem cell22_2719659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 11].length) (baseStart_2719659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719659 prefixEnd_2719659 := by exact prefixLift 2719659
  have htrace : WordTrace (prefixWord ++ tailWord_2719659) baseStart_2719659 baseEnd_2719659 := by
    simpa [prefixWord, tailWord_2719659, baseEnd_2719659] using wordTrace_append hprefix tailTrace_2719659
  have hstable : (prefixWord ++ tailWord_2719659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719659).length < 2 ^ (prefixWord ++ tailWord_2719659).sum := by decide
  have hdescent : baseEnd_2719659 < baseStart_2719659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719736 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 3, 5]
def baseStart_2719736 : Nat := 118140960795 + 2719736 * 2 ^ 59
def prefixEnd_2719736 : Nat := 4983230072969 + 3 ^ 40 * 2719736 * 2
def baseEnd_2719736 : Nat := 931021214224450836061445

theorem tailTrace_2719736 : CollatzResearch.WordTrace tailWord_2719736 prefixEnd_2719736 931021214224450836061445 := by
  unfold tailWord_2719736
  simp only [CollatzResearch.WordTrace]
  refine ⟨49598460637434220386829531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66131280849912293849106041 49598460637434220386829531)
  ·
    refine ⟨74397690956151330580244297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49598460637434220386829531 74397690956151330580244297)
    ·
      refine ⟨55798268217113497935183223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74397690956151330580244297 55798268217113497935183223)
      ·
        refine ⟨83697402325670246902774835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55798268217113497935183223 83697402325670246902774835)
        ·
          refine ⟨125546103488505370354162253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83697402325670246902774835 125546103488505370354162253)
          ·
            refine ⟨47079788808189513882810845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125546103488505370354162253 47079788808189513882810845)
            ·
              refine ⟨17654920803071067706054067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47079788808189513882810845 17654920803071067706054067)
              ·
                refine ⟨26482381204606601559081101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17654920803071067706054067 26482381204606601559081101)
                ·
                  refine ⟨9930892951727475584655413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26482381204606601559081101 9930892951727475584655413)
                  ·
                    refine ⟨931021214224450836061445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9930892951727475584655413 931021214224450836061445)
                    ·
                      rfl

theorem cell22_2719736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_2719736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719736 prefixEnd_2719736 := by exact prefixLift 2719736
  have htrace : WordTrace (prefixWord ++ tailWord_2719736) baseStart_2719736 baseEnd_2719736 := by
    simpa [prefixWord, tailWord_2719736, baseEnd_2719736] using wordTrace_append hprefix tailTrace_2719736
  have hstable : (prefixWord ++ tailWord_2719736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719736).length < 2 ^ (prefixWord ++ tailWord_2719736).sum := by decide
  have hdescent : baseEnd_2719736 < baseStart_2719736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719740 : List Nat := [2, 2, 2, 1, 2, 2, 5, 1, 1, 4]
def baseStart_2719740 : Nat := 118140960795 + 2719740 * 2 ^ 59
def prefixEnd_2719740 : Nat := 4983230072969 + 3 ^ 40 * 2719740 * 2
def baseEnd_2719740 : Nat := 931022583506196158961433

theorem tailTrace_2719740 : CollatzResearch.WordTrace tailWord_2719740 prefixEnd_2719740 931022583506196158961433 := by
  unfold tailWord_2719740
  simp only [CollatzResearch.WordTrace]
  refine ⟨49598533583426974728402337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66131378111235966304536449 49598533583426974728402337)
  ·
    refine ⟨37198900187570231046301753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49598533583426974728402337 37198900187570231046301753)
    ·
      refine ⟨27899175140677673284726315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37198900187570231046301753 27899175140677673284726315)
      ·
        refine ⟨41848762711016509927089473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27899175140677673284726315 41848762711016509927089473)
        ·
          refine ⟨31386572033262382445317105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41848762711016509927089473 31386572033262382445317105)
          ·
            refine ⟨23539929024946786833987829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31386572033262382445317105 23539929024946786833987829)
            ·
              refine ⟨2206868346088761265686359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23539929024946786833987829 2206868346088761265686359)
              ·
                refine ⟨3310302519133141898529539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2206868346088761265686359 3310302519133141898529539)
                ·
                  refine ⟨4965453778699712847794309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3310302519133141898529539 4965453778699712847794309)
                  ·
                    refine ⟨931022583506196158961433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4965453778699712847794309 931022583506196158961433)
                    ·
                      rfl

theorem cell22_2719740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_2719740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719740 prefixEnd_2719740 := by exact prefixLift 2719740
  have htrace : WordTrace (prefixWord ++ tailWord_2719740) baseStart_2719740 baseEnd_2719740 := by
    simpa [prefixWord, tailWord_2719740, baseEnd_2719740] using wordTrace_append hprefix tailTrace_2719740
  have hstable : (prefixWord ++ tailWord_2719740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719740).length < 2 ^ (prefixWord ++ tailWord_2719740).sum := by decide
  have hdescent : baseEnd_2719740 < baseStart_2719740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719748 : List Nat := [2, 3, 2, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2719748 : Nat := 118140960795 + 2719748 * 2 ^ 59
def prefixEnd_2719748 : Nat := 4983230072969 + 3 ^ 40 * 2719748 * 2
def baseEnd_2719748 : Nat := 931025322069686804761409

theorem tailTrace_2719748 : CollatzResearch.WordTrace tailWord_2719748 prefixEnd_2719748 931025322069686804761409 := by
  unfold tailWord_2719748
  simp only [CollatzResearch.WordTrace]
  refine ⟨49598679475412483411547949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66131572633883311215397265 49598679475412483411547949)
  ·
    refine ⟨18599504803279681279330481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49598679475412483411547949 18599504803279681279330481)
    ·
      refine ⟨13949628602459760959497861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18599504803279681279330481 13949628602459760959497861)
      ·
        refine ⟨2615555362961205179905849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13949628602459760959497861 2615555362961205179905849)
        ·
          refine ⟨1961666522220903884929387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2615555362961205179905849 1961666522220903884929387)
          ·
            refine ⟨2942499783331355827394081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1961666522220903884929387 2942499783331355827394081)
            ·
              refine ⟨2206874837498516870545561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2942499783331355827394081 2206874837498516870545561)
              ·
                refine ⟨1655156128123887652909171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2206874837498516870545561 1655156128123887652909171)
                ·
                  refine ⟨2482734192185831479363757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655156128123887652909171 2482734192185831479363757)
                  ·
                    refine ⟨931025322069686804761409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482734192185831479363757 931025322069686804761409)
                    ·
                      rfl

theorem cell22_2719748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2719748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719748 prefixEnd_2719748 := by exact prefixLift 2719748
  have htrace : WordTrace (prefixWord ++ tailWord_2719748) baseStart_2719748 baseEnd_2719748 := by
    simpa [prefixWord, tailWord_2719748, baseEnd_2719748] using wordTrace_append hprefix tailTrace_2719748
  have hstable : (prefixWord ++ tailWord_2719748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719748).length < 2 ^ (prefixWord ++ tailWord_2719748).sum := by decide
  have hdescent : baseEnd_2719748 < baseStart_2719748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719770 : List Nat := [3, 1, 1, 3, 1, 3, 2, 3, 2, 3]
def baseStart_2719770 : Nat := 118140960795 + 2719770 * 2 ^ 59
def prefixEnd_2719770 : Nat := 4983230072969 + 3 ^ 40 * 2719770 * 2
def baseEnd_2719770 : Nat := 931032853119286080711341

theorem tailTrace_2719770 : CollatzResearch.WordTrace tailWord_2719770 prefixEnd_2719770 931032853119286080711341 := by
  unfold tailWord_2719770
  simp only [CollatzResearch.WordTrace]
  refine ⟨24799540339186316145099191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66132107571163509720264509 24799540339186316145099191)
  ·
    refine ⟨37199310508779474217648787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24799540339186316145099191 37199310508779474217648787)
    ·
      refine ⟨55798965763169211326473181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37199310508779474217648787 55798965763169211326473181)
      ·
        refine ⟨20924612161188454247427443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55798965763169211326473181 20924612161188454247427443)
        ·
          refine ⟨31386918241782681371141165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20924612161188454247427443 31386918241782681371141165)
          ·
            refine ⟨11770094340668505514177937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31386918241782681371141165 11770094340668505514177937)
            ·
              refine ⟨8827570755501379135633453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11770094340668505514177937 8827570755501379135633453)
              ·
                refine ⟨3310339033313017175862545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8827570755501379135633453 3310339033313017175862545)
                ·
                  refine ⟨2482754274984762881896909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310339033313017175862545 2482754274984762881896909)
                  ·
                    refine ⟨931032853119286080711341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482754274984762881896909 931032853119286080711341)
                    ·
                      rfl

theorem cell22_2719770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_2719770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719770 prefixEnd_2719770 := by exact prefixLift 2719770
  have htrace : WordTrace (prefixWord ++ tailWord_2719770) baseStart_2719770 baseEnd_2719770 := by
    simpa [prefixWord, tailWord_2719770, baseEnd_2719770] using wordTrace_append hprefix tailTrace_2719770
  have hstable : (prefixWord ++ tailWord_2719770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719770).length < 2 ^ (prefixWord ++ tailWord_2719770).sum := by decide
  have hdescent : baseEnd_2719770 < baseStart_2719770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719815 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 3, 3]
def baseStart_2719815 : Nat := 118140960795 + 2719815 * 2 ^ 59
def prefixEnd_2719815 : Nat := 4983230072969 + 3 ^ 40 * 2719815 * 2
def baseEnd_2719815 : Nat := 931048257538920963336203

theorem tailTrace_2719815 : CollatzResearch.WordTrace tailWord_2719815 prefixEnd_2719815 931048257538920963336203 := by
  unfold tailWord_2719815
  simp only [CollatzResearch.WordTrace]
  refine ⟨99199802641582237265784899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66133201761054824843856599 99199802641582237265784899)
  ·
    refine ⟨148799703962373355898677349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99199802641582237265784899 148799703962373355898677349)
    ·
      refine ⟨27899944492945004231002003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148799703962373355898677349 27899944492945004231002003)
      ·
        refine ⟨41849916739417506346503005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27899944492945004231002003 41849916739417506346503005)
        ·
          refine ⟨15693718777281564879938627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41849916739417506346503005 15693718777281564879938627)
          ·
            refine ⟨23540578165922347319907941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15693718777281564879938627 23540578165922347319907941)
            ·
              refine ⟨4413858406110440122482739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23540578165922347319907941 4413858406110440122482739)
              ·
                refine ⟨6620787609165660183724109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4413858406110440122482739 6620787609165660183724109)
                ·
                  refine ⟨2482795353437122568896541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6620787609165660183724109 2482795353437122568896541)
                  ·
                    refine ⟨931048257538920963336203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482795353437122568896541 931048257538920963336203)
                    ·
                      rfl

theorem cell22_2719815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_2719815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719815 prefixEnd_2719815 := by exact prefixLift 2719815
  have htrace : WordTrace (prefixWord ++ tailWord_2719815) baseStart_2719815 baseEnd_2719815 := by
    simpa [prefixWord, tailWord_2719815, baseEnd_2719815] using wordTrace_append hprefix tailTrace_2719815
  have hstable : (prefixWord ++ tailWord_2719815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719815).length < 2 ^ (prefixWord ++ tailWord_2719815).sum := by decide
  have hdescent : baseEnd_2719815 < baseStart_2719815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719888 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 1, 5]
def baseStart_2719888 : Nat := 118140960795 + 2719888 * 2 ^ 59
def prefixEnd_2719888 : Nat := 4983230072969 + 3 ^ 40 * 2719888 * 2
def baseEnd_2719888 : Nat := 931073246930773106260979

theorem tailTrace_2719888 : CollatzResearch.WordTrace tailWord_2719888 prefixEnd_2719888 931073246930773106260979 := by
  unfold tailWord_2719888
  simp only [CollatzResearch.WordTrace]
  refine ⟨49601232585158885366596159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66134976780211847155461545 49601232585158885366596159)
  ·
    refine ⟨74401848877738328049894239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49601232585158885366596159 74401848877738328049894239)
    ·
      refine ⟨111602773316607492074841359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74401848877738328049894239 111602773316607492074841359)
      ·
        refine ⟨167404159974911238112262039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111602773316607492074841359 167404159974911238112262039)
        ·
          refine ⟨251106239962366857168393059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167404159974911238112262039 251106239962366857168393059)
          ·
            refine ⟨376659359943550285752589589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251106239962366857168393059 376659359943550285752589589)
            ·
              refine ⟨17655907497353919644652637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 376659359943550285752589589 17655907497353919644652637)
              ·
                refine ⟨6620965311507719866744739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17655907497353919644652637 6620965311507719866744739)
                ·
                  refine ⟨9931447967261579800117109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6620965311507719866744739 9931447967261579800117109)
                  ·
                    refine ⟨931073246930773106260979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9931447967261579800117109 931073246930773106260979)
                    ·
                      rfl

theorem cell22_2719888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 5].length) (baseStart_2719888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719888 prefixEnd_2719888 := by exact prefixLift 2719888
  have htrace : WordTrace (prefixWord ++ tailWord_2719888) baseStart_2719888 baseEnd_2719888 := by
    simpa [prefixWord, tailWord_2719888, baseEnd_2719888] using wordTrace_append hprefix tailTrace_2719888
  have hstable : (prefixWord ++ tailWord_2719888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719888).length < 2 ^ (prefixWord ++ tailWord_2719888).sum := by decide
  have hdescent : baseEnd_2719888 < baseStart_2719888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719905 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 1, 5]
def baseStart_2719905 : Nat := 118140960795 + 2719905 * 2 ^ 59
def prefixEnd_2719905 : Nat := 4983230072969 + 3 ^ 40 * 2719905 * 2
def baseEnd_2719905 : Nat := 931079066378190728585927

theorem tailTrace_2719905 : CollatzResearch.WordTrace tailWord_2719905 prefixEnd_2719905 931079066378190728585927 := by
  unfold tailWord_2719905
  simp only [CollatzResearch.WordTrace]
  refine ⟨99203085211256182636561169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66135390140837455091040779 99203085211256182636561169)
  ·
    refine ⟨74402313908442136977420877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99203085211256182636561169 74402313908442136977420877)
    ·
      refine ⟨27900867715665801366532829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74402313908442136977420877 27900867715665801366532829)
      ·
        refine ⟨10462825393374675512449811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27900867715665801366532829 10462825393374675512449811)
        ·
          refine ⟨15694238090062013268674717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10462825393374675512449811 15694238090062013268674717)
          ·
            refine ⟨5885339283773254975753019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15694238090062013268674717 5885339283773254975753019)
            ·
              refine ⟨8828008925659882463629529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5885339283773254975753019 8828008925659882463629529)
              ·
                refine ⟨6621006694244911847722147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8828008925659882463629529 6621006694244911847722147)
                ·
                  refine ⟨9931510041367367771583221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6621006694244911847722147 9931510041367367771583221)
                  ·
                    refine ⟨931079066378190728585927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9931510041367367771583221 931079066378190728585927)
                    ·
                      rfl

theorem cell22_2719905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 5].length) (baseStart_2719905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719905 prefixEnd_2719905 := by exact prefixLift 2719905
  have htrace : WordTrace (prefixWord ++ tailWord_2719905) baseStart_2719905 baseEnd_2719905 := by
    simpa [prefixWord, tailWord_2719905, baseEnd_2719905] using wordTrace_append hprefix tailTrace_2719905
  have hstable : (prefixWord ++ tailWord_2719905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719905).length < 2 ^ (prefixWord ++ tailWord_2719905).sum := by decide
  have hdescent : baseEnd_2719905 < baseStart_2719905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719922 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 2, 3]
def baseStart_2719922 : Nat := 118140960795 + 2719922 * 2 ^ 59
def prefixEnd_2719922 : Nat := 4983230072969 + 3 ^ 40 * 2719922 * 2
def baseEnd_2719922 : Nat := 931084885825608350910875

theorem tailTrace_2719922 : CollatzResearch.WordTrace tailWord_2719922 prefixEnd_2719922 931084885825608350910875 := by
  unfold tailWord_2719922
  simp only [CollatzResearch.WordTrace]
  refine ⟨24800926313048648634982505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66135803501463063026620013 24800926313048648634982505)
  ·
    refine ⟨18600694734786486476236879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24800926313048648634982505 18600694734786486476236879)
    ·
      refine ⟨27901042102179729714355319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18600694734786486476236879 27901042102179729714355319)
      ·
        refine ⟨41851563153269594571532979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27901042102179729714355319 41851563153269594571532979)
        ·
          refine ⟨62777344729904391857299469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41851563153269594571532979 62777344729904391857299469)
          ·
            refine ⟨23541504273714146946487301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62777344729904391857299469 23541504273714146946487301)
            ·
              refine ⟨4414032051321402552466369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23541504273714146946487301 4414032051321402552466369)
              ·
                refine ⟨3310524038491051914349777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4414032051321402552466369 3310524038491051914349777)
                ·
                  refine ⟨2482893028868288935762333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3310524038491051914349777 2482893028868288935762333)
                  ·
                    refine ⟨931084885825608350910875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2482893028868288935762333 931084885825608350910875)
                    ·
                      rfl

theorem cell22_2719922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_2719922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719922 prefixEnd_2719922 := by exact prefixLift 2719922
  have htrace : WordTrace (prefixWord ++ tailWord_2719922) baseStart_2719922 baseEnd_2719922 := by
    simpa [prefixWord, tailWord_2719922, baseEnd_2719922] using wordTrace_append hprefix tailTrace_2719922
  have hstable : (prefixWord ++ tailWord_2719922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719922).length < 2 ^ (prefixWord ++ tailWord_2719922).sum := by decide
  have hdescent : baseEnd_2719922 < baseStart_2719922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719933 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2719933 : Nat := 118140960795 + 2719933 * 2 ^ 59
def prefixEnd_2719933 : Nat := 4983230072969 + 3 ^ 40 * 2719933 * 2
def baseEnd_2719933 : Nat := 931088651350407988885841

theorem tailTrace_2719933 : CollatzResearch.WordTrace tailWord_2719933 prefixEnd_2719933 931088651350407988885841 := by
  unfold tailWord_2719933
  simp only [CollatzResearch.WordTrace]
  refine ⟨99204106455154743418580453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66136070970103162279053635 99204106455154743418580453)
  ·
    refine ⟨18600769960341514390983835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99204106455154743418580453 18600769960341514390983835)
    ·
      refine ⟨27901154940512271586475753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18600769960341514390983835 27901154940512271586475753)
      ·
        refine ⟨20925866205384203689856815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27901154940512271586475753 20925866205384203689856815)
        ·
          refine ⟨31388799308076305534785223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20925866205384203689856815 31388799308076305534785223)
          ·
            refine ⟨47083198962114458302177835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31388799308076305534785223 47083198962114458302177835)
            ·
              refine ⟨70624798443171687453266753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47083198962114458302177835 70624798443171687453266753)
              ·
                refine ⟨52968598832378765589950065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70624798443171687453266753 52968598832378765589950065)
                ·
                  refine ⟨39726449124284074192462549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52968598832378765589950065 39726449124284074192462549)
                  ·
                    refine ⟨931088651350407988885841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39726449124284074192462549 931088651350407988885841)
                    ·
                      rfl

theorem cell22_2719933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2719933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719933 prefixEnd_2719933 := by exact prefixLift 2719933
  have htrace : WordTrace (prefixWord ++ tailWord_2719933) baseStart_2719933 baseEnd_2719933 := by
    simpa [prefixWord, tailWord_2719933, baseEnd_2719933] using wordTrace_append hprefix tailTrace_2719933
  have hstable : (prefixWord ++ tailWord_2719933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719933).length < 2 ^ (prefixWord ++ tailWord_2719933).sum := by decide
  have hdescent : baseEnd_2719933 < baseStart_2719933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2719993 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 2, 8]
def baseStart_2719993 : Nat := 118140960795 + 2719993 * 2 ^ 59
def prefixEnd_2719993 : Nat := 4983230072969 + 3 ^ 40 * 2719993 * 2
def baseEnd_2719993 : Nat := 931109190576587832385657

theorem tailTrace_2719993 : CollatzResearch.WordTrace tailWord_2719993 prefixEnd_2719993 931109190576587832385657 := by
  unfold tailWord_2719993
  simp only [CollatzResearch.WordTrace]
  refine ⟨99206294834937373665764633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66137529889958249110509755 99206294834937373665764633)
  ·
    refine ⟨74404721126203030249323475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99206294834937373665764633 74404721126203030249323475)
    ·
      refine ⟨111607081689304545373985213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74404721126203030249323475 111607081689304545373985213)
      ·
        refine ⟨41852655633489204515244455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111607081689304545373985213 41852655633489204515244455)
        ·
          refine ⟨62778983450233806772866683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41852655633489204515244455 62778983450233806772866683)
          ·
            refine ⟨94168475175350710159300025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62778983450233806772866683 94168475175350710159300025)
            ·
              refine ⟨70626356381513032619475019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94168475175350710159300025 70626356381513032619475019)
              ·
                refine ⟨105939534572269548929212529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70626356381513032619475019 105939534572269548929212529)
                ·
                  refine ⟨79454650929202161696909397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105939534572269548929212529 79454650929202161696909397)
                  ·
                    refine ⟨931109190576587832385657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79454650929202161696909397 931109190576587832385657)
                    ·
                      rfl

theorem cell22_2719993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_2719993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2719993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2719993 prefixEnd_2719993 := by exact prefixLift 2719993
  have htrace : WordTrace (prefixWord ++ tailWord_2719993) baseStart_2719993 baseEnd_2719993 := by
    simpa [prefixWord, tailWord_2719993, baseEnd_2719993] using wordTrace_append hprefix tailTrace_2719993
  have hstable : (prefixWord ++ tailWord_2719993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2719993).length < 2 ^ (prefixWord ++ tailWord_2719993).sum := by decide
  have hdescent : baseEnd_2719993 < baseStart_2719993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2719993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720010 : List Nat := [3, 1, 2, 2, 1, 1, 2, 3, 3, 4]
def baseStart_2720010 : Nat := 118140960795 + 2720010 * 2 ^ 59
def prefixEnd_2720010 : Nat := 4983230072969 + 3 ^ 40 * 2720010 * 2
def baseEnd_2720010 : Nat := 931115010024005454710605

theorem tailTrace_2720010 : CollatzResearch.WordTrace tailWord_2720010 prefixEnd_2720010 931115010024005454710605 := by
  unfold tailWord_2720010
  simp only [CollatzResearch.WordTrace]
  refine ⟨24801728718968946392283371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66137943250583857046088989 24801728718968946392283371)
  ·
    refine ⟨37202593078453419588425057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24801728718968946392283371 37202593078453419588425057)
    ·
      refine ⟨27901944808840064691318793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37202593078453419588425057 27901944808840064691318793)
      ·
        refine ⟨20926458606630048518489095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27901944808840064691318793 20926458606630048518489095)
        ·
          refine ⟨31389687909945072777733643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20926458606630048518489095 31389687909945072777733643)
          ·
            refine ⟨47084531864917609166600465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31389687909945072777733643 47084531864917609166600465)
            ·
              refine ⟨35313398898688206874950349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47084531864917609166600465 35313398898688206874950349)
              ·
                refine ⟨13242524587008077578106381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35313398898688206874950349 13242524587008077578106381)
                ·
                  refine ⟨4965946720128029091789893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13242524587008077578106381 4965946720128029091789893)
                  ·
                    refine ⟨931115010024005454710605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4965946720128029091789893 931115010024005454710605)
                    ·
                      rfl

theorem cell22_2720010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_2720010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720010 prefixEnd_2720010 := by exact prefixLift 2720010
  have htrace : WordTrace (prefixWord ++ tailWord_2720010) baseStart_2720010 baseEnd_2720010 := by
    simpa [prefixWord, tailWord_2720010, baseEnd_2720010] using wordTrace_append hprefix tailTrace_2720010
  have hstable : (prefixWord ++ tailWord_2720010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720010).length < 2 ^ (prefixWord ++ tailWord_2720010).sum := by decide
  have hdescent : baseEnd_2720010 < baseStart_2720010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720100 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2720100 : Nat := 118140960795 + 2720100 * 2 ^ 59
def prefixEnd_2720100 : Nat := 4983230072969 + 3 ^ 40 * 2720100 * 2
def baseEnd_2720100 : Nat := 931145818863275219960329

theorem tailTrace_2720100 : CollatzResearch.WordTrace tailWord_2720100 prefixEnd_2720100 931145818863275219960329 := by
  unfold tailWord_2720100
  simp only [CollatzResearch.WordTrace]
  refine ⟨49605098722774865469954877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66140131630366487293273169 49605098722774865469954877)
  ·
    refine ⟨18601912021040574551233079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49605098722774865469954877 18601912021040574551233079)
    ·
      refine ⟨27902868031560861826849619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18601912021040574551233079 27902868031560861826849619)
      ·
        refine ⟨41854302047341292740274429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27902868031560861826849619 41854302047341292740274429)
        ·
          refine ⟨15695363267752984777602911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41854302047341292740274429 15695363267752984777602911)
          ·
            refine ⟨23543044901629477166404367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15695363267752984777602911 23543044901629477166404367)
            ·
              refine ⟨35314567352444215749606551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23543044901629477166404367 35314567352444215749606551)
              ·
                refine ⟨52971851028666323624409827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35314567352444215749606551 52971851028666323624409827)
                ·
                  refine ⟨79457776542999485436614741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52971851028666323624409827 79457776542999485436614741)
                  ·
                    refine ⟨931145818863275219960329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79457776542999485436614741 931145818863275219960329)
                    ·
                      rfl

theorem cell22_2720100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2720100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720100 prefixEnd_2720100 := by exact prefixLift 2720100
  have htrace : WordTrace (prefixWord ++ tailWord_2720100) baseStart_2720100 baseEnd_2720100 := by
    simpa [prefixWord, tailWord_2720100, baseEnd_2720100] using wordTrace_append hprefix tailTrace_2720100
  have hstable : (prefixWord ++ tailWord_2720100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720100).length < 2 ^ (prefixWord ++ tailWord_2720100).sum := by decide
  have hdescent : baseEnd_2720100 < baseStart_2720100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720136 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 1, 3]
def baseStart_2720136 : Nat := 118140960795 + 2720136 * 2 ^ 59
def prefixEnd_2720136 : Nat := 4983230072969 + 3 ^ 40 * 2720136 * 2
def baseEnd_2720136 : Nat := 931158142398983126060219

theorem tailTrace_2720136 : CollatzResearch.WordTrace tailWord_2720136 prefixEnd_2720136 931158142398983126060219 := by
  unfold tailWord_2720136
  simp only [CollatzResearch.WordTrace]
  refine ⟨49605755236709654544110131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66141006982279539392146841 49605755236709654544110131)
  ·
    refine ⟨74408632855064481816165197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49605755236709654544110131 74408632855064481816165197)
    ·
      refine ⟨27903237320649180681061949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74408632855064481816165197 27903237320649180681061949)
      ·
        refine ⟨10463713995243442755398231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27903237320649180681061949 10463713995243442755398231)
        ·
          refine ⟨15695570992865164133097347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10463713995243442755398231 15695570992865164133097347)
          ·
            refine ⟨23543356489297746199646021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15695570992865164133097347 23543356489297746199646021)
            ·
              refine ⟨4414379341743327412433629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23543356489297746199646021 4414379341743327412433629)
              ·
                refine ⟨1655392253153747779662611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4414379341743327412433629 1655392253153747779662611)
                ·
                  refine ⟨2483088379730621669493917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1655392253153747779662611 2483088379730621669493917)
                  ·
                    refine ⟨931158142398983126060219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2483088379730621669493917 931158142398983126060219)
                    ·
                      rfl

theorem cell22_2720136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_2720136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720136 prefixEnd_2720136 := by exact prefixLift 2720136
  have htrace : WordTrace (prefixWord ++ tailWord_2720136) baseStart_2720136 baseEnd_2720136 := by
    simpa [prefixWord, tailWord_2720136, baseEnd_2720136] using wordTrace_append hprefix tailTrace_2720136
  have hstable : (prefixWord ++ tailWord_2720136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720136).length < 2 ^ (prefixWord ++ tailWord_2720136).sum := by decide
  have hdescent : baseEnd_2720136 < baseStart_2720136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720177 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 6]
def baseStart_2720177 : Nat := 118140960795 + 2720177 * 2 ^ 59
def prefixEnd_2720177 : Nat := 4983230072969 + 3 ^ 40 * 2720177 * 2
def baseEnd_2720177 : Nat := 310390725845624228595031

theorem tailTrace_2720177 : CollatzResearch.WordTrace tailWord_2720177 prefixEnd_2720177 310390725845624228595031 := by
  unfold tailWord_2720177
  simp only [CollatzResearch.WordTrace]
  refine ⟨99213005866270773090462785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66142003910847182060308523 99213005866270773090462785)
  ·
    refine ⟨74409754399703079817847089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99213005866270773090462785 74409754399703079817847089)
    ·
      refine ⟨55807315799777309863385317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74409754399703079817847089 55807315799777309863385317)
      ·
        refine ⟨10463871712458245599384747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55807315799777309863385317 10463871712458245599384747)
        ·
          refine ⟨15695807568687368399077121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10463871712458245599384747 15695807568687368399077121)
          ·
            refine ⟨11771855676515526299307841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15695807568687368399077121 11771855676515526299307841)
            ·
              refine ⟨8828891757386644724480881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11771855676515526299307841 8828891757386644724480881)
              ·
                refine ⟨6621668818039983543360661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8828891757386644724480881 6621668818039983543360661)
                ·
                  refine ⟨310390725845624228595031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6621668818039983543360661 310390725845624228595031)
                  ·
                    rfl

theorem cell22_2720177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 6].length) (baseStart_2720177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720177 prefixEnd_2720177 := by exact prefixLift 2720177
  have htrace : WordTrace (prefixWord ++ tailWord_2720177) baseStart_2720177 baseEnd_2720177 := by
    simpa [prefixWord, tailWord_2720177, baseEnd_2720177] using wordTrace_append hprefix tailTrace_2720177
  have hstable : (prefixWord ++ tailWord_2720177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720177).length < 2 ^ (prefixWord ++ tailWord_2720177).sum := by decide
  have hdescent : baseEnd_2720177 < baseStart_2720177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720262 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2720262 : Nat := 118140960795 + 2720262 * 2 ^ 59
def prefixEnd_2720262 : Nat := 4983230072969 + 3 ^ 40 * 2720262 * 2
def baseEnd_2720262 : Nat := 310400424924653599136611

theorem tailTrace_2720262 : CollatzResearch.WordTrace tailWord_2720262 prefixEnd_2720262 310400424924653599136611 := by
  unfold tailWord_2720262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100503314717588518978345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 66144070713975221738204693 3100503314717588518978345)
  ·
    refine ⟨2325377486038191389233759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3100503314717588518978345 2325377486038191389233759)
    ·
      refine ⟨3488066229057287083850639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2325377486038191389233759 3488066229057287083850639)
      ·
        refine ⟨5232099343585930625775959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3488066229057287083850639 5232099343585930625775959)
        ·
          refine ⟨7848149015378895938663939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5232099343585930625775959 7848149015378895938663939)
          ·
            refine ⟨11772223523068343907995909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7848149015378895938663939 11772223523068343907995909)
            ·
              refine ⟨2207291910575314482749233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11772223523068343907995909 2207291910575314482749233)
              ·
                refine ⟨1655468932931485862061925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2207291910575314482749233 1655468932931485862061925)
                ·
                  refine ⟨310400424924653599136611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1655468932931485862061925 310400424924653599136611)
                  ·
                    rfl

theorem cell22_2720262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2720262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720262 prefixEnd_2720262 := by exact prefixLift 2720262
  have htrace : WordTrace (prefixWord ++ tailWord_2720262) baseStart_2720262 baseEnd_2720262 := by
    simpa [prefixWord, tailWord_2720262, baseEnd_2720262] using wordTrace_append hprefix tailTrace_2720262
  have hstable : (prefixWord ++ tailWord_2720262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720262).length < 2 ^ (prefixWord ++ tailWord_2720262).sum := by decide
  have hdescent : baseEnd_2720262 < baseStart_2720262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720282 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_2720282 : Nat := 118140960795 + 2720282 * 2 ^ 59
def prefixEnd_2720282 : Nat := 4983230072969 + 3 ^ 40 * 2720282 * 2
def baseEnd_2720282 : Nat := 931208121182687411909771

theorem tailTrace_2720282 : CollatzResearch.WordTrace tailWord_2720282 prefixEnd_2720282 931208121182687411909771 := by
  unfold tailWord_2720282
  simp only [CollatzResearch.WordTrace]
  refine ⟨24804208882722594005758775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 66144557020593584015356733 24804208882722594005758775)
  ·
    refine ⟨37206313324083891008638163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24804208882722594005758775 37206313324083891008638163)
    ·
      refine ⟨55809469986125836512957245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37206313324083891008638163 55809469986125836512957245)
      ·
        refine ⟨20928551244797188692358967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55809469986125836512957245 20928551244797188692358967)
        ·
          refine ⟨31392826867195783038538451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20928551244797188692358967 31392826867195783038538451)
          ·
            refine ⟨47089240300793674557807677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31392826867195783038538451 47089240300793674557807677)
            ·
              refine ⟨17658465112797627959177879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47089240300793674557807677 17658465112797627959177879)
              ·
                refine ⟨26487697669196441938766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17658465112797627959177879 26487697669196441938766819)
                ·
                  refine ⟨39731546503794662908150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26487697669196441938766819 39731546503794662908150229)
                  ·
                    refine ⟨931208121182687411909771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39731546503794662908150229 931208121182687411909771)
                    ·
                      rfl

theorem cell22_2720282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_2720282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720282 prefixEnd_2720282 := by exact prefixLift 2720282
  have htrace : WordTrace (prefixWord ++ tailWord_2720282) baseStart_2720282 baseEnd_2720282 := by
    simpa [prefixWord, tailWord_2720282, baseEnd_2720282] using wordTrace_append hprefix tailTrace_2720282
  have hstable : (prefixWord ++ tailWord_2720282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720282).length < 2 ^ (prefixWord ++ tailWord_2720282).sum := by decide
  have hdescent : baseEnd_2720282 < baseStart_2720282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720284 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 5]
def baseStart_2720284 : Nat := 118140960795 + 2720284 * 2 ^ 59
def prefixEnd_2720284 : Nat := 4983230072969 + 3 ^ 40 * 2720284 * 2
def baseEnd_2720284 : Nat := 310402935274520024453255

theorem tailTrace_2720284 : CollatzResearch.WordTrace tailWord_2720284 prefixEnd_2720284 310402935274520024453255 := by
  unfold tailWord_2720284
  simp only [CollatzResearch.WordTrace]
  refine ⟨49608454238441565182303953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66144605651255420243071937 49608454238441565182303953)
  ·
    refine ⟨37206340678831173886727965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49608454238441565182303953 37206340678831173886727965)
    ·
      refine ⟨13952377754561690207522987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37206340678831173886727965 13952377754561690207522987)
      ·
        refine ⟨20928566631842535311284481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13952377754561690207522987 20928566631842535311284481)
        ·
          refine ⟨15696424973881901483463361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20928566631842535311284481 15696424973881901483463361)
          ·
            refine ⟨11772318730411426112597521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15696424973881901483463361 11772318730411426112597521)
            ·
              refine ⟨8829239047808569584448141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11772318730411426112597521 8829239047808569584448141)
              ·
                refine ⟨3310964642928213594168053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8829239047808569584448141 3310964642928213594168053)
                ·
                  refine ⟨310402935274520024453255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3310964642928213594168053 310402935274520024453255)
                  ·
                    rfl

theorem cell22_2720284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_2720284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720284 prefixEnd_2720284 := by exact prefixLift 2720284
  have htrace : WordTrace (prefixWord ++ tailWord_2720284) baseStart_2720284 baseEnd_2720284 := by
    simpa [prefixWord, tailWord_2720284, baseEnd_2720284] using wordTrace_append hprefix tailTrace_2720284
  have hstable : (prefixWord ++ tailWord_2720284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720284).length < 2 ^ (prefixWord ++ tailWord_2720284).sum := by decide
  have hdescent : baseEnd_2720284 < baseStart_2720284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720312 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 8]
def baseStart_2720312 : Nat := 118140960795 + 2720312 * 2 ^ 59
def prefixEnd_2720312 : Nat := 4983230072969 + 3 ^ 40 * 2720312 * 2
def baseEnd_2720312 : Nat := 310406130265259111219893

theorem tailTrace_2720312 : CollatzResearch.WordTrace tailWord_2720312 prefixEnd_2720312 310406130265259111219893 := by
  unfold tailWord_2720312
  simp only [CollatzResearch.WordTrace]
  refine ⟨49608964860390845573313595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66145286480521127431084793 49608964860390845573313595)
  ·
    refine ⟨74413447290586268359970393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49608964860390845573313595 74413447290586268359970393)
    ·
      refine ⟨55810085467939701269977795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74413447290586268359970393 55810085467939701269977795)
      ·
        refine ⟨83715128201909551904966693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55810085467939701269977795 83715128201909551904966693)
        ·
          refine ⟨15696586537858040982181255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83715128201909551904966693 15696586537858040982181255)
          ·
            refine ⟨23544879806787061473271883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15696586537858040982181255 23544879806787061473271883)
            ·
              refine ⟨35317319710180592209907825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23544879806787061473271883 35317319710180592209907825)
              ·
                refine ⟨26487989782635444157430869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35317319710180592209907825 26487989782635444157430869)
                ·
                  refine ⟨310406130265259111219893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26487989782635444157430869 310406130265259111219893)
                  ·
                    rfl

theorem cell22_2720312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 8].length) (baseStart_2720312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720312 prefixEnd_2720312 := by exact prefixLift 2720312
  have htrace : WordTrace (prefixWord ++ tailWord_2720312) baseStart_2720312 baseEnd_2720312 := by
    simpa [prefixWord, tailWord_2720312, baseEnd_2720312] using wordTrace_append hprefix tailTrace_2720312
  have hstable : (prefixWord ++ tailWord_2720312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720312).length < 2 ^ (prefixWord ++ tailWord_2720312).sum := by decide
  have hdescent : baseEnd_2720312 < baseStart_2720312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720344 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 1, 5]
def baseStart_2720344 : Nat := 118140960795 + 2720344 * 2 ^ 59
def prefixEnd_2720344 : Nat := 4983230072969 + 3 ^ 40 * 2720344 * 2
def baseEnd_2720344 : Nat := 931229345049739916859581

theorem tailTrace_2720344 : CollatzResearch.WordTrace tailWord_2720344 prefixEnd_2720344 931229345049739916859581 := by
  unfold tailWord_2720344
  simp only [CollatzResearch.WordTrace]
  refine ⟨49609548428332880305896043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66146064571110507074528057 49609548428332880305896043)
  ·
    refine ⟨74414322642499320458844065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49609548428332880305896043 74414322642499320458844065)
    ·
      refine ⟨55810741981874490344133049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74414322642499320458844065 55810741981874490344133049)
      ·
        refine ⟨41858056486405867758099787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55810741981874490344133049 41858056486405867758099787)
        ·
          refine ⟨62787084729608801637149681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41858056486405867758099787 62787084729608801637149681)
          ·
            refine ⟨47090313547206601227862261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62787084729608801637149681 47090313547206601227862261)
            ·
              refine ⟨4414716895050618865112087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47090313547206601227862261 4414716895050618865112087)
              ·
                refine ⟨6622075342575928297668131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4414716895050618865112087 6622075342575928297668131)
                ·
                  refine ⟨9933113013863892446502197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6622075342575928297668131 9933113013863892446502197)
                  ·
                    refine ⟨931229345049739916859581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9933113013863892446502197 931229345049739916859581)
                    ·
                      rfl

theorem cell22_2720344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 1, 5].length) (baseStart_2720344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720344 prefixEnd_2720344 := by exact prefixLift 2720344
  have htrace : WordTrace (prefixWord ++ tailWord_2720344) baseStart_2720344 baseEnd_2720344 := by
    simpa [prefixWord, tailWord_2720344, baseEnd_2720344] using wordTrace_append hprefix tailTrace_2720344
  have hstable : (prefixWord ++ tailWord_2720344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720344).length < 2 ^ (prefixWord ++ tailWord_2720344).sum := by decide
  have hdescent : baseEnd_2720344 < baseStart_2720344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720348 : List Nat := [2, 2, 4, 1, 3, 1, 2, 2, 1, 4]
def baseStart_2720348 : Nat := 118140960795 + 2720348 * 2 ^ 59
def prefixEnd_2720348 : Nat := 4983230072969 + 3 ^ 40 * 2720348 * 2
def baseEnd_2720348 : Nat := 931230714331485239759569

theorem tailTrace_2720348 : CollatzResearch.WordTrace tailWord_2720348 prefixEnd_2720348 931230714331485239759569 := by
  unfold tailWord_2720348
  simp only [CollatzResearch.WordTrace]
  refine ⟨49609621374325634647468849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 66146161832434179529958465 49609621374325634647468849)
  ·
    refine ⟨37207216030744225985601637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49609621374325634647468849 37207216030744225985601637)
    ·
      refine ⟨6976353005764542372300307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37207216030744225985601637 6976353005764542372300307)
      ·
        refine ⟨10464529508646813558450461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6976353005764542372300307 10464529508646813558450461)
        ·
          refine ⟨3924198565742555084418923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10464529508646813558450461 3924198565742555084418923)
          ·
            refine ⟨5886297848613832626628385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3924198565742555084418923 5886297848613832626628385)
            ·
              refine ⟨4414723386460374469971289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5886297848613832626628385 4414723386460374469971289)
              ·
                refine ⟨3311042539845280852478467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4414723386460374469971289 3311042539845280852478467)
                ·
                  refine ⟨4966563809767921278717701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3311042539845280852478467 4966563809767921278717701)
                  ·
                    refine ⟨931230714331485239759569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966563809767921278717701 931230714331485239759569)
                    ·
                      rfl

theorem cell22_2720348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_2720348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720348 prefixEnd_2720348 := by exact prefixLift 2720348
  have htrace : WordTrace (prefixWord ++ tailWord_2720348) baseStart_2720348 baseEnd_2720348 := by
    simpa [prefixWord, tailWord_2720348, baseEnd_2720348] using wordTrace_append hprefix tailTrace_2720348
  have hstable : (prefixWord ++ tailWord_2720348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720348).length < 2 ^ (prefixWord ++ tailWord_2720348).sum := by decide
  have hdescent : baseEnd_2720348 < baseStart_2720348 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2720359 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 2, 4]
def baseStart_2720359 : Nat := 118140960795 + 2720359 * 2 ^ 59
def prefixEnd_2720359 : Nat := 4983230072969 + 3 ^ 40 * 2720359 * 2
def baseEnd_2720359 : Nat := 931234479856284877734535

theorem tailTrace_2720359 : CollatzResearch.WordTrace tailWord_2720359 prefixEnd_2720359 931234479856284877734535 := by
  unfold tailWord_2720359
  simp only [CollatzResearch.WordTrace]
  refine ⟨99219643951611418173588131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 66146429301074278782392087 99219643951611418173588131)
  ·
    refine ⟨148829465927417127260382197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99219643951611418173588131 148829465927417127260382197)
    ·
      refine ⟨13952762430695355680660831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148829465927417127260382197 13952762430695355680660831)
      ·
        refine ⟨20929143646043033520991247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13952762430695355680660831 20929143646043033520991247)
        ·
          refine ⟨31393715469064550281486871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20929143646043033520991247 31393715469064550281486871)
          ·
            refine ⟨47090573203596825422230307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31393715469064550281486871 47090573203596825422230307)
            ·
              refine ⟨70635859805395238133345461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47090573203596825422230307 70635859805395238133345461)
              ·
                refine ⟨6622111856755803575001137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70635859805395238133345461 6622111856755803575001137)
                ·
                  refine ⟨4966583892566852681250853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6622111856755803575001137 4966583892566852681250853)
                  ·
                    refine ⟨931234479856284877734535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4966583892566852681250853 931234479856284877734535)
                    ·
                      rfl

theorem cell22_2720359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_2720359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2720359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2720359 prefixEnd_2720359 := by exact prefixLift 2720359
  have htrace : WordTrace (prefixWord ++ tailWord_2720359) baseStart_2720359 baseEnd_2720359 := by
    simpa [prefixWord, tailWord_2720359, baseEnd_2720359] using wordTrace_append hprefix tailTrace_2720359
  have hstable : (prefixWord ++ tailWord_2720359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2720359).length < 2 ^ (prefixWord ++ tailWord_2720359).sum := by decide
  have hdescent : baseEnd_2720359 < baseStart_2720359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2720359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
