import V185TrunkScan23Chunk1171

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6943444 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 2, 2, 2]
def baseStart_6943444 : Nat := 118140960795 + 6943444 * 2 ^ 59
def prefixEnd_6943444 : Nat := 4983230072969 + 3 ^ 40 * 6943444 * 2
def baseEnd_6943444 : Nat := 3565324169577036977117689

theorem tailTrace_6943444 : CollatzResearch.WordTrace tailWord_6943444 prefixEnd_6943444 3565324169577036977117689 := by
  unfold tailWord_6943444
  simp only [CollatzResearch.WordTrace]
  refine ⟨126624103928547854335150693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168832138571397139113534257 126624103928547854335150693)
  ·
    refine ⟨23742019486602722687840755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126624103928547854335150693 23742019486602722687840755)
    ·
      refine ⟨35613029229904084031761133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23742019486602722687840755 35613029229904084031761133)
      ·
        refine ⟨13354885961214031511910425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35613029229904084031761133 13354885961214031511910425)
        ·
          refine ⟨10016164470910523633932819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13354885961214031511910425 10016164470910523633932819)
          ·
            refine ⟨15024246706365785450899229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016164470910523633932819 15024246706365785450899229)
            ·
              refine ⟨5634092514887169544087211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15024246706365785450899229 5634092514887169544087211)
              ·
                refine ⟨8451138772330754316130817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5634092514887169544087211 8451138772330754316130817)
                ·
                  refine ⟨6338354079248065737098113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451138772330754316130817 6338354079248065737098113)
                  ·
                    refine ⟨4753765559436049302823585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6338354079248065737098113 4753765559436049302823585)
                    ·
                      refine ⟨3565324169577036977117689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753765559436049302823585 3565324169577036977117689)
                      ·
                        rfl

theorem cell23_6943444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_6943444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943444 prefixEnd_6943444 := by exact prefixLift 6943444
  have htrace : WordTrace (prefixWord ++ tailWord_6943444) baseStart_6943444 baseEnd_6943444 := by
    simpa [prefixWord, tailWord_6943444, baseEnd_6943444] using wordTrace_append hprefix tailTrace_6943444
  have hstable : (prefixWord ++ tailWord_6943444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943444).length < 2 ^ (prefixWord ++ tailWord_6943444).sum := by decide
  have hdescent : baseEnd_6943444 < baseStart_6943444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943449 : List Nat := [1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_6943449 : Nat := 118140960795 + 6943449 * 2 ^ 59
def prefixEnd_6943449 : Nat := 4983230072969 + 3 ^ 40 * 6943449 * 2
def baseEnd_6943449 : Nat := 3565326736980309457555165

theorem tailTrace_6943449 : CollatzResearch.WordTrace tailWord_6943449 prefixEnd_6943449 3565326736980309457555165 := by
  unfold tailWord_6943449
  simp only [CollatzResearch.WordTrace]
  refine ⟨253248390222077594524233401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168832260148051729682822267 253248390222077594524233401)
  ·
    refine ⟨189936292666558195893175051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253248390222077594524233401 189936292666558195893175051)
    ·
      refine ⟨284904438999837293839762577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189936292666558195893175051 284904438999837293839762577)
      ·
        refine ⟨213678329249877970379821933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284904438999837293839762577 213678329249877970379821933)
        ·
          refine ⟨80129373468704238892433225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213678329249877970379821933 80129373468704238892433225)
          ·
            refine ⟨60097030101528179169324919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80129373468704238892433225 60097030101528179169324919)
            ·
              refine ⟨90145545152292268753987379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60097030101528179169324919 90145545152292268753987379)
              ·
                refine ⟨135218317728438403130981069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90145545152292268753987379 135218317728438403130981069)
                ·
                  refine ⟨50706869148164401174117901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135218317728438403130981069 50706869148164401174117901)
                  ·
                    refine ⟨19015075930561650440294213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50706869148164401174117901 19015075930561650440294213)
                    ·
                      refine ⟨3565326736980309457555165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19015075930561650440294213 3565326736980309457555165)
                      ·
                        rfl

theorem cell23_6943449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_6943449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943449 prefixEnd_6943449 := by exact prefixLift 6943449
  have htrace : WordTrace (prefixWord ++ tailWord_6943449) baseStart_6943449 baseEnd_6943449 := by
    simpa [prefixWord, tailWord_6943449, baseEnd_6943449] using wordTrace_append hprefix tailTrace_6943449
  have hstable : (prefixWord ++ tailWord_6943449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943449).length < 2 ^ (prefixWord ++ tailWord_6943449).sum := by decide
  have hdescent : baseEnd_6943449 < baseStart_6943449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943466 : List Nat := [3, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_6943466 : Nat := 118140960795 + 6943466 * 2 ^ 59
def prefixEnd_6943466 : Nat := 4983230072969 + 3 ^ 40 * 6943466 * 2
def baseEnd_6943466 : Nat := 3565335466151435891042587

theorem tailTrace_6943466 : CollatzResearch.WordTrace tailWord_6943466 prefixEnd_6943466 3565335466151435891042587 := by
  unfold tailWord_6943466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63312252565754001606900563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168832673508677337618401501 63312252565754001606900563)
  ·
    refine ⟨94968378848631002410350845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63312252565754001606900563 94968378848631002410350845)
    ·
      refine ⟨35613142068236625903881567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94968378848631002410350845 35613142068236625903881567)
      ·
        refine ⟨53419713102354938855822351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35613142068236625903881567 53419713102354938855822351)
        ·
          refine ⟨80129569653532408283733527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53419713102354938855822351 80129569653532408283733527)
          ·
            refine ⟨120194354480298612425600291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80129569653532408283733527 120194354480298612425600291)
            ·
              refine ⟨180291531720447918638400437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120194354480298612425600291 180291531720447918638400437)
              ·
                refine ⟨16902331098791992372350041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180291531720447918638400437 16902331098791992372350041)
                ·
                  refine ⟨12676748324093994279262531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16902331098791992372350041 12676748324093994279262531)
                  ·
                    refine ⟨19015122486140991418893797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12676748324093994279262531 19015122486140991418893797)
                    ·
                      refine ⟨3565335466151435891042587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19015122486140991418893797 3565335466151435891042587)
                      ·
                        rfl

theorem cell23_6943466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_6943466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943466 prefixEnd_6943466 := by exact prefixLift 6943466
  have htrace : WordTrace (prefixWord ++ tailWord_6943466) baseStart_6943466 baseEnd_6943466 := by
    simpa [prefixWord, tailWord_6943466, baseEnd_6943466] using wordTrace_append hprefix tailTrace_6943466
  have hstable : (prefixWord ++ tailWord_6943466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943466).length < 2 ^ (prefixWord ++ tailWord_6943466).sum := by decide
  have hdescent : baseEnd_6943466 < baseStart_6943466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943493 : List Nat := [1, 3, 1, 1, 2, 1, 1, 8, 1, 4]
def baseStart_6943493 : Nat := 118140960795 + 6943493 * 2 ^ 59
def prefixEnd_6943493 : Nat := 4983230072969 + 3 ^ 40 * 6943493 * 2
def baseEnd_6943493 : Nat := 1188449776709702428468321

theorem tailTrace_6943493 : CollatzResearch.WordTrace tailWord_6943493 prefixEnd_6943493 1188449776709702428468321 := by
  unfold tailWord_6943493
  simp only [CollatzResearch.WordTrace]
  refine ⟨253249995033918190038835133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168833330022612126692556755 253249995033918190038835133)
  ·
    refine ⟨94968748137719321264563175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253249995033918190038835133 94968748137719321264563175)
    ·
      refine ⟨142453122206578981896844763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94968748137719321264563175 142453122206578981896844763)
      ·
        refine ⟨213679683309868472845267145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142453122206578981896844763 213679683309868472845267145)
        ·
          refine ⟨160259762482401354633950359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213679683309868472845267145 160259762482401354633950359)
          ·
            refine ⟨240389643723602031950925539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160259762482401354633950359 240389643723602031950925539)
            ·
              refine ⟨360584465585403047926388309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240389643723602031950925539 360584465585403047926388309)
              ·
                refine ⟨4225599206078941967887363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 360584465585403047926388309 4225599206078941967887363)
                ·
                  refine ⟨6338398809118412951831045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225599206078941967887363 6338398809118412951831045)
                  ·
                    refine ⟨1188449776709702428468321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338398809118412951831045 1188449776709702428468321)
                    ·
                      rfl

theorem cell23_6943493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 8, 1, 4].length) (baseStart_6943493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943493 prefixEnd_6943493 := by exact prefixLift 6943493
  have htrace : WordTrace (prefixWord ++ tailWord_6943493) baseStart_6943493 baseEnd_6943493 := by
    simpa [prefixWord, tailWord_6943493, baseEnd_6943493] using wordTrace_append hprefix tailTrace_6943493
  have hstable : (prefixWord ++ tailWord_6943493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943493).length < 2 ^ (prefixWord ++ tailWord_6943493).sum := by decide
  have hdescent : baseEnd_6943493 < baseStart_6943493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943536 : List Nat := [2, 1, 1, 1, 2, 2, 1, 7, 1, 5]
def baseStart_6943536 : Nat := 118140960795 + 6943536 * 2 ^ 59
def prefixEnd_6943536 : Nat := 4983230072969 + 3 ^ 40 * 6943536 * 2
def baseEnd_6943536 : Nat := 1188457136599083539055755

theorem tailTrace_6943536 : CollatzResearch.WordTrace tailWord_6943536 prefixEnd_6943536 1188457136599083539055755 := by
  unfold tailWord_6943536
  simp only [CollatzResearch.WordTrace]
  refine ⟨126625781686381204191325231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168834375581841605588433641 126625781686381204191325231)
  ·
    refine ⟨189938672529571806286987847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126625781686381204191325231 189938672529571806286987847)
    ·
      refine ⟨284908008794357709430481771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189938672529571806286987847 284908008794357709430481771)
      ·
        refine ⟨427362013191536564145722657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284908008794357709430481771 427362013191536564145722657)
        ·
          refine ⟨320521509893652423109291993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427362013191536564145722657 320521509893652423109291993)
          ·
            refine ⟨240391132420239317331968995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320521509893652423109291993 240391132420239317331968995)
            ·
              refine ⟨360586698630358975997953493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240391132420239317331968995 360586698630358975997953493)
              ·
                refine ⟨8451250749149038499952035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 360586698630358975997953493 8451250749149038499952035)
                ·
                  refine ⟨12676876123723557749928053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8451250749149038499952035 12676876123723557749928053)
                  ·
                    refine ⟨1188457136599083539055755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12676876123723557749928053 1188457136599083539055755)
                    ·
                      rfl

theorem cell23_6943536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_6943536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943536 prefixEnd_6943536 := by exact prefixLift 6943536
  have htrace : WordTrace (prefixWord ++ tailWord_6943536) baseStart_6943536 baseEnd_6943536 := by
    simpa [prefixWord, tailWord_6943536, baseEnd_6943536] using wordTrace_append hprefix tailTrace_6943536
  have hstable : (prefixWord ++ tailWord_6943536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943536).length < 2 ^ (prefixWord ++ tailWord_6943536).sum := by decide
  have hdescent : baseEnd_6943536 < baseStart_6943536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943540 : List Nat := [2, 5, 1, 1, 3, 1, 2, 2, 6]
def baseStart_6943540 : Nat := 118140960795 + 6943540 * 2 ^ 59
def prefixEnd_6943540 : Nat := 4983230072969 + 3 ^ 40 * 6943540 * 2
def baseEnd_6943540 : Nat := 396152607079985400168583

theorem tailTrace_6943540 : CollatzResearch.WordTrace tailWord_6943540 prefixEnd_6943540 396152607079985400168583 := by
  unfold tailWord_6943540
  simp only [CollatzResearch.WordTrace]
  refine ⟨126625854632373958532898037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168834472843165278043864049 126625854632373958532898037)
  ·
    refine ⟨11871173871785058612459191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126625854632373958532898037 11871173871785058612459191)
    ·
      refine ⟨17806760807677587918688787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11871173871785058612459191 17806760807677587918688787)
      ·
        refine ⟨26710141211516381878033181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17806760807677587918688787 26710141211516381878033181)
        ·
          refine ⟨10016302954318643204262443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26710141211516381878033181 10016302954318643204262443)
          ·
            refine ⟨15024454431477964806393665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016302954318643204262443 15024454431477964806393665)
            ·
              refine ⟨11268340823608473604795249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15024454431477964806393665 11268340823608473604795249)
              ·
                refine ⟨8451255617706355203596437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11268340823608473604795249 8451255617706355203596437)
                ·
                  refine ⟨396152607079985400168583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8451255617706355203596437 396152607079985400168583)
                  ·
                    rfl

theorem cell23_6943540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_6943540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943540 prefixEnd_6943540 := by exact prefixLift 6943540
  have htrace : WordTrace (prefixWord ++ tailWord_6943540) baseStart_6943540 baseEnd_6943540 := by
    simpa [prefixWord, tailWord_6943540, baseEnd_6943540] using wordTrace_append hprefix tailTrace_6943540
  have hstable : (prefixWord ++ tailWord_6943540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943540).length < 2 ^ (prefixWord ++ tailWord_6943540).sum := by decide
  have hdescent : baseEnd_6943540 < baseStart_6943540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943543 : List Nat := [1, 1, 3, 1, 2, 1, 3, 4, 2, 3, 2]
def baseStart_6943543 : Nat := 118140960795 + 6943543 * 2 ^ 59
def prefixEnd_6943543 : Nat := 4983230072969 + 3 ^ 40 * 6943543 * 2
def baseEnd_6943543 : Nat := 3565375004161832089779733

theorem tailTrace_6943543 : CollatzResearch.WordTrace tailWord_6943543 prefixEnd_6943543 3565375004161832089779733 := by
  unfold tailWord_6943543
  simp only [CollatzResearch.WordTrace]
  refine ⟨253251818683737048578155283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168834545789158032385436855 253251818683737048578155283)
  ·
    refine ⟨379877728025605572867232925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253251818683737048578155283 379877728025605572867232925)
    ·
      refine ⟨142454148009602089825212347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379877728025605572867232925 142454148009602089825212347)
      ·
        refine ⟨213681222014403134737818521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142454148009602089825212347 213681222014403134737818521)
        ·
          refine ⟨160260916510802351053363891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213681222014403134737818521 160260916510802351053363891)
          ·
            refine ⟨240391374766203526580045837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160260916510802351053363891 240391374766203526580045837)
            ·
              refine ⟨90146765537326322467517189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240391374766203526580045837 90146765537326322467517189)
              ·
                refine ⟨16902518538248685462659473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90146765537326322467517189 16902518538248685462659473)
                ·
                  refine ⟨12676888903686514096994605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16902518538248685462659473 12676888903686514096994605)
                  ·
                    refine ⟨4753833338882442786372977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12676888903686514096994605 4753833338882442786372977)
                    ·
                      refine ⟨3565375004161832089779733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753833338882442786372977 3565375004161832089779733)
                      ·
                        rfl

theorem cell23_6943543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 4, 2, 3, 2].length) (baseStart_6943543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943543 prefixEnd_6943543 := by exact prefixLift 6943543
  have htrace : WordTrace (prefixWord ++ tailWord_6943543) baseStart_6943543 baseEnd_6943543 := by
    simpa [prefixWord, tailWord_6943543, baseEnd_6943543] using wordTrace_append hprefix tailTrace_6943543
  have hstable : (prefixWord ++ tailWord_6943543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943543).length < 2 ^ (prefixWord ++ tailWord_6943543).sum := by decide
  have hdescent : baseEnd_6943543 < baseStart_6943543 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943573 : List Nat := [1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6943573 : Nat := 118140960795 + 6943573 * 2 ^ 59
def prefixEnd_6943573 : Nat := 4983230072969 + 3 ^ 40 * 6943573 * 2
def baseEnd_6943573 : Nat := 3565390408581466972404595

theorem tailTrace_6943573 : CollatzResearch.WordTrace tailWord_6943573 prefixEnd_6943573 3565390408581466972404595 := by
  unfold tailWord_6943573
  simp only [CollatzResearch.WordTrace]
  refine ⟨253252912873628363701747373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168835275249085575801164915 253252912873628363701747373)
  ·
    refine ⟨94969842327610636388155265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253252912873628363701747373 94969842327610636388155265)
    ·
      refine ⟨71227381745707977291116449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94969842327610636388155265 71227381745707977291116449)
      ·
        refine ⟨53420536309280982968337337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71227381745707977291116449 53420536309280982968337337)
        ·
          refine ⟨40065402231960737226253003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53420536309280982968337337 40065402231960737226253003)
          ·
            refine ⟨60098103347941105839379505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40065402231960737226253003 60098103347941105839379505)
            ·
              refine ⟨45073577510955829379534629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60098103347941105839379505 45073577510955829379534629)
              ·
                refine ⟨8451295783304218008662743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45073577510955829379534629 8451295783304218008662743)
                ·
                  refine ⟨12676943674956327012994115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8451295783304218008662743 12676943674956327012994115)
                  ·
                    refine ⟨19015415512434490519491173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12676943674956327012994115 19015415512434490519491173)
                    ·
                      refine ⟨3565390408581466972404595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19015415512434490519491173 3565390408581466972404595)
                      ·
                        rfl

theorem cell23_6943573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6943573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943573 prefixEnd_6943573 := by exact prefixLift 6943573
  have htrace : WordTrace (prefixWord ++ tailWord_6943573) baseStart_6943573 baseEnd_6943573 := by
    simpa [prefixWord, tailWord_6943573, baseEnd_6943573] using wordTrace_append hprefix tailTrace_6943573
  have hstable : (prefixWord ++ tailWord_6943573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943573).length < 2 ^ (prefixWord ++ tailWord_6943573).sum := by decide
  have hdescent : baseEnd_6943573 < baseStart_6943573 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943663 : List Nat := [1, 1, 2, 1, 2, 2, 2, 1, 5, 4, 2]
def baseStart_6943663 : Nat := 118140960795 + 6943663 * 2 ^ 59
def prefixEnd_6943663 : Nat := 4983230072969 + 3 ^ 40 * 6943663 * 2
def baseEnd_6943663 : Nat := 3565436621840371620279181

theorem tailTrace_6943663 : CollatzResearch.WordTrace tailWord_6943663 prefixEnd_6943663 3565436621840371620279181 := by
  unfold tailWord_6943663
  simp only [CollatzResearch.WordTrace]
  refine ⟨253256195443302309072523643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168837463628868206048349095 253256195443302309072523643)
  ·
    refine ⟨379884293164953463608785465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253256195443302309072523643 379884293164953463608785465)
    ·
      refine ⟨284913219873715097706589099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379884293164953463608785465 284913219873715097706589099)
      ·
        refine ⟨427369829810572646559883649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284913219873715097706589099 427369829810572646559883649)
        ·
          refine ⟨320527372357929484919912737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427369829810572646559883649 320527372357929484919912737)
          ·
            refine ⟨240395529268447113689934553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320527372357929484919912737 240395529268447113689934553)
            ·
              refine ⟨180296646951335335267450915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240395529268447113689934553 180296646951335335267450915)
              ·
                refine ⟨270444970427003002901176373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180296646951335335267450915 270444970427003002901176373)
                ·
                  refine ⟨25354215977531531521985285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270444970427003002901176373 25354215977531531521985285)
                  ·
                    refine ⟨4753915495787162160372241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25354215977531531521985285 4753915495787162160372241)
                    ·
                      refine ⟨3565436621840371620279181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753915495787162160372241 3565436621840371620279181)
                      ·
                        rfl

theorem cell23_6943663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 1, 5, 4, 2].length) (baseStart_6943663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943663 prefixEnd_6943663 := by exact prefixLift 6943663
  have htrace : WordTrace (prefixWord ++ tailWord_6943663) baseStart_6943663 baseEnd_6943663 := by
    simpa [prefixWord, tailWord_6943663, baseEnd_6943663] using wordTrace_append hprefix tailTrace_6943663
  have hstable : (prefixWord ++ tailWord_6943663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943663).length < 2 ^ (prefixWord ++ tailWord_6943663).sum := by decide
  have hdescent : baseEnd_6943663 < baseStart_6943663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943684 : List Nat := [2, 3, 3, 3, 1, 1, 1, 1, 3, 3, 2]
def baseStart_6943684 : Nat := 118140960795 + 6943684 * 2 ^ 59
def prefixEnd_6943684 : Nat := 4983230072969 + 3 ^ 40 * 6943684 * 2
def baseEnd_6943684 : Nat := 3565447404934116038116585

theorem tailTrace_6943684 : CollatzResearch.WordTrace tailWord_6943684 prefixEnd_6943684 3565447404934116038116585 := by
  unfold tailWord_6943684
  simp only [CollatzResearch.WordTrace]
  refine ⟨126628480688113114829519053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168837974250817486439358737 126628480688113114829519053)
  ·
    refine ⟨47485680258042418061069645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126628480688113114829519053 47485680258042418061069645)
    ·
      refine ⟨17807130096765906772901117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47485680258042418061069645 17807130096765906772901117)
      ·
        refine ⟨6677673786287215039837919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17807130096765906772901117 6677673786287215039837919)
        ·
          refine ⟨10016510679430822559756879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6677673786287215039837919 10016510679430822559756879)
          ·
            refine ⟨15024766019146233839635319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10016510679430822559756879 15024766019146233839635319)
            ·
              refine ⟨22537149028719350759452979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15024766019146233839635319 22537149028719350759452979)
              ·
                refine ⟨33805723543079026139179469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22537149028719350759452979 33805723543079026139179469)
                ·
                  refine ⟨12677146328654634802192301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33805723543079026139179469 12677146328654634802192301)
                  ·
                    refine ⟨4753929873245488050822113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12677146328654634802192301 4753929873245488050822113)
                    ·
                      refine ⟨3565447404934116038116585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753929873245488050822113 3565447404934116038116585)
                      ·
                        rfl

theorem cell23_6943684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_6943684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943684 prefixEnd_6943684 := by exact prefixLift 6943684
  have htrace : WordTrace (prefixWord ++ tailWord_6943684) baseStart_6943684 baseEnd_6943684 := by
    simpa [prefixWord, tailWord_6943684, baseEnd_6943684] using wordTrace_append hprefix tailTrace_6943684
  have hstable : (prefixWord ++ tailWord_6943684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943684).length < 2 ^ (prefixWord ++ tailWord_6943684).sum := by decide
  have hdescent : baseEnd_6943684 < baseStart_6943684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943713 : List Nat := [1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 3]
def baseStart_6943713 : Nat := 118140960795 + 6943713 * 2 ^ 59
def prefixEnd_6943713 : Nat := 4983230072969 + 3 ^ 40 * 6943713 * 2
def baseEnd_6943713 : Nat := 3565462295873096424653951

theorem tailTrace_6943713 : CollatzResearch.WordTrace tailWord_6943713 prefixEnd_6943713 3565462295873096424653951 := by
  unfold tailWord_6943713
  simp only [CollatzResearch.WordTrace]
  refine ⟨253258019093121167611843793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168838679395414111741229195 253258019093121167611843793)
  ·
    refine ⟨189943514319840875708882845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253258019093121167611843793 189943514319840875708882845)
    ·
      refine ⟨71228817869940328390831067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189943514319840875708882845 71228817869940328390831067)
      ·
        refine ⟨106843226804910492586246601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71228817869940328390831067 106843226804910492586246601)
        ·
          refine ⟨80132420103682869439684951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106843226804910492586246601 80132420103682869439684951)
          ·
            refine ⟨120198630155524304159527427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80132420103682869439684951 120198630155524304159527427)
            ·
              refine ⟨180297945233286456239291141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120198630155524304159527427 180297945233286456239291141)
              ·
                refine ⟨33805864731241210544867089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180297945233286456239291141 33805864731241210544867089)
                ·
                  refine ⟨25354398548430907908650317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33805864731241210544867089 25354398548430907908650317)
                  ·
                    refine ⟨9507899455661590465743869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25354398548430907908650317 9507899455661590465743869)
                    ·
                      refine ⟨3565462295873096424653951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9507899455661590465743869 3565462295873096424653951)
                      ·
                        rfl

theorem cell23_6943713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_6943713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943713 prefixEnd_6943713 := by exact prefixLift 6943713
  have htrace : WordTrace (prefixWord ++ tailWord_6943713) baseStart_6943713 baseEnd_6943713 := by
    simpa [prefixWord, tailWord_6943713, baseEnd_6943713] using wordTrace_append hprefix tailTrace_6943713
  have hstable : (prefixWord ++ tailWord_6943713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943713).length < 2 ^ (prefixWord ++ tailWord_6943713).sum := by decide
  have hdescent : baseEnd_6943713 < baseStart_6943713 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943763 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 7, 4]
def baseStart_6943763 : Nat := 118140960795 + 6943763 * 2 ^ 59
def prefixEnd_6943763 : Nat := 4983230072969 + 3 ^ 40 * 6943763 * 2
def baseEnd_6943763 : Nat := 1188495989968607076342907

theorem tailTrace_6943763 : CollatzResearch.WordTrace tailWord_6943763 prefixEnd_6943763 1188495989968607076342907 := by
  unfold tailWord_6943763
  simp only [CollatzResearch.WordTrace]
  refine ⟨253259842742940026151163943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168839895161960017434109295 253259842742940026151163943)
  ·
    refine ⟨379889764114410039226745915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253259842742940026151163943 379889764114410039226745915)
    ·
      refine ⟨569834646171615058840118873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379889764114410039226745915 569834646171615058840118873)
      ·
        refine ⟨427375984628711294130089155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569834646171615058840118873 427375984628711294130089155)
        ·
          refine ⟨641063976943066941195133733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427375984628711294130089155 641063976943066941195133733)
          ·
            refine ⟨120199495676825051474087575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 641063976943066941195133733 120199495676825051474087575)
            ·
              refine ⟨180299243515237577211131363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120199495676825051474087575 180299243515237577211131363)
              ·
                refine ⟨270448865272856365816697045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180299243515237577211131363 270448865272856365816697045)
                ·
                  refine ⟨6338645279832571073828837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 270448865272856365816697045 6338645279832571073828837)
                  ·
                    refine ⟨1188495989968607076342907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338645279832571073828837 1188495989968607076342907)
                    ·
                      rfl

theorem cell23_6943763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 7, 4].length) (baseStart_6943763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943763 prefixEnd_6943763 := by exact prefixLift 6943763
  have htrace : WordTrace (prefixWord ++ tailWord_6943763) baseStart_6943763 baseEnd_6943763 := by
    simpa [prefixWord, tailWord_6943763, baseEnd_6943763] using wordTrace_append hprefix tailTrace_6943763
  have hstable : (prefixWord ++ tailWord_6943763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943763).length < 2 ^ (prefixWord ++ tailWord_6943763).sum := by decide
  have hdescent : baseEnd_6943763 < baseStart_6943763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943770 : List Nat := [3, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2]
def baseStart_6943770 : Nat := 118140960795 + 6943770 * 2 ^ 59
def prefixEnd_6943770 : Nat := 4983230072969 + 3 ^ 40 * 6943770 * 2
def baseEnd_6943770 : Nat := 3565491564270402701641189

theorem tailTrace_6943770 : CollatzResearch.WordTrace tailWord_6943770 prefixEnd_6943770 3565491564270402701641189 := by
  unfold tailWord_6943770
  simp only [CollatzResearch.WordTrace]
  refine ⟨63315024513478666586667191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168840065369276444231112509 63315024513478666586667191)
  ·
    refine ⟨94972536770217999880000787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63315024513478666586667191 94972536770217999880000787)
    ·
      refine ⟨142458805155326999820001181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94972536770217999880000787 142458805155326999820001181)
      ·
        refine ⟨53422051933247624932500443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142458805155326999820001181 53422051933247624932500443)
        ·
          refine ⟨80133077899871437398750665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53422051933247624932500443 80133077899871437398750665)
          ·
            refine ⟨60099808424903578049062999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80133077899871437398750665 60099808424903578049062999)
            ·
              refine ⟨90149712637355367073594499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60099808424903578049062999 90149712637355367073594499)
              ·
                refine ⟨135224568956033050610391749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90149712637355367073594499 135224568956033050610391749)
                ·
                  refine ⟨25354606679256196989448453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135224568956033050610391749 25354606679256196989448453)
                  ·
                    refine ⟨4753988752360536935521585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25354606679256196989448453 4753988752360536935521585)
                    ·
                      refine ⟨3565491564270402701641189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4753988752360536935521585 3565491564270402701641189)
                      ·
                        rfl

theorem cell23_6943770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 1, 4, 4, 2].length) (baseStart_6943770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943770 prefixEnd_6943770 := by exact prefixLift 6943770
  have htrace : WordTrace (prefixWord ++ tailWord_6943770) baseStart_6943770 baseEnd_6943770 := by
    simpa [prefixWord, tailWord_6943770, baseEnd_6943770] using wordTrace_append hprefix tailTrace_6943770
  have hstable : (prefixWord ++ tailWord_6943770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943770).length < 2 ^ (prefixWord ++ tailWord_6943770).sum := by decide
  have hdescent : baseEnd_6943770 < baseStart_6943770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943790 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_6943790 : Nat := 118140960795 + 6943790 * 2 ^ 59
def prefixEnd_6943790 : Nat := 4983230072969 + 3 ^ 40 * 6943790 * 2
def baseEnd_6943790 : Nat := 3565501833883492623391097

theorem tailTrace_6943790 : CollatzResearch.WordTrace tailWord_6943790 prefixEnd_6943790 3565501833883492623391097 := by
  unfold tailWord_6943790
  simp only [CollatzResearch.WordTrace]
  refine ⟨31657603439230276220299603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168840551675894806508264549 31657603439230276220299603)
  ·
    refine ⟨47486405158845414330449405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31657603439230276220299603 47486405158845414330449405)
    ·
      refine ⟨17807401934567030373918527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47486405158845414330449405 17807401934567030373918527)
      ·
        refine ⟨26711102901850545560877791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17807401934567030373918527 26711102901850545560877791)
        ·
          refine ⟨40066654352775818341316687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26711102901850545560877791 40066654352775818341316687)
          ·
            refine ⟨60099981529163727511975031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40066654352775818341316687 60099981529163727511975031)
            ·
              refine ⟨90149972293745591267962547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60099981529163727511975031 90149972293745591267962547)
              ·
                refine ⟨135224958440618386901943821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90149972293745591267962547 135224958440618386901943821)
                ·
                  refine ⟨50709359415231895088228933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135224958440618386901943821 50709359415231895088228933)
                  ·
                    refine ⟨9508004890355980329042925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50709359415231895088228933 9508004890355980329042925)
                    ·
                      refine ⟨3565501833883492623391097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9508004890355980329042925 3565501833883492623391097)
                      ·
                        rfl

theorem cell23_6943790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_6943790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943790 prefixEnd_6943790 := by exact prefixLift 6943790
  have htrace : WordTrace (prefixWord ++ tailWord_6943790) baseStart_6943790 baseEnd_6943790 := by
    simpa [prefixWord, tailWord_6943790, baseEnd_6943790] using wordTrace_append hprefix tailTrace_6943790
  have hstable : (prefixWord ++ tailWord_6943790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943790).length < 2 ^ (prefixWord ++ tailWord_6943790).sum := by decide
  have hdescent : baseEnd_6943790 < baseStart_6943790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943843 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6943843 : Nat := 118140960795 + 6943843 * 2 ^ 59
def prefixEnd_6943843 : Nat := 4983230072969 + 3 ^ 40 * 6943843 * 2
def baseEnd_6943843 : Nat := 3565529048358180916028353

theorem tailTrace_6943843 : CollatzResearch.WordTrace tailWord_6943843 prefixEnd_6943843 3565529048358180916028353 := by
  unfold tailWord_6943843
  simp only [CollatzResearch.WordTrace]
  refine ⟨253262760582650199814076183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168841840388433466542717455 253262760582650199814076183)
  ·
    refine ⟨379894140873975299721114275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253262760582650199814076183 379894140873975299721114275)
    ·
      refine ⟨569841211310962949581671413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379894140873975299721114275 569841211310962949581671413)
      ·
        refine ⟨53422613560402776523281695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 569841211310962949581671413 53422613560402776523281695)
        ·
          refine ⟨80133920340604164784922543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53422613560402776523281695 80133920340604164784922543)
          ·
            refine ⟨120200880510906247177383815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80133920340604164784922543 120200880510906247177383815)
            ·
              refine ⟨180301320766359370766075723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120200880510906247177383815 180301320766359370766075723)
              ·
                refine ⟨270451981149539056149113585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180301320766359370766075723 270451981149539056149113585)
                ·
                  refine ⟨202838985862154292111835189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270451981149539056149113585 202838985862154292111835189)
                  ·
                    refine ⟨19016154924576964885484549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 202838985862154292111835189 19016154924576964885484549)
                    ·
                      refine ⟨3565529048358180916028353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19016154924576964885484549 3565529048358180916028353)
                      ·
                        rfl

theorem cell23_6943843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6943843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943843 prefixEnd_6943843 := by exact prefixLift 6943843
  have htrace : WordTrace (prefixWord ++ tailWord_6943843) baseStart_6943843 baseEnd_6943843 := by
    simpa [prefixWord, tailWord_6943843, baseEnd_6943843] using wordTrace_append hprefix tailTrace_6943843
  have hstable : (prefixWord ++ tailWord_6943843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943843).length < 2 ^ (prefixWord ++ tailWord_6943843).sum := by decide
  have hdescent : baseEnd_6943843 < baseStart_6943843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943893 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6943893 : Nat := 118140960795 + 6943893 * 2 ^ 59
def prefixEnd_6943893 : Nat := 4983230072969 + 3 ^ 40 * 6943893 * 2
def baseEnd_6943893 : Nat := 3565554722390905720403123

theorem tailTrace_6943893 : CollatzResearch.WordTrace tailWord_6943893 prefixEnd_6943893 3565554722390905720403123 := by
  unfold tailWord_6943893
  simp only [CollatzResearch.WordTrace]
  refine ⟨253264584232469058353396333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168843056154979372235597555 253264584232469058353396333)
  ·
    refine ⟨94974219087175896882523625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253264584232469058353396333 94974219087175896882523625)
    ·
      refine ⟨71230664315381922661892719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94974219087175896882523625 71230664315381922661892719)
      ·
        refine ⟨106845996473072883992839079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71230664315381922661892719 106845996473072883992839079)
        ·
          refine ⟨160268994709609325989258619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106845996473072883992839079 160268994709609325989258619)
          ·
            refine ⟨240403492064413988983887929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160268994709609325989258619 240403492064413988983887929)
            ·
              refine ⟨180302619048310491737915947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240403492064413988983887929 180302619048310491737915947)
              ·
                refine ⟨270453928572465737606873921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180302619048310491737915947 270453928572465737606873921)
                ·
                  refine ⟨202840446429349303205155441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270453928572465737606873921 202840446429349303205155441)
                  ·
                    refine ⟨152130334822011977403866581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202840446429349303205155441 152130334822011977403866581)
                    ·
                      refine ⟨3565554722390905720403123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152130334822011977403866581 3565554722390905720403123)
                      ·
                        rfl

theorem cell23_6943893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6943893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943893 prefixEnd_6943893 := by exact prefixLift 6943893
  have htrace : WordTrace (prefixWord ++ tailWord_6943893) baseStart_6943893 baseEnd_6943893 := by
    simpa [prefixWord, tailWord_6943893, baseEnd_6943893] using wordTrace_append hprefix tailTrace_6943893
  have hstable : (prefixWord ++ tailWord_6943893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943893).length < 2 ^ (prefixWord ++ tailWord_6943893).sum := by decide
  have hdescent : baseEnd_6943893 < baseStart_6943893 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943900 : List Nat := [2, 2, 3, 2, 1, 2, 3, 8]
def baseStart_6943900 : Nat := 118140960795 + 6943900 * 2 ^ 59
def prefixEnd_6943900 : Nat := 4983230072969 + 3 ^ 40 * 6943900 * 2
def baseEnd_6943900 : Nat := 132057715435388414556133

theorem tailTrace_6943900 : CollatzResearch.WordTrace tailWord_6943900 prefixEnd_6943900 132057715435388414556133 := by
  unfold tailWord_6943900
  simp only [CollatzResearch.WordTrace]
  refine ⟨126632419771721849274450577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168843226362295799032600769 126632419771721849274450577)
  ·
    refine ⟨94974314828791386955837933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126632419771721849274450577 94974314828791386955837933)
    ·
      refine ⟨35615368060796770108439225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94974314828791386955837933 35615368060796770108439225)
      ·
        refine ⟨26711526045597577581329419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35615368060796770108439225 26711526045597577581329419)
        ·
          refine ⟨40067289068396366371994129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26711526045597577581329419 40067289068396366371994129)
          ·
            refine ⟨30050466801297274778995597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40067289068396366371994129 30050466801297274778995597)
            ·
              refine ⟨11268925050486478042123349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30050466801297274778995597 11268925050486478042123349)
              ·
                refine ⟨132057715435388414556133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11268925050486478042123349 132057715435388414556133)
                ·
                  rfl

theorem cell23_6943900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 8].length) (baseStart_6943900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943900 prefixEnd_6943900 := by exact prefixLift 6943900
  have htrace : WordTrace (prefixWord ++ tailWord_6943900) baseStart_6943900 baseEnd_6943900 := by
    simpa [prefixWord, tailWord_6943900, baseEnd_6943900] using wordTrace_append hprefix tailTrace_6943900
  have hstable : (prefixWord ++ tailWord_6943900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943900).length < 2 ^ (prefixWord ++ tailWord_6943900).sum := by decide
  have hdescent : baseEnd_6943900 < baseStart_6943900 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943911 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6943911 : Nat := 118140960795 + 6943911 * 2 ^ 59
def prefixEnd_6943911 : Nat := 4983230072969 + 3 ^ 40 * 6943911 * 2
def baseEnd_6943911 : Nat := 3565563965042686649978041

theorem tailTrace_6943911 : CollatzResearch.WordTrace tailWord_6943911 prefixEnd_6943911 3565563965042686649978041 := by
  unfold tailWord_6943911
  simp only [CollatzResearch.WordTrace]
  refine ⟨253265240746403847427551587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168843493830935898285034391 253265240746403847427551587)
  ·
    refine ⟨379897861119605771141327381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253265240746403847427551587 379897861119605771141327381)
    ·
      refine ⟨17807712239981520522249721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 379897861119605771141327381 17807712239981520522249721)
      ·
        refine ⟨13355784179986140391687291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17807712239981520522249721 13355784179986140391687291)
        ·
          refine ⟨20033676269979210587530937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13355784179986140391687291 20033676269979210587530937)
          ·
            refine ⟨15025257202484407940648203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20033676269979210587530937 15025257202484407940648203)
            ·
              refine ⟨22537885803726611910972305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15025257202484407940648203 22537885803726611910972305)
              ·
                refine ⟨16903414352794958933229229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22537885803726611910972305 16903414352794958933229229)
                ·
                  refine ⟨6338780382298109599960961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16903414352794958933229229 6338780382298109599960961)
                  ·
                    refine ⟨4754085286723582199970721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6338780382298109599960961 4754085286723582199970721)
                    ·
                      refine ⟨3565563965042686649978041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754085286723582199970721 3565563965042686649978041)
                      ·
                        rfl

theorem cell23_6943911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6943911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943911 prefixEnd_6943911 := by exact prefixLift 6943911
  have htrace : WordTrace (prefixWord ++ tailWord_6943911) baseStart_6943911 baseEnd_6943911 := by
    simpa [prefixWord, tailWord_6943911, baseEnd_6943911] using wordTrace_append hprefix tailTrace_6943911
  have hstable : (prefixWord ++ tailWord_6943911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943911).length < 2 ^ (prefixWord ++ tailWord_6943911).sum := by decide
  have hdescent : baseEnd_6943911 < baseStart_6943911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943914 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_6943914 : Nat := 118140960795 + 6943914 * 2 ^ 59
def prefixEnd_6943914 : Nat := 4983230072969 + 3 ^ 40 * 6943914 * 2
def baseEnd_6943914 : Nat := 3565565505484650138240527

theorem tailTrace_6943914 : CollatzResearch.WordTrace tailWord_6943914 prefixEnd_6943914 3565565505484650138240527 := by
  unfold tailWord_6943914
  simp only [CollatzResearch.WordTrace]
  refine ⟨63316337541348244734977699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168843566776928652626607197 63316337541348244734977699)
  ·
    refine ⟨94974506312022367102466549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63316337541348244734977699 94974506312022367102466549)
    ·
      refine ⟨8903859966752096915856239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94974506312022367102466549 8903859966752096915856239)
      ·
        refine ⟨13355789950128145373784359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8903859966752096915856239 13355789950128145373784359)
        ·
          refine ⟨20033684925192218060676539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13355789950128145373784359 20033684925192218060676539)
          ·
            refine ⟨30050527387788327091014809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20033684925192218060676539 30050527387788327091014809)
            ·
              refine ⟨22537895540841245318261107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30050527387788327091014809 22537895540841245318261107)
              ·
                refine ⟨33806843311261867977391661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22537895540841245318261107 33806843311261867977391661)
                ·
                  refine ⟨12677566241723200491521873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33806843311261867977391661 12677566241723200491521873)
                  ·
                    refine ⟨9508174681292400368641405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12677566241723200491521873 9508174681292400368641405)
                    ·
                      refine ⟨3565565505484650138240527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9508174681292400368641405 3565565505484650138240527)
                      ·
                        rfl

theorem cell23_6943914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_6943914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943914 prefixEnd_6943914 := by exact prefixLift 6943914
  have htrace : WordTrace (prefixWord ++ tailWord_6943914) baseStart_6943914 baseEnd_6943914 := by
    simpa [prefixWord, tailWord_6943914, baseEnd_6943914] using wordTrace_append hprefix tailTrace_6943914
  have hstable : (prefixWord ++ tailWord_6943914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943914).length < 2 ^ (prefixWord ++ tailWord_6943914).sum := by decide
  have hdescent : baseEnd_6943914 < baseStart_6943914 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943927 : List Nat := [1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 3]
def baseStart_6943927 : Nat := 118140960795 + 6943927 * 2 ^ 59
def prefixEnd_6943927 : Nat := 4983230072969 + 3 ^ 40 * 6943927 * 2
def baseEnd_6943927 : Nat := 3565572180733158587377967

theorem tailTrace_6943927 : CollatzResearch.WordTrace tailWord_6943927 prefixEnd_6943927 3565572180733158587377967 := by
  unfold tailWord_6943927
  simp only [CollatzResearch.WordTrace]
  refine ⟨253265824314345882160134035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168843882876230588106756023 253265824314345882160134035)
  ·
    refine ⟨379898736471518823240201053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253265824314345882160134035 379898736471518823240201053)
    ·
      refine ⟨142462026176819558715075395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379898736471518823240201053 142462026176819558715075395)
      ·
        refine ⟨213693039265229338072613093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142462026176819558715075395 213693039265229338072613093)
        ·
          refine ⟨40067444862230500888614955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213693039265229338072613093 40067444862230500888614955)
          ·
            refine ⟨60101167293345751332922433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40067444862230500888614955 60101167293345751332922433)
            ·
              refine ⟨45075875470009313499691825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60101167293345751332922433 45075875470009313499691825)
              ·
                refine ⟨33806906602506985124768869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45075875470009313499691825 33806906602506985124768869)
                ·
                  refine ⟨6338794987970059710894163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33806906602506985124768869 6338794987970059710894163)
                  ·
                    refine ⟨9508192481955089566341245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6338794987970059710894163 9508192481955089566341245)
                    ·
                      refine ⟨3565572180733158587377967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9508192481955089566341245 3565572180733158587377967)
                      ·
                        rfl

theorem cell23_6943927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 2, 4, 1, 3].length) (baseStart_6943927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943927 prefixEnd_6943927 := by exact prefixLift 6943927
  have htrace : WordTrace (prefixWord ++ tailWord_6943927) baseStart_6943927 baseEnd_6943927 := by
    simpa [prefixWord, tailWord_6943927, baseEnd_6943927] using wordTrace_append hprefix tailTrace_6943927
  have hstable : (prefixWord ++ tailWord_6943927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943927).length < 2 ^ (prefixWord ++ tailWord_6943927).sum := by decide
  have hdescent : baseEnd_6943927 < baseStart_6943927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943944 : List Nat := [2, 1, 3, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_6943944 : Nat := 118140960795 + 6943944 * 2 ^ 59
def prefixEnd_6943944 : Nat := 4983230072969 + 3 ^ 40 * 6943944 * 2
def baseEnd_6943944 : Nat := 3565580909904285020865389

theorem tailTrace_6943944 : CollatzResearch.WordTrace tailWord_6943944 prefixEnd_6943944 3565580909904285020865389 := by
  unfold tailWord_6943944
  simp only [CollatzResearch.WordTrace]
  refine ⟨126633222177642147031751443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168844296236856196042335257 126633222177642147031751443)
  ·
    refine ⟨189949833266463220547627165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126633222177642147031751443 189949833266463220547627165)
    ·
      refine ⟨71231187474923707705360187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189949833266463220547627165 71231187474923707705360187)
      ·
        refine ⟨106846781212385561558040281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71231187474923707705360187 106846781212385561558040281)
        ·
          refine ⟨80135085909289171168530211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106846781212385561558040281 80135085909289171168530211)
          ·
            refine ⟨120202628863933756752795317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80135085909289171168530211 120202628863933756752795317)
            ·
              refine ⟨11268996455993789695574561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120202628863933756752795317 11268996455993789695574561)
              ·
                refine ⟨8451747341995342271680921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11268996455993789695574561 8451747341995342271680921)
                ·
                  refine ⟨6338810506496506703760691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8451747341995342271680921 6338810506496506703760691)
                  ·
                    refine ⟨9508215759744760055641037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6338810506496506703760691 9508215759744760055641037)
                    ·
                      refine ⟨3565580909904285020865389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9508215759744760055641037 3565580909904285020865389)
                      ·
                        rfl

theorem cell23_6943944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_6943944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943944 prefixEnd_6943944 := by exact prefixLift 6943944
  have htrace : WordTrace (prefixWord ++ tailWord_6943944) baseStart_6943944 baseEnd_6943944 := by
    simpa [prefixWord, tailWord_6943944, baseEnd_6943944] using wordTrace_append hprefix tailTrace_6943944
  have hstable : (prefixWord ++ tailWord_6943944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943944).length < 2 ^ (prefixWord ++ tailWord_6943944).sum := by decide
  have hdescent : baseEnd_6943944 < baseStart_6943944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6943958 : List Nat := [5, 2, 1, 2, 3, 1, 1, 1, 1, 2, 4]
def baseStart_6943958 : Nat := 118140960795 + 6943958 * 2 ^ 59
def prefixEnd_6943958 : Nat := 4983230072969 + 3 ^ 40 * 6943958 * 2
def baseEnd_6943958 : Nat := 3565588098633447966090325

theorem tailTrace_6943958 : CollatzResearch.WordTrace tailWord_6943958 prefixEnd_6943958 3565588098633447966090325 := by
  unfold tailWord_6943958
  simp only [CollatzResearch.WordTrace]
  refine ⟨15829184686077098403407033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168844636651489049636341685 15829184686077098403407033)
  ·
    refine ⟨11871888514557823802555275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15829184686077098403407033 11871888514557823802555275)
    ·
      refine ⟨17807832771836735703832913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11871888514557823802555275 17807832771836735703832913)
      ·
        refine ⟨13355874578877551777874685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17807832771836735703832913 13355874578877551777874685)
        ·
          refine ⟨5008452967079081916703007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13355874578877551777874685 5008452967079081916703007)
          ·
            refine ⟨7512679450618622875054511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5008452967079081916703007 7512679450618622875054511)
            ·
              refine ⟨11269019175927934312581767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7512679450618622875054511 11269019175927934312581767)
              ·
                refine ⟨16903528763891901468872651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11269019175927934312581767 16903528763891901468872651)
                ·
                  refine ⟨25355293145837852203308977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16903528763891901468872651 25355293145837852203308977)
                  ·
                    refine ⟨19016469859378389152481733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25355293145837852203308977 19016469859378389152481733)
                    ·
                      refine ⟨3565588098633447966090325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19016469859378389152481733 3565588098633447966090325)
                      ·
                        rfl

theorem cell23_6943958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_6943958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6943958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6943958 prefixEnd_6943958 := by exact prefixLift 6943958
  have htrace : WordTrace (prefixWord ++ tailWord_6943958) baseStart_6943958 baseEnd_6943958 := by
    simpa [prefixWord, tailWord_6943958, baseEnd_6943958] using wordTrace_append hprefix tailTrace_6943958
  have hstable : (prefixWord ++ tailWord_6943958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6943958).length < 2 ^ (prefixWord ++ tailWord_6943958).sum := by decide
  have hdescent : baseEnd_6943958 < baseStart_6943958 := by decide
  rcases family_descends (prefixWord ++ tailWord_6943958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944037 : List Nat := [1, 3, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_6944037 : Nat := 118140960795 + 6944037 * 2 ^ 59
def prefixEnd_6944037 : Nat := 4983230072969 + 3 ^ 40 * 6944037 * 2
def baseEnd_6944037 : Nat := 1188542887868384385667487

theorem tailTrace_6944037 : CollatzResearch.WordTrace tailWord_6944037 prefixEnd_6944037 1188542887868384385667487 := by
  unfold tailWord_6944037
  simp only [CollatzResearch.WordTrace]
  refine ⟨253269836343947370946638365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168846557562631580631092243 253269836343947370946638365)
  ·
    refine ⟨94976188628980264104989387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253269836343947370946638365 94976188628980264104989387)
    ·
      refine ⟨142464282943470396157484081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94976188628980264104989387 142464282943470396157484081)
      ·
        refine ⟨106848212207602797118113061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142464282943470396157484081 106848212207602797118113061)
        ·
          refine ⟨20034039788925524459646199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106848212207602797118113061 20034039788925524459646199)
          ·
            refine ⟨30051059683388286689469299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20034039788925524459646199 30051059683388286689469299)
            ·
              refine ⟨45076589525082430034203949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30051059683388286689469299 45076589525082430034203949)
              ·
                refine ⟨16903721071905911262826481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45076589525082430034203949 16903721071905911262826481)
                ·
                  refine ⟨12677790803929433447119861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16903721071905911262826481 12677790803929433447119861)
                  ·
                    refine ⟨1188542887868384385667487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12677790803929433447119861 1188542887868384385667487)
                    ·
                      rfl

theorem cell23_6944037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_6944037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944037 prefixEnd_6944037 := by exact prefixLift 6944037
  have htrace : WordTrace (prefixWord ++ tailWord_6944037) baseStart_6944037 baseEnd_6944037 := by
    simpa [prefixWord, tailWord_6944037, baseEnd_6944037] using wordTrace_append hprefix tailTrace_6944037
  have hstable : (prefixWord ++ tailWord_6944037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944037).length < 2 ^ (prefixWord ++ tailWord_6944037).sum := by decide
  have hdescent : baseEnd_6944037 < baseStart_6944037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944067 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 3, 4]
def baseStart_6944067 : Nat := 118140960795 + 6944067 * 2 ^ 59
def prefixEnd_6944067 : Nat := 4983230072969 + 3 ^ 40 * 6944067 * 2
def baseEnd_6944067 : Nat := 1188548022674929346542441

theorem tailTrace_6944067 : CollatzResearch.WordTrace tailWord_6944067 prefixEnd_6944067 1188548022674929346542441 := by
  unfold tailWord_6944067
  simp only [CollatzResearch.WordTrace]
  refine ⟨253270930533838686070230455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168847287022559124046820303 253270930533838686070230455)
  ·
    refine ⟨379906395800758029105345683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253270930533838686070230455 379906395800758029105345683)
    ·
      refine ⟨569859593701137043658018525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379906395800758029105345683 569859593701137043658018525)
      ·
        refine ⟨213697347637926391371756947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569859593701137043658018525 213697347637926391371756947)
        ·
          refine ⟨320546021456889587057635421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213697347637926391371756947 320546021456889587057635421)
          ·
            refine ⟨120204758046333595146613283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320546021456889587057635421 120204758046333595146613283)
            ·
              refine ⟨180307137069500392719919925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120204758046333595146613283 180307137069500392719919925)
              ·
                refine ⟨16903794100265661817492493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180307137069500392719919925 16903794100265661817492493)
                ·
                  refine ⟨6338922787599623181559685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16903794100265661817492493 6338922787599623181559685)
                  ·
                    refine ⟨1188548022674929346542441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338922787599623181559685 1188548022674929346542441)
                    ·
                      rfl

theorem cell23_6944067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 4].length) (baseStart_6944067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944067 prefixEnd_6944067 := by exact prefixLift 6944067
  have htrace : WordTrace (prefixWord ++ tailWord_6944067) baseStart_6944067 baseEnd_6944067 := by
    simpa [prefixWord, tailWord_6944067, baseEnd_6944067] using wordTrace_append hprefix tailTrace_6944067
  have hstable : (prefixWord ++ tailWord_6944067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944067).length < 2 ^ (prefixWord ++ tailWord_6944067).sum := by decide
  have hdescent : baseEnd_6944067 < baseStart_6944067 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944084 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 3, 4]
def baseStart_6944084 : Nat := 118140960795 + 6944084 * 2 ^ 59
def prefixEnd_6944084 : Nat := 4983230072969 + 3 ^ 40 * 6944084 * 2
def baseEnd_6944084 : Nat := 1188550932398638157704915

theorem tailTrace_6944084 : CollatzResearch.WordTrace tailWord_6944084 prefixEnd_6944084 1188550932398638157704915 := by
  unfold tailWord_6944084
  simp only [CollatzResearch.WordTrace]
  refine ⟨126635775287388548986799653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168847700383184731982399537 126635775287388548986799653)
  ·
    refine ⟨23744207866385352935024935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126635775287388548986799653 23744207866385352935024935)
    ·
      refine ⟨35616311799578029402537403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23744207866385352935024935 35616311799578029402537403)
      ·
        refine ⟨53424467699367044103806105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35616311799578029402537403 53424467699367044103806105)
        ·
          refine ⟨40068350774525283077854579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53424467699367044103806105 40068350774525283077854579)
          ·
            refine ⟨60102526161787924616781869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40068350774525283077854579 60102526161787924616781869)
            ·
              refine ⟨22538447310670471731293201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60102526161787924616781869 22538447310670471731293201)
              ·
                refine ⟨16903835483002853798469901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22538447310670471731293201 16903835483002853798469901)
                ·
                  refine ⟨6338938306126070174426213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16903835483002853798469901 6338938306126070174426213)
                  ·
                    refine ⟨1188550932398638157704915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338938306126070174426213 1188550932398638157704915)
                    ·
                      rfl

theorem cell23_6944084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 3, 4].length) (baseStart_6944084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944084 prefixEnd_6944084 := by exact prefixLift 6944084
  have htrace : WordTrace (prefixWord ++ tailWord_6944084) baseStart_6944084 baseEnd_6944084 := by
    simpa [prefixWord, tailWord_6944084, baseEnd_6944084] using wordTrace_append hprefix tailTrace_6944084
  have hstable : (prefixWord ++ tailWord_6944084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944084).length < 2 ^ (prefixWord ++ tailWord_6944084).sum := by decide
  have hdescent : baseEnd_6944084 < baseStart_6944084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944101 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 1, 4]
def baseStart_6944101 : Nat := 118140960795 + 6944101 * 2 ^ 59
def prefixEnd_6944101 : Nat := 4983230072969 + 3 ^ 40 * 6944101 * 2
def baseEnd_6944101 : Nat := 1188553842122346968867389

theorem tailTrace_6944101 : CollatzResearch.WordTrace tailWord_6944101 prefixEnd_6944101 1188553842122346968867389 := by
  unfold tailWord_6944101
  simp only [CollatzResearch.WordTrace]
  refine ⟨253272170615715509876968157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168848113743810339917978771 253272170615715509876968157)
  ·
    refine ⟨94977063980893316203863059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253272170615715509876968157 94977063980893316203863059)
    ·
      refine ⟨142465595971339974305794589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94977063980893316203863059 142465595971339974305794589)
      ·
        refine ⟨53424598489252490364672971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142465595971339974305794589 53424598489252490364672971)
        ·
          refine ⟨80136897733878735547009457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53424598489252490364672971 80136897733878735547009457)
          ·
            refine ⟨60102673300409051660257093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80136897733878735547009457 60102673300409051660257093)
            ·
              refine ⟨11269251243826697186298205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60102673300409051660257093 11269251243826697186298205)
              ·
                refine ⟨4225969216435011444861827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11269251243826697186298205 4225969216435011444861827)
                ·
                  refine ⟨6338953824652517167292741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4225969216435011444861827 6338953824652517167292741)
                  ·
                    refine ⟨1188553842122346968867389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6338953824652517167292741 1188553842122346968867389)
                    ·
                      rfl

theorem cell23_6944101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 1, 4].length) (baseStart_6944101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944101 prefixEnd_6944101 := by exact prefixLift 6944101
  have htrace : WordTrace (prefixWord ++ tailWord_6944101) baseStart_6944101 baseEnd_6944101 := by
    simpa [prefixWord, tailWord_6944101, baseEnd_6944101] using wordTrace_append hprefix tailTrace_6944101
  have hstable : (prefixWord ++ tailWord_6944101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944101).length < 2 ^ (prefixWord ++ tailWord_6944101).sum := by decide
  have hdescent : baseEnd_6944101 < baseStart_6944101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944177 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6944177 : Nat := 118140960795 + 6944177 * 2 ^ 59
def prefixEnd_6944177 : Nat := 4983230072969 + 3 ^ 40 * 6944177 * 2
def baseEnd_6944177 : Nat := 3565700550896782609251817

theorem tailTrace_6944177 : CollatzResearch.WordTrace tailWord_6944177 prefixEnd_6944177 3565700550896782609251817 := by
  unfold tailWord_6944177
  simp only [CollatzResearch.WordTrace]
  refine ⟨253274942563440174856734785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168849961708960116571156523 253274942563440174856734785)
  ·
    refine ⟨189956206922580131142551089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253274942563440174856734785 189956206922580131142551089)
    ·
      refine ⟨142467155191935098356913317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189956206922580131142551089 142467155191935098356913317)
      ·
        refine ⟨26712591598487830941921247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142467155191935098356913317 26712591598487830941921247)
        ·
          refine ⟨40068887397731746412881871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26712591598487830941921247 40068887397731746412881871)
          ·
            refine ⟨60103331096597619619322807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40068887397731746412881871 60103331096597619619322807)
            ·
              refine ⟨90154996644896429428984211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60103331096597619619322807 90154996644896429428984211)
              ·
                refine ⟨135232494967344644143476317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90154996644896429428984211 135232494967344644143476317)
                ·
                  refine ⟨50712185612754241553803619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135232494967344644143476317 50712185612754241553803619)
                  ·
                    refine ⟨76068278419131362330705429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50712185612754241553803619 76068278419131362330705429)
                    ·
                      refine ⟨3565700550896782609251817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76068278419131362330705429 3565700550896782609251817)
                      ·
                        rfl

theorem cell23_6944177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6944177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944177 prefixEnd_6944177 := by exact prefixLift 6944177
  have htrace : WordTrace (prefixWord ++ tailWord_6944177) baseStart_6944177 baseEnd_6944177 := by
    simpa [prefixWord, tailWord_6944177, baseEnd_6944177] using wordTrace_append hprefix tailTrace_6944177
  have hstable : (prefixWord ++ tailWord_6944177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944177).length < 2 ^ (prefixWord ++ tailWord_6944177).sum := by decide
  have hdescent : baseEnd_6944177 < baseStart_6944177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944218 : List Nat := [3, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3]
def baseStart_6944218 : Nat := 118140960795 + 6944218 * 2 ^ 59
def prefixEnd_6944218 : Nat := 4983230072969 + 3 ^ 40 * 6944218 * 2
def baseEnd_6944218 : Nat := 3565721603603616948839129

theorem tailTrace_6944218 : CollatzResearch.WordTrace tailWord_6944218 prefixEnd_6944218 3565721603603616948839129 := by
  unfold tailWord_6944218
  simp only [CollatzResearch.WordTrace]
  refine ⟨63319109489072909714744327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168850958637527759239318205 63319109489072909714744327)
  ·
    refine ⟨94978664233609364572116491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63319109489072909714744327 94978664233609364572116491)
    ·
      refine ⟨142467996350414046858174737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94978664233609364572116491 142467996350414046858174737)
      ·
        refine ⟨106850997262810535143631053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142467996350414046858174737 106850997262810535143631053)
        ·
          refine ⟨40069123973553950678861645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106850997262810535143631053 40069123973553950678861645)
          ·
            refine ⟨15025921490082731504573117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40069123973553950678861645 15025921490082731504573117)
            ·
              refine ⟨5634720558781024314214919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15025921490082731504573117 5634720558781024314214919)
              ·
                refine ⟨8452080838171536471322379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5634720558781024314214919 8452080838171536471322379)
                ·
                  refine ⟨12678121257257304706983569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8452080838171536471322379 12678121257257304706983569)
                  ·
                    refine ⟨9508590942942978530237677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12678121257257304706983569 9508590942942978530237677)
                    ·
                      refine ⟨3565721603603616948839129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9508590942942978530237677 3565721603603616948839129)
                      ·
                        rfl

theorem cell23_6944218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3].length) (baseStart_6944218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944218 prefixEnd_6944218 := by exact prefixLift 6944218
  have htrace : WordTrace (prefixWord ++ tailWord_6944218) baseStart_6944218 baseEnd_6944218 := by
    simpa [prefixWord, tailWord_6944218, baseEnd_6944218] using wordTrace_append hprefix tailTrace_6944218
  have hstable : (prefixWord ++ tailWord_6944218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944218).length < 2 ^ (prefixWord ++ tailWord_6944218).sum := by decide
  have hdescent : baseEnd_6944218 < baseStart_6944218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944241 : List Nat := [1, 2, 2, 2, 3, 2, 1, 2, 3, 3, 2]
def baseStart_6944241 : Nat := 118140960795 + 6944241 * 2 ^ 59
def prefixEnd_6944241 : Nat := 4983230072969 + 3 ^ 40 * 6944241 * 2
def baseEnd_6944241 : Nat := 3565733413658670358851523

theorem tailTrace_6944241 : CollatzResearch.WordTrace tailWord_6944241 prefixEnd_6944241 3565733413658670358851523 := by
  unfold tailWord_6944241
  simp only [CollatzResearch.WordTrace]
  refine ⟨253277276835208313787064577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168851517890138875858043051 253277276835208313787064577)
  ·
    refine ⟨189957957626406235340298433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253277276835208313787064577 189957957626406235340298433)
    ·
      refine ⟨142468468219804676505223825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189957957626406235340298433 142468468219804676505223825)
      ·
        refine ⟨106851351164853507378917869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142468468219804676505223825 106851351164853507378917869)
        ·
          refine ⟨40069256686820065267094201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106851351164853507378917869 40069256686820065267094201)
          ·
            refine ⟨30051942515115048950320651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40069256686820065267094201 30051942515115048950320651)
            ·
              refine ⟨45077913772672573425480977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30051942515115048950320651 45077913772672573425480977)
              ·
                refine ⟨33808435329504430069110733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45077913772672573425480977 33808435329504430069110733)
                ·
                  refine ⟨12678163248564161275916525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33808435329504430069110733 12678163248564161275916525)
                  ·
                    refine ⟨4754311218211560478468697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12678163248564161275916525 4754311218211560478468697)
                    ·
                      refine ⟨3565733413658670358851523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754311218211560478468697 3565733413658670358851523)
                      ·
                        rfl

theorem cell23_6944241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_6944241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944241 prefixEnd_6944241 := by exact prefixLift 6944241
  have htrace : WordTrace (prefixWord ++ tailWord_6944241) baseStart_6944241 baseEnd_6944241 := by
    simpa [prefixWord, tailWord_6944241, baseEnd_6944241] using wordTrace_append hprefix tailTrace_6944241
  have hstable : (prefixWord ++ tailWord_6944241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944241).length < 2 ^ (prefixWord ++ tailWord_6944241).sum := by decide
  have hdescent : baseEnd_6944241 < baseStart_6944241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944269 : List Nat := [1, 7, 1, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6944269 : Nat := 118140960795 + 6944269 * 2 ^ 59
def prefixEnd_6944269 : Nat := 4983230072969 + 3 ^ 40 * 6944269 * 2
def baseEnd_6944269 : Nat := 3565747791116996249301395

theorem tailTrace_6944269 : CollatzResearch.WordTrace tailWord_6944269 prefixEnd_6944269 3565747791116996249301395 := by
  unfold tailWord_6944269
  simp only [CollatzResearch.WordTrace]
  refine ⟨253278298079106874569083861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168852198719404583046055907 253278298079106874569083861)
  ·
    refine ⟨5936210111229067372712903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 253278298079106874569083861 5936210111229067372712903)
    ·
      refine ⟨8904315166843601059069355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5936210111229067372712903 8904315166843601059069355)
      ·
        refine ⟨13356472750265401588604033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8904315166843601059069355 13356472750265401588604033)
        ·
          refine ⟨10017354562699051191453025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13356472750265401588604033 10017354562699051191453025)
          ·
            refine ⟨7513015922024288393589769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10017354562699051191453025 7513015922024288393589769)
            ·
              refine ⟨5634761941518216295192327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7513015922024288393589769 5634761941518216295192327)
              ·
                refine ⟨8452142912277324442788491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5634761941518216295192327 8452142912277324442788491)
                ·
                  refine ⟨12678214368415986664182737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8452142912277324442788491 12678214368415986664182737)
                  ·
                    refine ⟨9508660776311989998137053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12678214368415986664182737 9508660776311989998137053)
                    ·
                      refine ⟨3565747791116996249301395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9508660776311989998137053 3565747791116996249301395)
                      ·
                        rfl

theorem cell23_6944269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6944269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944269 prefixEnd_6944269 := by exact prefixLift 6944269
  have htrace : WordTrace (prefixWord ++ tailWord_6944269) baseStart_6944269 baseEnd_6944269 := by
    simpa [prefixWord, tailWord_6944269, baseEnd_6944269] using wordTrace_append hprefix tailTrace_6944269
  have hstable : (prefixWord ++ tailWord_6944269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944269).length < 2 ^ (prefixWord ++ tailWord_6944269).sum := by decide
  have hdescent : baseEnd_6944269 < baseStart_6944269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944275 : List Nat := [1, 1, 1, 2, 1, 8, 2, 1, 1, 3, 2]
def baseStart_6944275 : Nat := 118140960795 + 6944275 * 2 ^ 59
def prefixEnd_6944275 : Nat := 4983230072969 + 3 ^ 40 * 6944275 * 2
def baseEnd_6944275 : Nat := 3565750872000923225826367

theorem tailTrace_6944275 : CollatzResearch.WordTrace tailWord_6944275 prefixEnd_6944275 3565750872000923225826367 := by
  unfold tailWord_6944275
  simp only [CollatzResearch.WordTrace]
  refine ⟨253278516917085137593802279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168852344611390091729201519 253278516917085137593802279)
  ·
    refine ⟨379917775375627706390703419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253278516917085137593802279 379917775375627706390703419)
    ·
      refine ⟨569876663063441559586055129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379917775375627706390703419 569876663063441559586055129)
      ·
        refine ⟨427407497297581169689541347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 569876663063441559586055129 427407497297581169689541347)
        ·
          refine ⟨641111245946371754534312021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427407497297581169689541347 641111245946371754534312021)
          ·
            refine ⟨7513022413434043998448969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 641111245946371754534312021 7513022413434043998448969)
            ·
              refine ⟨5634766810075532998836727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7513022413434043998448969 5634766810075532998836727)
              ·
                refine ⟨8452150215113299498255091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5634766810075532998836727 8452150215113299498255091)
                ·
                  refine ⟨12678225322669949247382637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8452150215113299498255091 12678225322669949247382637)
                  ·
                    refine ⟨4754334496001230967768489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12678225322669949247382637 4754334496001230967768489)
                    ·
                      refine ⟨3565750872000923225826367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754334496001230967768489 3565750872000923225826367)
                      ·
                        rfl

theorem cell23_6944275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 2, 1, 1, 3, 2].length) (baseStart_6944275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944275 prefixEnd_6944275 := by exact prefixLift 6944275
  have htrace : WordTrace (prefixWord ++ tailWord_6944275) baseStart_6944275 baseEnd_6944275 := by
    simpa [prefixWord, tailWord_6944275, baseEnd_6944275] using wordTrace_append hprefix tailTrace_6944275
  have hstable : (prefixWord ++ tailWord_6944275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944275).length < 2 ^ (prefixWord ++ tailWord_6944275).sum := by decide
  have hdescent : baseEnd_6944275 < baseStart_6944275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944284 : List Nat := [2, 2, 3, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6944284 : Nat := 118140960795 + 6944284 * 2 ^ 59
def prefixEnd_6944284 : Nat := 4983230072969 + 3 ^ 40 * 6944284 * 2
def baseEnd_6944284 : Nat := 3565755493326813690613825

theorem tailTrace_6944284 : CollatzResearch.WordTrace tailWord_6944284 prefixEnd_6944284 3565755493326813690613825 := by
  unfold tailWord_6944284
  simp only [CollatzResearch.WordTrace]
  refine ⟨126639422587026266065439953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168852563449368354753919937 126639422587026266065439953)
  ·
    refine ⟨94979566940269699549079965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126639422587026266065439953 94979566940269699549079965)
    ·
      refine ⟨35617337602601137330904987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94979566940269699549079965 35617337602601137330904987)
      ·
        refine ⟨53426006403901705996357481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35617337602601137330904987 53426006403901705996357481)
        ·
          refine ⟨40069504802926279497268111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53426006403901705996357481 40069504802926279497268111)
          ·
            refine ⟨60104257204389419245902167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40069504802926279497268111 60104257204389419245902167)
            ·
              refine ⟨90156385806584128868853251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60104257204389419245902167 90156385806584128868853251)
              ·
                refine ⟨135234578709876193303279877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90156385806584128868853251 135234578709876193303279877)
                ·
                  refine ⟨25356483508101786244364977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 135234578709876193303279877 25356483508101786244364977)
                  ·
                    refine ⟨19017362631076339683273733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25356483508101786244364977 19017362631076339683273733)
                    ·
                      refine ⟨3565755493326813690613825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19017362631076339683273733 3565755493326813690613825)
                      ·
                        rfl

theorem cell23_6944284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6944284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944284 prefixEnd_6944284 := by exact prefixLift 6944284
  have htrace : WordTrace (prefixWord ++ tailWord_6944284) baseStart_6944284 baseEnd_6944284 := by
    simpa [prefixWord, tailWord_6944284, baseEnd_6944284] using wordTrace_append hprefix tailTrace_6944284
  have hstable : (prefixWord ++ tailWord_6944284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944284).length < 2 ^ (prefixWord ++ tailWord_6944284).sum := by decide
  have hdescent : baseEnd_6944284 < baseStart_6944284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944334 : List Nat := [4, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6944334 : Nat := 118140960795 + 6944334 * 2 ^ 59
def prefixEnd_6944334 : Nat := 4983230072969 + 3 ^ 40 * 6944334 * 2
def baseEnd_6944334 : Nat := 3565781167359538494988595

theorem tailTrace_6944334 : CollatzResearch.WordTrace tailWord_6944334 prefixEnd_6944334 3565781167359538494988595 := by
  unfold tailWord_6944334
  simp only [CollatzResearch.WordTrace]
  refine ⟨31660083602983923833775007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168853779215914260446800037 31660083602983923833775007)
  ·
    refine ⟨47490125404475885750662511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31660083602983923833775007 47490125404475885750662511)
    ·
      refine ⟨71235188106713828625993767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47490125404475885750662511 71235188106713828625993767)
      ·
        refine ⟨106852782160070742938990651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71235188106713828625993767 106852782160070742938990651)
        ·
          refine ⟨160279173240106114408485977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106852782160070742938990651 160279173240106114408485977)
          ·
            refine ⟨120209379930079585806364483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160279173240106114408485977 120209379930079585806364483)
            ·
              refine ⟨180314069895119378709546725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120209379930079585806364483 180314069895119378709546725)
              ·
                refine ⟨33808888105334883508040011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 180314069895119378709546725 33808888105334883508040011)
                ·
                  refine ⟨50713332158002325262060017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33808888105334883508040011 50713332158002325262060017)
                  ·
                    refine ⟨38034999118501743946545013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50713332158002325262060017 38034999118501743946545013)
                    ·
                      refine ⟨3565781167359538494988595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38034999118501743946545013 3565781167359538494988595)
                      ·
                        rfl

theorem cell23_6944334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6944334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944334 prefixEnd_6944334 := by exact prefixLift 6944334
  have htrace : WordTrace (prefixWord ++ tailWord_6944334) baseStart_6944334 baseEnd_6944334 := by
    simpa [prefixWord, tailWord_6944334, baseEnd_6944334] using wordTrace_append hprefix tailTrace_6944334
  have hstable : (prefixWord ++ tailWord_6944334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944334).length < 2 ^ (prefixWord ++ tailWord_6944334).sum := by decide
  have hdescent : baseEnd_6944334 < baseStart_6944334 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944361 : List Nat := [1, 2, 1, 1, 1, 4, 2, 3, 2, 4, 2]
def baseStart_6944361 : Nat := 118140960795 + 6944361 * 2 ^ 59
def prefixEnd_6944361 : Nat := 4983230072969 + 3 ^ 40 * 6944361 * 2
def baseEnd_6944361 : Nat := 3565795031337209889350971

theorem tailTrace_6944361 : CollatzResearch.WordTrace tailWord_6944361 prefixEnd_6944361 3565795031337209889350971 := by
  unfold tailWord_6944361
  simp only [CollatzResearch.WordTrace]
  refine ⟨253281653594773574281432937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168854435729849049520955291 253281653594773574281432937)
  ·
    refine ⟨189961240196080180711074703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253281653594773574281432937 189961240196080180711074703)
    ·
      refine ⟨284941860294120271066612055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189961240196080180711074703 284941860294120271066612055)
      ·
        refine ⟨427412790441180406599918083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284941860294120271066612055 427412790441180406599918083)
        ·
          refine ⟨641119185661770609899877125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427412790441180406599918083 641119185661770609899877125)
          ·
            refine ⟨120209847311581989356226961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 641119185661770609899877125 120209847311581989356226961)
            ·
              refine ⟨90157385483686492017170221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120209847311581989356226961 90157385483686492017170221)
              ·
                refine ⟨33809019556382434506438833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90157385483686492017170221 33809019556382434506438833)
                ·
                  refine ⟨25356764667286825879829125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33809019556382434506438833 25356764667286825879829125)
                  ·
                    refine ⟨4754393375116279852467961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25356764667286825879829125 4754393375116279852467961)
                    ·
                      refine ⟨3565795031337209889350971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754393375116279852467961 3565795031337209889350971)
                      ·
                        rfl

theorem cell23_6944361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 3, 2, 4, 2].length) (baseStart_6944361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944361 prefixEnd_6944361 := by exact prefixLift 6944361
  have htrace : WordTrace (prefixWord ++ tailWord_6944361) baseStart_6944361 baseEnd_6944361 := by
    simpa [prefixWord, tailWord_6944361, baseEnd_6944361] using wordTrace_append hprefix tailTrace_6944361
  have hstable : (prefixWord ++ tailWord_6944361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944361).length < 2 ^ (prefixWord ++ tailWord_6944361).sum := by decide
  have hdescent : baseEnd_6944361 < baseStart_6944361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944398 : List Nat := [4, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6944398 : Nat := 118140960795 + 6944398 * 2 ^ 59
def prefixEnd_6944398 : Nat := 4983230072969 + 3 ^ 40 * 6944398 * 2
def baseEnd_6944398 : Nat := 3565814030121426244588301

theorem tailTrace_6944398 : CollatzResearch.WordTrace tailWord_6944398 prefixEnd_6944398 3565814030121426244588301 := by
  unfold tailWord_6944398
  simp only [CollatzResearch.WordTrace]
  refine ⟨31660375386954941200066231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168855335397093019733686565 31660375386954941200066231)
  ·
    refine ⟨47490563080432411800099347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31660375386954941200066231 47490563080432411800099347)
    ·
      refine ⟨71235844620648617700149021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47490563080432411800099347 71235844620648617700149021)
      ·
        refine ⟨26713441732743231637555883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71235844620648617700149021 26713441732743231637555883)
        ·
          refine ⟨40070162599114847456333825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26713441732743231637555883 40070162599114847456333825)
          ·
            refine ⟨30052621949336135592250369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40070162599114847456333825 30052621949336135592250369)
            ·
              refine ⟨22539466462002101694187777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30052621949336135592250369 22539466462002101694187777)
              ·
                refine ⟨16904599846501576270640833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22539466462002101694187777 16904599846501576270640833)
                ·
                  refine ⟨12678449884876182202980625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16904599846501576270640833 12678449884876182202980625)
                  ·
                    refine ⟨9508837413657136652235469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12678449884876182202980625 9508837413657136652235469)
                    ·
                      refine ⟨3565814030121426244588301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9508837413657136652235469 3565814030121426244588301)
                      ·
                        rfl

theorem cell23_6944398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6944398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944398 prefixEnd_6944398 := by exact prefixLift 6944398
  have htrace : WordTrace (prefixWord ++ tailWord_6944398) baseStart_6944398 baseEnd_6944398 := by
    simpa [prefixWord, tailWord_6944398, baseEnd_6944398] using wordTrace_append hprefix tailTrace_6944398
  have hstable : (prefixWord ++ tailWord_6944398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944398).length < 2 ^ (prefixWord ++ tailWord_6944398).sum := by decide
  have hdescent : baseEnd_6944398 < baseStart_6944398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944431 : List Nat := [1, 1, 2, 1, 2, 4, 2, 4, 1, 5]
def baseStart_6944431 : Nat := 118140960795 + 6944431 * 2 ^ 59
def prefixEnd_6944431 : Nat := 4983230072969 + 3 ^ 40 * 6944431 * 2
def baseEnd_6944431 : Nat := 1188610324994341538491883

theorem tailTrace_6944431 : CollatzResearch.WordTrace tailWord_6944431 prefixEnd_6944431 1188610324994341538491883 := by
  unfold tailWord_6944431
  simp only [CollatzResearch.WordTrace]
  refine ⟨253284206704519976236481147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168856137803013317490987431 253284206704519976236481147)
  ·
    refine ⟨379926310056779964354721721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253284206704519976236481147 379926310056779964354721721)
    ·
      refine ⟨284944732542584973266041291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379926310056779964354721721 284944732542584973266041291)
      ·
        refine ⟨427417098813877459899061937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284944732542584973266041291 427417098813877459899061937)
        ·
          refine ⟨320562824110408094924296453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427417098813877459899061937 320562824110408094924296453)
          ·
            refine ⟨60105529520701517798305585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320562824110408094924296453 60105529520701517798305585)
            ·
              refine ⟨45079147140526138348729189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60105529520701517798305585 45079147140526138348729189)
              ·
                refine ⟨8452340088848650940386723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45079147140526138348729189 8452340088848650940386723)
                ·
                  refine ⟨12678510133272976410580085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8452340088848650940386723 12678510133272976410580085)
                  ·
                    refine ⟨1188610324994341538491883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12678510133272976410580085 1188610324994341538491883)
                    ·
                      rfl

theorem cell23_6944431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 1, 5].length) (baseStart_6944431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944431 prefixEnd_6944431 := by exact prefixLift 6944431
  have htrace : WordTrace (prefixWord ++ tailWord_6944431) baseStart_6944431 baseEnd_6944431 := by
    simpa [prefixWord, tailWord_6944431, baseEnd_6944431] using wordTrace_append hprefix tailTrace_6944431
  have hstable : (prefixWord ++ tailWord_6944431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944431).length < 2 ^ (prefixWord ++ tailWord_6944431).sum := by decide
  have hdescent : baseEnd_6944431 < baseStart_6944431 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944451 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 3, 8, 2]
def baseStart_6944451 : Nat := 118140960795 + 6944451 * 2 ^ 59
def prefixEnd_6944451 : Nat := 4983230072969 + 3 ^ 40 * 6944451 * 2
def baseEnd_6944451 : Nat := 3565841244596114537225557

theorem tailTrace_6944451 : CollatzResearch.WordTrace tailWord_6944451 prefixEnd_6944451 3565841244596114537225557 := by
  unfold tailWord_6944451
  simp only [CollatzResearch.WordTrace]
  refine ⟨253284936164447519652209207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168856624109631679768139471 253284936164447519652209207)
  ·
    refine ⟨379927404246671279478313811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253284936164447519652209207 379927404246671279478313811)
    ·
      refine ⟨569891106370006919217470717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379927404246671279478313811 569891106370006919217470717)
      ·
        refine ⟨213709164888752594706551519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 569891106370006919217470717 213709164888752594706551519)
        ·
          refine ⟨320563747333128892059827279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213709164888752594706551519 320563747333128892059827279)
          ·
            refine ⟨480845620999693338089740919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320563747333128892059827279 480845620999693338089740919)
            ·
              refine ⟨721268431499540007134611379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480845620999693338089740919 721268431499540007134611379)
              ·
                refine ⟨1081902647249310010701917069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721268431499540007134611379 1081902647249310010701917069)
                ·
                  refine ⟨405713492718491254013218901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1081902647249310010701917069 405713492718491254013218901)
                  ·
                    refine ⟨4754454992794819382967409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 405713492718491254013218901 4754454992794819382967409)
                    ·
                      refine ⟨3565841244596114537225557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754454992794819382967409 3565841244596114537225557)
                      ·
                        rfl

theorem cell23_6944451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_6944451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944451 prefixEnd_6944451 := by exact prefixLift 6944451
  have htrace : WordTrace (prefixWord ++ tailWord_6944451) baseStart_6944451 baseEnd_6944451 := by
    simpa [prefixWord, tailWord_6944451, baseEnd_6944451] using wordTrace_append hprefix tailTrace_6944451
  have hstable : (prefixWord ++ tailWord_6944451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944451).length < 2 ^ (prefixWord ++ tailWord_6944451).sum := by decide
  have hdescent : baseEnd_6944451 < baseStart_6944451 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944471 : List Nat := [1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_6944471 : Nat := 118140960795 + 6944471 * 2 ^ 59
def prefixEnd_6944471 : Nat := 4983230072969 + 3 ^ 40 * 6944471 * 2
def baseEnd_6944471 : Nat := 3565851514209204458975465

theorem tailTrace_6944471 : CollatzResearch.WordTrace tailWord_6944471 prefixEnd_6944471 3565851514209204458975465 := by
  unfold tailWord_6944471
  simp only [CollatzResearch.WordTrace]
  refine ⟨253285665624375063067937267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168857110416250042045291511 253285665624375063067937267)
  ·
    refine ⟨379928498436562594601905901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253285665624375063067937267 379928498436562594601905901)
    ·
      refine ⟨142473186913710972975714713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379928498436562594601905901 142473186913710972975714713)
      ·
        refine ⟨106854890185283229731786035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142473186913710972975714713 106854890185283229731786035)
        ·
          refine ⟨160282335277924844597679053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106854890185283229731786035 160282335277924844597679053)
          ·
            refine ⟨60105875729221816724129645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160282335277924844597679053 60105875729221816724129645)
            ·
              refine ⟨22539703398458181271548617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60105875729221816724129645 22539703398458181271548617)
              ·
                refine ⟨16904777548843635953661463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22539703398458181271548617 16904777548843635953661463)
                ·
                  refine ⟨25357166323265453930492195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16904777548843635953661463 25357166323265453930492195)
                  ·
                    refine ⟨38035749484898180895738293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25357166323265453930492195 38035749484898180895738293)
                    ·
                      refine ⟨3565851514209204458975465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38035749484898180895738293 3565851514209204458975465)
                      ·
                        rfl

theorem cell23_6944471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_6944471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944471 prefixEnd_6944471 := by exact prefixLift 6944471
  have htrace : WordTrace (prefixWord ++ tailWord_6944471) baseStart_6944471 baseEnd_6944471 := by
    simpa [prefixWord, tailWord_6944471, baseEnd_6944471] using wordTrace_append hprefix tailTrace_6944471
  have hstable : (prefixWord ++ tailWord_6944471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944471).length < 2 ^ (prefixWord ++ tailWord_6944471).sum := by decide
  have hdescent : baseEnd_6944471 < baseStart_6944471 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944485 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6944485 : Nat := 118140960795 + 6944485 * 2 ^ 59
def prefixEnd_6944485 : Nat := 4983230072969 + 3 ^ 40 * 6944485 * 2
def baseEnd_6944485 : Nat := 3565858702938367404200401

theorem tailTrace_6944485 : CollatzResearch.WordTrace tailWord_6944485 prefixEnd_6944485 3565858702938367404200401 := by
  unfold tailWord_6944485
  simp only [CollatzResearch.WordTrace]
  refine ⟨253286176246324343458946909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168857450830882895639297939 253286176246324343458946909)
  ·
    refine ⟨94982316092371628797105091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253286176246324343458946909 94982316092371628797105091)
    ·
      refine ⟨142473474138557443195657637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94982316092371628797105091 142473474138557443195657637)
      ·
        refine ⟨26713776400979520599185807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142473474138557443195657637 26713776400979520599185807)
        ·
          refine ⟨40070664601469280898778711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26713776400979520599185807 40070664601469280898778711)
          ·
            refine ⟨60105996902203921348168067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40070664601469280898778711 60105996902203921348168067)
            ·
              refine ⟨90158995353305882022252101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60105996902203921348168067 90158995353305882022252101)
              ·
                refine ⟨16904811628744852879172269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90158995353305882022252101 16904811628744852879172269)
                ·
                  refine ⟨6339304360779319829689601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16904811628744852879172269 6339304360779319829689601)
                  ·
                    refine ⟨4754478270584489872267201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6339304360779319829689601 4754478270584489872267201)
                    ·
                      refine ⟨3565858702938367404200401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754478270584489872267201 3565858702938367404200401)
                      ·
                        rfl

theorem cell23_6944485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6944485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944485 prefixEnd_6944485 := by exact prefixLift 6944485
  have htrace : WordTrace (prefixWord ++ tailWord_6944485) baseStart_6944485 baseEnd_6944485 := by
    simpa [prefixWord, tailWord_6944485, baseEnd_6944485] using wordTrace_append hprefix tailTrace_6944485
  have hstable : (prefixWord ++ tailWord_6944485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944485).length < 2 ^ (prefixWord ++ tailWord_6944485).sum := by decide
  have hdescent : baseEnd_6944485 < baseStart_6944485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944491 : List Nat := [1, 1, 1, 1, 2, 4, 6, 7]
def baseStart_6944491 : Nat := 118140960795 + 6944491 * 2 ^ 59
def prefixEnd_6944491 : Nat := 4983230072969 + 3 ^ 40 * 6944491 * 2
def baseEnd_6944491 : Nat := 132068954956381273360199

theorem tailTrace_6944491 : CollatzResearch.WordTrace tailWord_6944491 prefixEnd_6944491 132068954956381273360199 := by
  unfold tailWord_6944491
  simp only [CollatzResearch.WordTrace]
  refine ⟨253286395084302606483665327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168857596722868404322443551 253286395084302606483665327)
  ·
    refine ⟨379929592626453909725497991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253286395084302606483665327 379929592626453909725497991)
    ·
      refine ⟨569894388939680864588246987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379929592626453909725497991 569894388939680864588246987)
      ·
        refine ⟨854841583409521296882370481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569894388939680864588246987 854841583409521296882370481)
        ·
          refine ⟨641131187557140972661777861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854841583409521296882370481 641131187557140972661777861)
          ·
            refine ⟨120212097666963932374083349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 641131187557140972661777861 120212097666963932374083349)
            ·
              refine ⟨5634942078138934330035157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 120212097666963932374083349 5634942078138934330035157)
              ·
                refine ⟨132068954956381273360199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5634942078138934330035157 132068954956381273360199)
                ·
                  rfl

theorem cell23_6944491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 7].length) (baseStart_6944491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944491 prefixEnd_6944491 := by exact prefixLift 6944491
  have htrace : WordTrace (prefixWord ++ tailWord_6944491) baseStart_6944491 baseEnd_6944491 := by
    simpa [prefixWord, tailWord_6944491, baseEnd_6944491] using wordTrace_append hprefix tailTrace_6944491
  have hstable : (prefixWord ++ tailWord_6944491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944491).length < 2 ^ (prefixWord ++ tailWord_6944491).sum := by decide
  have hdescent : baseEnd_6944491 < baseStart_6944491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944519 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 3, 2, 2]
def baseStart_6944519 : Nat := 118140960795 + 6944519 * 2 ^ 59
def prefixEnd_6944519 : Nat := 4983230072969 + 3 ^ 40 * 6944519 * 2
def baseEnd_6944519 : Nat := 3565876161280620271175245

theorem tailTrace_6944519 : CollatzResearch.WordTrace tailWord_6944519 prefixEnd_6944519 3565876161280620271175245 := by
  unfold tailWord_6944519
  simp only [CollatzResearch.WordTrace]
  refine ⟨253287416328201167265684611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168858277552134111510456407 253287416328201167265684611)
  ·
    refine ⟨379931124492301750898526917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253287416328201167265684611 379931124492301750898526917)
    ·
      refine ⟨71237085842306578293473797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 379931124492301750898526917 71237085842306578293473797)
      ·
        refine ⟨13356953595432483430026337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71237085842306578293473797 13356953595432483430026337)
        ·
          refine ⟨10017715196574362572519753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13356953595432483430026337 10017715196574362572519753)
          ·
            refine ⟨7513286397430771929389815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10017715196574362572519753 7513286397430771929389815)
            ·
              refine ⟨11269929596146157894084723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7513286397430771929389815 11269929596146157894084723)
              ·
                refine ⟨16904894394219236841127085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11269929596146157894084723 16904894394219236841127085)
                ·
                  refine ⟨6339335397832213815422657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16904894394219236841127085 6339335397832213815422657)
                  ·
                    refine ⟨4754501548374160361566993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6339335397832213815422657 4754501548374160361566993)
                    ·
                      refine ⟨3565876161280620271175245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754501548374160361566993 3565876161280620271175245)
                      ·
                        rfl

theorem cell23_6944519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_6944519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944519 prefixEnd_6944519 := by exact prefixLift 6944519
  have htrace : WordTrace (prefixWord ++ tailWord_6944519) baseStart_6944519 baseEnd_6944519 := by
    simpa [prefixWord, tailWord_6944519, baseEnd_6944519] using wordTrace_append hprefix tailTrace_6944519
  have hstable : (prefixWord ++ tailWord_6944519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944519).length < 2 ^ (prefixWord ++ tailWord_6944519).sum := by decide
  have hdescent : baseEnd_6944519 < baseStart_6944519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944545 : List Nat := [1, 2, 3, 2, 1, 4, 1, 1, 3, 3, 2]
def baseStart_6944545 : Nat := 118140960795 + 6944545 * 2 ^ 59
def prefixEnd_6944545 : Nat := 4983230072969 + 3 ^ 40 * 6944545 * 2
def baseEnd_6944545 : Nat := 3565889511777637169450125

theorem tailTrace_6944545 : CollatzResearch.WordTrace tailWord_6944545 prefixEnd_6944545 3565889511777637169450125 := by
  unfold tailWord_6944545
  simp only [CollatzResearch.WordTrace]
  refine ⟨253288364626106973706131089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168858909750737982470754059 253288364626106973706131089)
  ·
    refine ⟨189966273469580230279598317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253288364626106973706131089 189966273469580230279598317)
    ·
      refine ⟨71237352551092586354849369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189966273469580230279598317 71237352551092586354849369)
      ·
        refine ⟨53428014413319439766137027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71237352551092586354849369 53428014413319439766137027)
        ·
          refine ⟨80142021619979159649205541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53428014413319439766137027 80142021619979159649205541)
          ·
            refine ⟨15026629053746092434226039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80142021619979159649205541 15026629053746092434226039)
            ·
              refine ⟨22539943580619138651339059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15026629053746092434226039 22539943580619138651339059)
              ·
                refine ⟨33809915370928707977008589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22539943580619138651339059 33809915370928707977008589)
                ·
                  refine ⟨12678718264098265491378221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33809915370928707977008589 12678718264098265491378221)
                  ·
                    refine ⟨4754519349036849559266833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12678718264098265491378221 4754519349036849559266833)
                    ·
                      refine ⟨3565889511777637169450125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754519349036849559266833 3565889511777637169450125)
                      ·
                        rfl

theorem cell23_6944545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_6944545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944545 prefixEnd_6944545 := by exact prefixLift 6944545
  have htrace : WordTrace (prefixWord ++ tailWord_6944545) baseStart_6944545 baseEnd_6944545 := by
    simpa [prefixWord, tailWord_6944545, baseEnd_6944545] using wordTrace_append hprefix tailTrace_6944545
  have hstable : (prefixWord ++ tailWord_6944545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944545).length < 2 ^ (prefixWord ++ tailWord_6944545).sum := by decide
  have hdescent : baseEnd_6944545 < baseStart_6944545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944569 : List Nat := [1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6944569 : Nat := 118140960795 + 6944569 * 2 ^ 59
def prefixEnd_6944569 : Nat := 4983230072969 + 3 ^ 40 * 6944569 * 2
def baseEnd_6944569 : Nat := 3565901835313345075550015

theorem tailTrace_6944569 : CollatzResearch.WordTrace tailWord_6944569 prefixEnd_6944569 3565901835313345075550015 := by
  unfold tailWord_6944569
  simp only [CollatzResearch.WordTrace]
  refine ⟨253289239978020025805004761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168859493318680017203336507 253289239978020025805004761)
  ·
    refine ⟨189966929983515019353753571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253289239978020025805004761 189966929983515019353753571)
    ·
      refine ⟨284950394975272529030630357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189966929983515019353753571 284950394975272529030630357)
      ·
        refine ⟨6678524882232949899155399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 284950394975272529030630357 6678524882232949899155399)
        ·
          refine ⟨10017787323349424848733099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6678524882232949899155399 10017787323349424848733099)
          ·
            refine ⟨15026680985024137273099649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10017787323349424848733099 15026680985024137273099649)
            ·
              refine ⟨11270010738768102954824737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15026680985024137273099649 11270010738768102954824737)
              ·
                refine ⟨8452508054076077216118553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11270010738768102954824737 8452508054076077216118553)
                ·
                  refine ⟨6339381040557057912088915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8452508054076077216118553 6339381040557057912088915)
                  ·
                    refine ⟨9509071560835586868133373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6339381040557057912088915 9509071560835586868133373)
                    ·
                      refine ⟨3565901835313345075550015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509071560835586868133373 3565901835313345075550015)
                      ·
                        rfl

theorem cell23_6944569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6944569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944569 prefixEnd_6944569 := by exact prefixLift 6944569
  have htrace : WordTrace (prefixWord ++ tailWord_6944569) baseStart_6944569 baseEnd_6944569 := by
    simpa [prefixWord, tailWord_6944569, baseEnd_6944569] using wordTrace_append hprefix tailTrace_6944569
  have hstable : (prefixWord ++ tailWord_6944569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944569).length < 2 ^ (prefixWord ++ tailWord_6944569).sum := by decide
  have hdescent : baseEnd_6944569 < baseStart_6944569 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944581 : List Nat := [1, 3, 1, 1, 1, 2, 4, 3, 7]
def baseStart_6944581 : Nat := 118140960795 + 6944581 * 2 ^ 59
def prefixEnd_6944581 : Nat := 4983230072969 + 3 ^ 40 * 6944581 * 2
def baseEnd_6944581 : Nat := 396211999675688780955551

theorem tailTrace_6944581 : CollatzResearch.WordTrace tailWord_6944581 prefixEnd_6944581 396211999675688780955551 := by
  unfold tailWord_6944581
  simp only [CollatzResearch.WordTrace]
  refine ⟨253289677653976551854441597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168859785102651034569627731 253289677653976551854441597)
  ·
    refine ⟨94983629120241206945415599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253289677653976551854441597 94983629120241206945415599)
    ·
      refine ⟨142475443680361810418123399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94983629120241206945415599 142475443680361810418123399)
      ·
        refine ⟨213713165520542715627185099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142475443680361810418123399 213713165520542715627185099)
        ·
          refine ⟨320569748280814073440777649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213713165520542715627185099 320569748280814073440777649)
          ·
            refine ⟨240427311210610555080583237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320569748280814073440777649 240427311210610555080583237)
            ·
              refine ⟨45080120851989479077609357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240427311210610555080583237 45080120851989479077609357)
              ·
                refine ⟨16905045319496054654103509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45080120851989479077609357 16905045319496054654103509)
                ·
                  refine ⟨396211999675688780955551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16905045319496054654103509 396211999675688780955551)
                  ·
                    rfl

theorem cell23_6944581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_6944581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944581 prefixEnd_6944581 := by exact prefixLift 6944581
  have htrace : WordTrace (prefixWord ++ tailWord_6944581) baseStart_6944581 baseEnd_6944581 := by
    simpa [prefixWord, tailWord_6944581, baseEnd_6944581] using wordTrace_append hprefix tailTrace_6944581
  have hstable : (prefixWord ++ tailWord_6944581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944581).length < 2 ^ (prefixWord ++ tailWord_6944581).sum := by decide
  have hdescent : baseEnd_6944581 < baseStart_6944581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944615 : List Nat := [1, 1, 5, 1, 2, 1, 4, 3, 5]
def baseStart_6944615 : Nat := 118140960795 + 6944615 * 2 ^ 59
def prefixEnd_6944615 : Nat := 4983230072969 + 3 ^ 40 * 6944615 * 2
def baseEnd_6944615 : Nat := 396213939491494655063867

theorem tailTrace_6944615 : CollatzResearch.WordTrace tailWord_6944615 prefixEnd_6944615 396213939491494655063867 := by
  unfold tailWord_6944615
  simp only [CollatzResearch.WordTrace]
  refine ⟨253290917735853375661179299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168860611823902250440786199 253290917735853375661179299)
  ·
    refine ⟨379936376603780063491768949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253290917735853375661179299 379936376603780063491768949)
    ·
      refine ⟨35619035306604380952353339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 379936376603780063491768949 35619035306604380952353339)
      ·
        refine ⟨53428552959906571428530009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35619035306604380952353339 53428552959906571428530009)
        ·
          refine ⟨40071414719929928571397507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53428552959906571428530009 40071414719929928571397507)
          ·
            refine ⟨60107122079894892857096261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40071414719929928571397507 60107122079894892857096261)
            ·
              refine ⟨11270085389980292410705549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60107122079894892857096261 11270085389980292410705549)
              ·
                refine ⟨4226282021242609654014581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11270085389980292410705549 4226282021242609654014581)
                ·
                  refine ⟨396213939491494655063867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4226282021242609654014581 396213939491494655063867)
                  ·
                    rfl

theorem cell23_6944615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 3, 5].length) (baseStart_6944615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944615 prefixEnd_6944615 := by exact prefixLift 6944615
  have htrace : WordTrace (prefixWord ++ tailWord_6944615) baseStart_6944615 baseEnd_6944615 := by
    simpa [prefixWord, tailWord_6944615, baseEnd_6944615] using wordTrace_append hprefix tailTrace_6944615
  have hstable : (prefixWord ++ tailWord_6944615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944615).length < 2 ^ (prefixWord ++ tailWord_6944615).sum := by decide
  have hdescent : baseEnd_6944615 < baseStart_6944615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944698 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3]
def baseStart_6944698 : Nat := 118140960795 + 6944698 * 2 ^ 59
def prefixEnd_6944698 : Nat := 4983230072969 + 3 ^ 40 * 6944698 * 2
def baseEnd_6944698 : Nat := 3565968074317775070836921

theorem tailTrace_6944698 : CollatzResearch.WordTrace tailWord_6944698 prefixEnd_6944698 3565968074317775070836921 := by
  unfold tailWord_6944698
  simp only [CollatzResearch.WordTrace]
  refine ⟨63323486248638170209112687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168862629996368453890967165 63323486248638170209112687)
  ·
    refine ⟨94985229372957255313669031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63323486248638170209112687 94985229372957255313669031)
    ·
      refine ⟨142477844059435882970503547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94985229372957255313669031 142477844059435882970503547)
      ·
        refine ⟨213716766089153824455755321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142477844059435882970503547 213716766089153824455755321)
        ·
          refine ⟨160287574566865368341816491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213716766089153824455755321 160287574566865368341816491)
          ·
            refine ⟨240431361850298052512724737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160287574566865368341816491 240431361850298052512724737)
            ·
              refine ⟨180323521387723539384543553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240431361850298052512724737 180323521387723539384543553)
              ·
                refine ⟨135242641040792654538407665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180323521387723539384543553 135242641040792654538407665)
                ·
                  refine ⟨101431980780594490903805749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135242641040792654538407665 101431980780594490903805749)
                  ·
                    refine ⟨9509248198180733522231789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101431980780594490903805749 9509248198180733522231789)
                    ·
                      refine ⟨3565968074317775070836921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509248198180733522231789 3565968074317775070836921)
                      ·
                        rfl

theorem cell23_6944698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3].length) (baseStart_6944698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944698 prefixEnd_6944698 := by exact prefixLift 6944698
  have htrace : WordTrace (prefixWord ++ tailWord_6944698) baseStart_6944698 baseEnd_6944698 := by
    simpa [prefixWord, tailWord_6944698, baseEnd_6944698] using wordTrace_append hprefix tailTrace_6944698
  have hstable : (prefixWord ++ tailWord_6944698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944698).length < 2 ^ (prefixWord ++ tailWord_6944698).sum := by decide
  have hdescent : baseEnd_6944698 < baseStart_6944698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944715 : List Nat := [1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 3]
def baseStart_6944715 : Nat := 118140960795 + 6944715 * 2 ^ 59
def prefixEnd_6944715 : Nat := 4983230072969 + 3 ^ 40 * 6944715 * 2
def baseEnd_6944715 : Nat := 3565976803488901504324343

theorem tailTrace_6944715 : CollatzResearch.WordTrace tailWord_6944715 prefixEnd_6944715 3565976803488901504324343 := by
  unfold tailWord_6944715
  simp only [CollatzResearch.WordTrace]
  refine ⟨253294565035491092739819599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168863043356994061826546399 253294565035491092739819599)
  ·
    refine ⟨379941847553236639109729399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253294565035491092739819599 379941847553236639109729399)
    ·
      refine ⟨569912771329854958664594099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379941847553236639109729399 569912771329854958664594099)
      ·
        refine ⟨854869156994782437996891149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569912771329854958664594099 854869156994782437996891149)
        ·
          refine ⟨320575933873043414248834181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 854869156994782437996891149 320575933873043414248834181)
          ·
            refine ⟨60107987601195640171656409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320575933873043414248834181 60107987601195640171656409)
            ·
              refine ⟨45080990700896730128742307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60107987601195640171656409 45080990700896730128742307)
              ·
                refine ⟨67621486051345095193113461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45080990700896730128742307 67621486051345095193113461)
                ·
                  refine ⟨6339514317313602674354387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67621486051345095193113461 6339514317313602674354387)
                  ·
                    refine ⟨9509271475970404011531581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6339514317313602674354387 9509271475970404011531581)
                    ·
                      refine ⟨3565976803488901504324343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509271475970404011531581 3565976803488901504324343)
                      ·
                        rfl

theorem cell23_6944715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 1, 5, 1, 3].length) (baseStart_6944715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944715 prefixEnd_6944715 := by exact prefixLift 6944715
  have htrace : WordTrace (prefixWord ++ tailWord_6944715) baseStart_6944715 baseEnd_6944715 := by
    simpa [prefixWord, tailWord_6944715, baseEnd_6944715] using wordTrace_append hprefix tailTrace_6944715
  have hstable : (prefixWord ++ tailWord_6944715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944715).length < 2 ^ (prefixWord ++ tailWord_6944715).sum := by decide
  have hdescent : baseEnd_6944715 < baseStart_6944715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944743 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 1, 4]
def baseStart_6944743 : Nat := 118140960795 + 6944743 * 2 ^ 59
def prefixEnd_6944743 : Nat := 4983230072969 + 3 ^ 40 * 6944743 * 2
def baseEnd_6944743 : Nat := 1188663726982409131591405

theorem tailTrace_6944743 : CollatzResearch.WordTrace tailWord_6944743 prefixEnd_6944743 1188663726982409131591405 := by
  unfold tailWord_6944743
  simp only [CollatzResearch.WordTrace]
  refine ⟨253295586279389653521838883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168863724186259769014559255 253295586279389653521838883)
  ·
    refine ⟨379943379419084480282758325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253295586279389653521838883 379943379419084480282758325)
    ·
      refine ⟨35619691820539170026508593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 379943379419084480282758325 35619691820539170026508593)
      ·
        refine ⟨26714768865404377519881445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35619691820539170026508593 26714768865404377519881445)
        ·
          refine ⟨5009019162263320784977771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26714768865404377519881445 5009019162263320784977771)
          ·
            refine ⟨7513528743394981177466657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009019162263320784977771 7513528743394981177466657)
            ·
              refine ⟨5635146557546235883099993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7513528743394981177466657 5635146557546235883099993)
              ·
                refine ⟨4226359918159676912324995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5635146557546235883099993 4226359918159676912324995)
                ·
                  refine ⟨6339539877239515368487493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4226359918159676912324995 6339539877239515368487493)
                  ·
                    refine ⟨1188663726982409131591405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6339539877239515368487493 1188663726982409131591405)
                    ·
                      rfl

theorem cell23_6944743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_6944743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944743 prefixEnd_6944743 := by exact prefixLift 6944743
  have htrace : WordTrace (prefixWord ++ tailWord_6944743) baseStart_6944743 baseEnd_6944743 := by
    simpa [prefixWord, tailWord_6944743, baseEnd_6944743] using wordTrace_append hprefix tailTrace_6944743
  have hstable : (prefixWord ++ tailWord_6944743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944743).length < 2 ^ (prefixWord ++ tailWord_6944743).sum := by decide
  have hdescent : baseEnd_6944743 < baseStart_6944743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944792 : List Nat := [2, 1, 2, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_6944792 : Nat := 118140960795 + 6944792 * 2 ^ 59
def prefixEnd_6944792 : Nat := 4983230072969 + 3 ^ 40 * 6944792 * 2
def baseEnd_6944792 : Nat := 3566016341499297703061489

theorem tailTrace_6944792 : CollatzResearch.WordTrace tailWord_6944792 prefixEnd_6944792 3566016341499297703061489 := by
  unfold tailWord_6944792
  simp only [CollatzResearch.WordTrace]
  refine ⟨126648686728106067445186315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168864915637474756593581753 126648686728106067445186315)
  ·
    refine ⟨189973030092159101167779473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126648686728106067445186315 189973030092159101167779473)
    ·
      refine ⟨142479772569119325875834605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189973030092159101167779473 142479772569119325875834605)
      ·
        refine ⟨53429914713419747203437977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142479772569119325875834605 53429914713419747203437977)
        ·
          refine ⟨40072436035064810402578483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53429914713419747203437977 40072436035064810402578483)
          ·
            refine ⟨60108654052597215603867725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40072436035064810402578483 60108654052597215603867725)
            ·
              refine ⟨22540745269723955851450397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60108654052597215603867725 22540745269723955851450397)
              ·
                refine ⟨8452779476146483444293899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22540745269723955851450397 8452779476146483444293899)
                ·
                  refine ⟨12679169214219725166440849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8452779476146483444293899 12679169214219725166440849)
                  ·
                    refine ⟨9509376910664793874830637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12679169214219725166440849 9509376910664793874830637)
                    ·
                      refine ⟨3566016341499297703061489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509376910664793874830637 3566016341499297703061489)
                      ·
                        rfl

theorem cell23_6944792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_6944792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944792 prefixEnd_6944792 := by exact prefixLift 6944792
  have htrace : WordTrace (prefixWord ++ tailWord_6944792) baseStart_6944792 baseEnd_6944792 := by
    simpa [prefixWord, tailWord_6944792, baseEnd_6944792] using wordTrace_append hprefix tailTrace_6944792
  have hstable : (prefixWord ++ tailWord_6944792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944792).length < 2 ^ (prefixWord ++ tailWord_6944792).sum := by decide
  have hdescent : baseEnd_6944792 < baseStart_6944792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944815 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 2, 7, 2]
def baseStart_6944815 : Nat := 118140960795 + 6944815 * 2 ^ 59
def prefixEnd_6944815 : Nat := 4983230072969 + 3 ^ 40 * 6944815 * 2
def baseEnd_6944815 : Nat := 3566028151554351113073883

theorem tailTrace_6944815 : CollatzResearch.WordTrace tailWord_6944815 prefixEnd_6944815 3566028151554351113073883 := by
  unfold tailWord_6944815
  simp only [CollatzResearch.WordTrace]
  refine ⟨253298212335128809818459899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168865474890085873212306599 253298212335128809818459899)
  ·
    refine ⟨379947318502693214727689849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253298212335128809818459899 379947318502693214727689849)
    ·
      refine ⟨284960488877019911045767387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379947318502693214727689849 284960488877019911045767387)
      ·
        refine ⟨427440733315529866568651081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284960488877019911045767387 427440733315529866568651081)
        ·
          refine ⟨320580549986647399926488311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427440733315529866568651081 320580549986647399926488311)
          ·
            refine ⟨480870824979971099889732467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320580549986647399926488311 480870824979971099889732467)
            ·
              refine ⟨721306237469956649834598701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480870824979971099889732467 721306237469956649834598701)
              ·
                refine ⟨270489839051233743687974513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721306237469956649834598701 270489839051233743687974513)
                ·
                  refine ⟨202867379288425307765980885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270489839051233743687974513 202867379288425307765980885)
                  ·
                    refine ⟨4754704202072468150765177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 202867379288425307765980885 4754704202072468150765177)
                    ·
                      refine ⟨3566028151554351113073883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754704202072468150765177 3566028151554351113073883)
                      ·
                        rfl

theorem cell23_6944815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 2, 7, 2].length) (baseStart_6944815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944815 prefixEnd_6944815 := by exact prefixLift 6944815
  have htrace : WordTrace (prefixWord ++ tailWord_6944815) baseStart_6944815 baseEnd_6944815 := by
    simpa [prefixWord, tailWord_6944815, baseEnd_6944815] using wordTrace_append hprefix tailTrace_6944815
  have hstable : (prefixWord ++ tailWord_6944815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944815).length < 2 ^ (prefixWord ++ tailWord_6944815).sum := by decide
  have hdescent : baseEnd_6944815 < baseStart_6944815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944865 : List Nat := [1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 3]
def baseStart_6944865 : Nat := 118140960795 + 6944865 * 2 ^ 59
def prefixEnd_6944865 : Nat := 4983230072969 + 3 ^ 40 * 6944865 * 2
def baseEnd_6944865 : Nat := 3566053825587075917448653

theorem tailTrace_6944865 : CollatzResearch.WordTrace tailWord_6944865 prefixEnd_6944865 3566053825587075917448653 := by
  unfold tailWord_6944865
  simp only [CollatzResearch.WordTrace]
  refine ⟨253300035984947668357780049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168866690656631778905186699 253300035984947668357780049)
  ·
    refine ⟨189975026988710751268335037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253300035984947668357780049 189975026988710751268335037)
    ·
      refine ⟨71240635120766531725625639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 189975026988710751268335037 71240635120766531725625639)
      ·
        refine ⟨106860952681149797588438459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71240635120766531725625639 106860952681149797588438459)
        ·
          refine ⟨160291429021724696382657689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106860952681149797588438459 160291429021724696382657689)
          ·
            refine ⟨120218571766293522286993267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160291429021724696382657689 120218571766293522286993267)
            ·
              refine ⟨180327857649440283430489901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120218571766293522286993267 180327857649440283430489901)
              ·
                refine ⟨67622946618540106286433713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180327857649440283430489901 67622946618540106286433713)
                ·
                  refine ⟨50717209963905079714825285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67622946618540106286433713 50717209963905079714825285)
                  ·
                    refine ⟨9509476868232202446529741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50717209963905079714825285 9509476868232202446529741)
                    ·
                      refine ⟨3566053825587075917448653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509476868232202446529741 3566053825587075917448653)
                      ·
                        rfl

theorem cell23_6944865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_6944865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944865 prefixEnd_6944865 := by exact prefixLift 6944865
  have htrace : WordTrace (prefixWord ++ tailWord_6944865) baseStart_6944865 baseEnd_6944865 := by
    simpa [prefixWord, tailWord_6944865, baseEnd_6944865] using wordTrace_append hprefix tailTrace_6944865
  have hstable : (prefixWord ++ tailWord_6944865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944865).length < 2 ^ (prefixWord ++ tailWord_6944865).sum := by decide
  have hdescent : baseEnd_6944865 < baseStart_6944865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944919 : List Nat := [1, 1, 3, 3, 4, 1, 1, 4, 5]
def baseStart_6944919 : Nat := 118140960795 + 6944919 * 2 ^ 59
def prefixEnd_6944919 : Nat := 4983230072969 + 3 ^ 40 * 6944919 * 2
def baseEnd_6944919 : Nat := 396231283726935411797045

theorem tailTrace_6944919 : CollatzResearch.WordTrace tailWord_6944919 prefixEnd_6944919 396231283726935411797045 := by
  unfold tailWord_6944919
  simp only [CollatzResearch.WordTrace]
  refine ⟨253302005526752035580245811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168868003684501357053497207 253302005526752035580245811)
  ·
    refine ⟨379953008290128053370368717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253302005526752035580245811 379953008290128053370368717)
    ·
      refine ⟨142482378108798020013888269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379953008290128053370368717 142482378108798020013888269)
      ·
        refine ⟨53430891790799257505208101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142482378108798020013888269 53430891790799257505208101)
        ·
          refine ⟨10018292210774860782226519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53430891790799257505208101 10018292210774860782226519)
          ·
            refine ⟨15027438316162291173339779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018292210774860782226519 15027438316162291173339779)
            ·
              refine ⟨22541157474243436760009669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15027438316162291173339779 22541157474243436760009669)
              ·
                refine ⟨4226467026420644392501813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22541157474243436760009669 4226467026420644392501813)
                ·
                  refine ⟨396231283726935411797045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4226467026420644392501813 396231283726935411797045)
                  ·
                    rfl

theorem cell23_6944919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 5].length) (baseStart_6944919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944919 prefixEnd_6944919 := by exact prefixLift 6944919
  have htrace : WordTrace (prefixWord ++ tailWord_6944919) baseStart_6944919 baseEnd_6944919 := by
    simpa [prefixWord, tailWord_6944919, baseEnd_6944919] using wordTrace_append hprefix tailTrace_6944919
  have hstable : (prefixWord ++ tailWord_6944919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944919).length < 2 ^ (prefixWord ++ tailWord_6944919).sum := by decide
  have hdescent : baseEnd_6944919 < baseStart_6944919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944949 : List Nat := [1, 3, 3, 4, 1, 1, 1, 1, 1, 7]
def baseStart_6944949 : Nat := 118140960795 + 6944949 * 2 ^ 59
def prefixEnd_6944949 : Nat := 4983230072969 + 3 ^ 40 * 6944949 * 2
def baseEnd_6944949 : Nat := 1188698985987351196266089

theorem tailTrace_6944949 : CollatzResearch.WordTrace tailWord_6944949 prefixEnd_6944949 1188698985987351196266089 := by
  unfold tailWord_6944949
  simp only [CollatzResearch.WordTrace]
  refine ⟨253303099716643350703837901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168868733144428900469225267 253303099716643350703837901)
  ·
    refine ⟨94988662393741256513939213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253303099716643350703837901 94988662393741256513939213)
    ·
      refine ⟨35620748397652971192727205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94988662393741256513939213 35620748397652971192727205)
      ·
        refine ⟨6678890324559932098636351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35620748397652971192727205 6678890324559932098636351)
        ·
          refine ⟨10018335486839898147954527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6678890324559932098636351 10018335486839898147954527)
          ·
            refine ⟨15027503230259847221931791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10018335486839898147954527 15027503230259847221931791)
            ·
              refine ⟨22541254845389770832897687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15027503230259847221931791 22541254845389770832897687)
              ·
                refine ⟨33811882268084656249346531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22541254845389770832897687 33811882268084656249346531)
                ·
                  refine ⟨50717823402126984374019797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33811882268084656249346531 50717823402126984374019797)
                  ·
                    refine ⟨1188698985987351196266089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50717823402126984374019797 1188698985987351196266089)
                    ·
                      rfl

theorem cell23_6944949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_6944949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944949 prefixEnd_6944949 := by exact prefixLift 6944949
  have htrace : WordTrace (prefixWord ++ tailWord_6944949) baseStart_6944949 baseEnd_6944949 := by
    simpa [prefixWord, tailWord_6944949, baseEnd_6944949] using wordTrace_append hprefix tailTrace_6944949
  have hstable : (prefixWord ++ tailWord_6944949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944949).length < 2 ^ (prefixWord ++ tailWord_6944949).sum := by decide
  have hdescent : baseEnd_6944949 < baseStart_6944949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944952 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 1, 6, 2]
def baseStart_6944952 : Nat := 118140960795 + 6944952 * 2 ^ 59
def prefixEnd_6944952 : Nat := 4983230072969 + 3 ^ 40 * 6944952 * 2
def baseEnd_6944952 : Nat := 3566098498404017077060753

theorem tailTrace_6944952 : CollatzResearch.WordTrace tailWord_6944952 prefixEnd_6944952 3566098498404017077060753 := by
  unfold tailWord_6944952
  simp only [CollatzResearch.WordTrace]
  refine ⟨126651604567816241108098555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168868806090421654810798073 126651604567816241108098555)
  ·
    refine ⟨189977406851724361662147833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126651604567816241108098555 189977406851724361662147833)
    ·
      refine ⟨142483055138793271246610875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 189977406851724361662147833 142483055138793271246610875)
      ·
        refine ⟨213724582708189906869916313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142483055138793271246610875 213724582708189906869916313)
        ·
          refine ⟨160293437031142430152437235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213724582708189906869916313 160293437031142430152437235)
          ·
            refine ⟨240440155546713645228655853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160293437031142430152437235 240440155546713645228655853)
            ·
              refine ⟨90165058330017616960745945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240440155546713645228655853 90165058330017616960745945)
              ·
                refine ⟨67623793747513212720559459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90165058330017616960745945 67623793747513212720559459)
                ·
                  refine ⟨101435690621269819080839189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67623793747513212720559459 101435690621269819080839189)
                  ·
                    refine ⟨4754797997872022769414337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101435690621269819080839189 4754797997872022769414337)
                    ·
                      refine ⟨3566098498404017077060753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4754797997872022769414337 3566098498404017077060753)
                      ·
                        rfl

theorem cell23_6944952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_6944952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944952 prefixEnd_6944952 := by exact prefixLift 6944952
  have htrace : WordTrace (prefixWord ++ tailWord_6944952) baseStart_6944952 baseEnd_6944952 := by
    simpa [prefixWord, tailWord_6944952, baseEnd_6944952] using wordTrace_append hprefix tailTrace_6944952
  have hstable : (prefixWord ++ tailWord_6944952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944952).length < 2 ^ (prefixWord ++ tailWord_6944952).sum := by decide
  have hdescent : baseEnd_6944952 < baseStart_6944952 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944965 : List Nat := [1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_6944965 : Nat := 118140960795 + 6944965 * 2 ^ 59
def prefixEnd_6944965 : Nat := 4983230072969 + 3 ^ 40 * 6944965 * 2
def baseEnd_6944965 : Nat := 3566105173652525526198193

theorem tailTrace_6944965 : CollatzResearch.WordTrace tailWord_6944965 prefixEnd_6944965 3566105173652525526198193 := by
  unfold tailWord_6944965
  simp only [CollatzResearch.WordTrace]
  refine ⟨253303683284585385436420349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168869122189723590290946899 253303683284585385436420349)
  ·
    refine ⟨94988881231719519538657631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253303683284585385436420349 94988881231719519538657631)
    ·
      refine ⟨142483321847579279307986447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94988881231719519538657631 142483321847579279307986447)
      ·
        refine ⟨213724982771368918961979671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142483321847579279307986447 213724982771368918961979671)
        ·
          refine ⟨320587474157053378442969507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213724982771368918961979671 320587474157053378442969507)
          ·
            refine ⟨480881211235580067664454261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320587474157053378442969507 480881211235580067664454261)
            ·
              refine ⟨45082613553335631343542587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 480881211235580067664454261 45082613553335631343542587)
              ·
                refine ⟨67623920330003447015313881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45082613553335631343542587 67623920330003447015313881)
                ·
                  refine ⟨50717940247502585261485411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67623920330003447015313881 50717940247502585261485411)
                  ·
                    refine ⟨76076910371253877892228117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50717940247502585261485411 76076910371253877892228117)
                    ·
                      refine ⟨3566105173652525526198193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76076910371253877892228117 3566105173652525526198193)
                      ·
                        rfl

theorem cell23_6944965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_6944965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944965 prefixEnd_6944965 := by exact prefixLift 6944965
  have htrace : WordTrace (prefixWord ++ tailWord_6944965) baseStart_6944965 baseEnd_6944965 := by
    simpa [prefixWord, tailWord_6944965, baseEnd_6944965] using wordTrace_append hprefix tailTrace_6944965
  have hstable : (prefixWord ++ tailWord_6944965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944965).length < 2 ^ (prefixWord ++ tailWord_6944965).sum := by decide
  have hdescent : baseEnd_6944965 < baseStart_6944965 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944975 : List Nat := [1, 1, 2, 1, 1, 3, 5, 1, 8]
def baseStart_6944975 : Nat := 118140960795 + 6944975 * 2 ^ 59
def prefixEnd_6944975 : Nat := 4983230072969 + 3 ^ 40 * 6944975 * 2
def baseEnd_6944975 : Nat := 396234478717674498563683

theorem tailTrace_6944975 : CollatzResearch.WordTrace tailWord_6944975 prefixEnd_6944975 396234478717674498563683 := by
  unfold tailWord_6944975
  simp only [CollatzResearch.WordTrace]
  refine ⟨253304048014549157144284379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168869365343032771429522919 253304048014549157144284379)
  ·
    refine ⟨379956072021823735716426569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253304048014549157144284379 379956072021823735716426569)
    ·
      refine ⟨284967054016367801787319927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379956072021823735716426569 284967054016367801787319927)
      ·
        refine ⟨427450581024551702680979891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284967054016367801787319927 427450581024551702680979891)
        ·
          refine ⟨641175871536827554021469837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427450581024551702680979891 641175871536827554021469837)
          ·
            refine ⟨240440951826310332758051189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641175871536827554021469837 240440951826310332758051189)
            ·
              refine ⟨22541339233716593696067299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 240440951826310332758051189 22541339233716593696067299)
              ·
                refine ⟨33812008850574890544100949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22541339233716593696067299 33812008850574890544100949)
                ·
                  refine ⟨396234478717674498563683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33812008850574890544100949 396234478717674498563683)
                  ·
                    rfl

theorem cell23_6944975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 8].length) (baseStart_6944975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944975 prefixEnd_6944975 := by exact prefixLift 6944975
  have htrace : WordTrace (prefixWord ++ tailWord_6944975) baseStart_6944975 baseEnd_6944975 := by
    simpa [prefixWord, tailWord_6944975, baseEnd_6944975] using wordTrace_append hprefix tailTrace_6944975
  have hstable : (prefixWord ++ tailWord_6944975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944975).length < 2 ^ (prefixWord ++ tailWord_6944975).sum := by decide
  have hdescent : baseEnd_6944975 < baseStart_6944975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6944989 : List Nat := [1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6944989 : Nat := 118140960795 + 6944989 * 2 ^ 59
def prefixEnd_6944989 : Nat := 4983230072969 + 3 ^ 40 * 6944989 * 2
def baseEnd_6944989 : Nat := 3566117497188233432298083

theorem tailTrace_6944989 : CollatzResearch.WordTrace tailWord_6944989 prefixEnd_6944989 3566117497188233432298083 := by
  unfold tailWord_6944989
  simp only [CollatzResearch.WordTrace]
  refine ⟨253304558636498437535294021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168869705757665625023529347 253304558636498437535294021)
  ·
    refine ⟨47494604744343457037867629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253304558636498437535294021 47494604744343457037867629)
    ·
      refine ⟨17810476779128796389200361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47494604744343457037867629 17810476779128796389200361)
      ·
        refine ⟨13357857584346597291900271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17810476779128796389200361 13357857584346597291900271)
        ·
          refine ⟨20036786376519895937850407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13357857584346597291900271 20036786376519895937850407)
          ·
            refine ⟨30055179564779843906775611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20036786376519895937850407 30055179564779843906775611)
            ·
              refine ⟨45082769347169765860163417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30055179564779843906775611 45082769347169765860163417)
              ·
                refine ⟨33812077010377324395122563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45082769347169765860163417 33812077010377324395122563)
                ·
                  refine ⟨50718115515565986592683845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33812077010377324395122563 50718115515565986592683845)
                  ·
                    refine ⟨9509646659168622486128221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50718115515565986592683845 9509646659168622486128221)
                    ·
                      refine ⟨3566117497188233432298083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509646659168622486128221 3566117497188233432298083)
                      ·
                        rfl

theorem cell23_6944989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6944989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6944989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6944989 prefixEnd_6944989 := by exact prefixLift 6944989
  have htrace : WordTrace (prefixWord ++ tailWord_6944989) baseStart_6944989 baseEnd_6944989 := by
    simpa [prefixWord, tailWord_6944989, baseEnd_6944989] using wordTrace_append hprefix tailTrace_6944989
  have hstable : (prefixWord ++ tailWord_6944989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6944989).length < 2 ^ (prefixWord ++ tailWord_6944989).sum := by decide
  have hdescent : baseEnd_6944989 < baseStart_6944989 := by decide
  rcases family_descends (prefixWord ++ tailWord_6944989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945002 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_6945002 : Nat := 118140960795 + 6945002 * 2 ^ 59
def prefixEnd_6945002 : Nat := 4983230072969 + 3 ^ 40 * 6945002 * 2
def baseEnd_6945002 : Nat := 3566124172436741881435523

theorem tailTrace_6945002 : CollatzResearch.WordTrace tailWord_6945002 prefixEnd_6945002 3566124172436741881435523 := by
  unfold tailWord_6945002
  simp only [CollatzResearch.WordTrace]
  refine ⟨63326258196362835188879315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168870021856967560503678173 63326258196362835188879315)
  ·
    refine ⟨94989387294544252783318973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63326258196362835188879315 94989387294544252783318973)
    ·
      refine ⟨35621020235454094793744615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94989387294544252783318973 35621020235454094793744615)
      ·
        refine ⟨53431530353181142190616923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35621020235454094793744615 53431530353181142190616923)
        ·
          refine ⟨80147295529771713285925385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53431530353181142190616923 80147295529771713285925385)
          ·
            refine ⟨60110471647328784964444039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80147295529771713285925385 60110471647328784964444039)
            ·
              refine ⟨90165707470993177446666059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60110471647328784964444039 90165707470993177446666059)
              ·
                refine ⟨135248561206489766169999089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90165707470993177446666059 135248561206489766169999089)
                ·
                  refine ⟨101436420904867324627499317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135248561206489766169999089 101436420904867324627499317)
                  ·
                    refine ⟨9509664459831311683828061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101436420904867324627499317 9509664459831311683828061)
                    ·
                      refine ⟨3566124172436741881435523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509664459831311683828061 3566124172436741881435523)
                      ·
                        rfl

theorem cell23_6945002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_6945002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945002 prefixEnd_6945002 := by exact prefixLift 6945002
  have htrace : WordTrace (prefixWord ++ tailWord_6945002) baseStart_6945002 baseEnd_6945002 := by
    simpa [prefixWord, tailWord_6945002, baseEnd_6945002] using wordTrace_append hprefix tailTrace_6945002
  have hstable : (prefixWord ++ tailWord_6945002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945002).length < 2 ^ (prefixWord ++ tailWord_6945002).sum := by decide
  have hdescent : baseEnd_6945002 < baseStart_6945002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945015 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 5]
def baseStart_6945015 : Nat := 118140960795 + 6945015 * 2 ^ 59
def prefixEnd_6945015 : Nat := 4983230072969 + 3 ^ 40 * 6945015 * 2
def baseEnd_6945015 : Nat := 3566130847685250330572963

theorem tailTrace_6945015 : CollatzResearch.WordTrace tailWord_6945015 prefixEnd_6945015 3566130847685250330572963 := by
  unfold tailWord_6945015
  simp only [CollatzResearch.WordTrace]
  refine ⟨253305506934404243975740499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168870337956269495983826999 253305506934404243975740499)
  ·
    refine ⟨379958260401606365963610749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253305506934404243975740499 379958260401606365963610749)
    ·
      refine ⟨142484347650602387236354031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379958260401606365963610749 142484347650602387236354031)
      ·
        refine ⟨213726521475903580854531047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142484347650602387236354031 213726521475903580854531047)
        ·
          refine ⟨320589782213855371281796571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213726521475903580854531047 320589782213855371281796571)
          ·
            refine ⟨480884673320783056922694857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320589782213855371281796571 480884673320783056922694857)
            ·
              refine ⟨360663504990587292692021143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480884673320783056922694857 360663504990587292692021143)
              ·
                refine ⟨540995257485880939038031715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360663504990587292692021143 540995257485880939038031715)
                ·
                  refine ⟨811492886228821408557047573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 540995257485880939038031715 811492886228821408557047573)
                  ·
                    refine ⟨38038729041976003526111605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 811492886228821408557047573 38038729041976003526111605)
                    ·
                      refine ⟨3566130847685250330572963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38038729041976003526111605 3566130847685250330572963)
                      ·
                        rfl

theorem cell23_6945015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 5].length) (baseStart_6945015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945015 prefixEnd_6945015 := by exact prefixLift 6945015
  have htrace : WordTrace (prefixWord ++ tailWord_6945015) baseStart_6945015 baseEnd_6945015 := by
    simpa [prefixWord, tailWord_6945015, baseEnd_6945015] using wordTrace_append hprefix tailTrace_6945015
  have hstable : (prefixWord ++ tailWord_6945015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945015).length < 2 ^ (prefixWord ++ tailWord_6945015).sum := by decide
  have hdescent : baseEnd_6945015 < baseStart_6945015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945052 : List Nat := [2, 2, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_6945052 : Nat := 118140960795 + 6945052 * 2 ^ 59
def prefixEnd_6945052 : Nat := 4983230072969 + 3 ^ 40 * 6945052 * 2
def baseEnd_6945052 : Nat := 1188716615489822228603431

theorem tailTrace_6945052 : CollatzResearch.WordTrace tailWord_6945052 prefixEnd_6945052 1188716615489822228603431 := by
  unfold tailWord_6945052
  simp only [CollatzResearch.WordTrace]
  refine ⟨126653428217635099647418705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168871237623513466196558273 126653428217635099647418705)
  ·
    refine ⟨94990071163226324735564029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126653428217635099647418705 94990071163226324735564029)
    ·
      refine ⟨35621276686209871775836511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94990071163226324735564029 35621276686209871775836511)
      ·
        refine ⟨53431915029314807663754767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35621276686209871775836511 53431915029314807663754767)
        ·
          refine ⟨80147872543972211495632151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53431915029314807663754767 80147872543972211495632151)
          ·
            refine ⟨120221808815958317243448227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80147872543972211495632151 120221808815958317243448227)
            ·
              refine ⟨180332713223937475865172341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120221808815958317243448227 180332713223937475865172341)
              ·
                refine ⟨16906191864744138362359907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180332713223937475865172341 16906191864744138362359907)
                ·
                  refine ⟨25359287797116207543539861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16906191864744138362359907 25359287797116207543539861)
                  ·
                    refine ⟨1188716615489822228603431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25359287797116207543539861 1188716615489822228603431)
                    ·
                      rfl

theorem cell23_6945052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_6945052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945052 prefixEnd_6945052 := by exact prefixLift 6945052
  have htrace : WordTrace (prefixWord ++ tailWord_6945052) baseStart_6945052 baseEnd_6945052 := by
    simpa [prefixWord, tailWord_6945052, baseEnd_6945052] using wordTrace_append hprefix tailTrace_6945052
  have hstable : (prefixWord ++ tailWord_6945052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945052).length < 2 ^ (prefixWord ++ tailWord_6945052).sum := by decide
  have hdescent : baseEnd_6945052 < baseStart_6945052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945056 : List Nat := [2, 1, 1, 5, 2, 3, 1, 2, 1, 5]
def baseStart_6945056 : Nat := 118140960795 + 6945056 * 2 ^ 59
def prefixEnd_6945056 : Nat := 4983230072969 + 3 ^ 40 * 6945056 * 2
def baseEnd_6945056 : Nat := 1188717300130694890053425

theorem tailTrace_6945056 : CollatzResearch.WordTrace tailWord_6945056 prefixEnd_6945056 1188717300130694890053425 := by
  unfold tailWord_6945056
  simp only [CollatzResearch.WordTrace]
  refine ⟨126653501163627853988991511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168871334884837138651988681 126653501163627853988991511)
  ·
    refine ⟨189980251745441780983487267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126653501163627853988991511 189980251745441780983487267)
    ·
      refine ⟨284970377618162671475230901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189980251745441780983487267 284970377618162671475230901)
      ·
        refine ⟨26715972901702750450802897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 284970377618162671475230901 26715972901702750450802897)
        ·
          refine ⟨20036979676277062838102173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26715972901702750450802897 20036979676277062838102173)
          ·
            refine ⟨7513867378603898564288315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20036979676277062838102173 7513867378603898564288315)
            ·
              refine ⟨11270801067905847846432473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7513867378603898564288315 11270801067905847846432473)
              ·
                refine ⟨8453100800929385884824355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11270801067905847846432473 8453100800929385884824355)
                ·
                  refine ⟨12679651201394078827236533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453100800929385884824355 12679651201394078827236533)
                  ·
                    refine ⟨1188717300130694890053425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12679651201394078827236533 1188717300130694890053425)
                    ·
                      rfl

theorem cell23_6945056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_6945056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945056 prefixEnd_6945056 := by exact prefixLift 6945056
  have htrace : WordTrace (prefixWord ++ tailWord_6945056) baseStart_6945056 baseEnd_6945056 := by
    simpa [prefixWord, tailWord_6945056, baseEnd_6945056] using wordTrace_append hprefix tailTrace_6945056
  have hstable : (prefixWord ++ tailWord_6945056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945056).length < 2 ^ (prefixWord ++ tailWord_6945056).sum := by decide
  have hdescent : baseEnd_6945056 < baseStart_6945056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945079 : List Nat := [1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 3]
def baseStart_6945079 : Nat := 118140960795 + 6945079 * 2 ^ 59
def prefixEnd_6945079 : Nat := 4983230072969 + 3 ^ 40 * 6945079 * 2
def baseEnd_6945079 : Nat := 3566163710447138080172669

theorem tailTrace_6945079 : CollatzResearch.WordTrace tailWord_6945079 prefixEnd_6945079 3566163710447138080172669 := by
  unfold tailWord_6945079
  simp only [CollatzResearch.WordTrace]
  refine ⟨253307841206172382906070291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168871894137448255270713527 253307841206172382906070291)
  ·
    refine ⟨379961761809258574359105437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253307841206172382906070291 379961761809258574359105437)
    ·
      refine ⟨142485660678471965384664539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379961761809258574359105437 142485660678471965384664539)
      ·
        refine ⟨213728491017707948076996809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142485660678471965384664539 213728491017707948076996809)
        ·
          refine ⟨160296368263280961057747607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213728491017707948076996809 160296368263280961057747607)
          ·
            refine ⟨240444552394921441586621411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160296368263280961057747607 240444552394921441586621411)
            ·
              refine ⟨360666828592382162379932117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240444552394921441586621411 360666828592382162379932117)
              ·
                refine ⟨8453128795133956930779659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 360666828592382162379932117 8453128795133956930779659)
                ·
                  refine ⟨12679693192700935396169489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453128795133956930779659 12679693192700935396169489)
                  ·
                    refine ⟨9509769894525701547127117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12679693192700935396169489 9509769894525701547127117)
                    ·
                      refine ⟨3566163710447138080172669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509769894525701547127117 3566163710447138080172669)
                      ·
                        rfl

theorem cell23_6945079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7, 1, 2, 3].length) (baseStart_6945079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945079 prefixEnd_6945079 := by exact prefixLift 6945079
  have htrace : WordTrace (prefixWord ++ tailWord_6945079) baseStart_6945079 baseEnd_6945079 := by
    simpa [prefixWord, tailWord_6945079, baseEnd_6945079] using wordTrace_append hprefix tailTrace_6945079
  have hstable : (prefixWord ++ tailWord_6945079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945079).length < 2 ^ (prefixWord ++ tailWord_6945079).sum := by decide
  have hdescent : baseEnd_6945079 < baseStart_6945079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945086 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 2, 4]
def baseStart_6945086 : Nat := 118140960795 + 6945086 * 2 ^ 59
def prefixEnd_6945086 : Nat := 4983230072969 + 3 ^ 40 * 6945086 * 2
def baseEnd_6945086 : Nat := 1188722434937239850928379

theorem tailTrace_6945086 : CollatzResearch.WordTrace tailWord_6945086 prefixEnd_6945086 1188722434937239850928379 := by
  unfold tailWord_6945086
  simp only [CollatzResearch.WordTrace]
  refine ⟨31663512064643377887696889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168872064344764682067716741 31663512064643377887696889)
  ·
    refine ⟨23747634048482533415772667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31663512064643377887696889 23747634048482533415772667)
    ·
      refine ⟨35621451072723800123659001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23747634048482533415772667 35621451072723800123659001)
      ·
        refine ⟨26716088304542850092744251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35621451072723800123659001 26716088304542850092744251)
        ·
          refine ⟨40074132456814275139116377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26716088304542850092744251 40074132456814275139116377)
          ·
            refine ⟨30055599342610706354337283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40074132456814275139116377 30055599342610706354337283)
            ·
              refine ⟨45083399013916059531505925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30055599342610706354337283 45083399013916059531505925)
              ·
                refine ⟨8453137315109261162157361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45083399013916059531505925 8453137315109261162157361)
                ·
                  refine ⟨6339852986331945871618021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8453137315109261162157361 6339852986331945871618021)
                  ·
                    refine ⟨1188722434937239850928379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6339852986331945871618021 1188722434937239850928379)
                    ·
                      rfl

theorem cell23_6945086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 2, 4].length) (baseStart_6945086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945086 prefixEnd_6945086 := by exact prefixLift 6945086
  have htrace : WordTrace (prefixWord ++ tailWord_6945086) baseStart_6945086 baseEnd_6945086 := by
    simpa [prefixWord, tailWord_6945086, baseEnd_6945086] using wordTrace_append hprefix tailTrace_6945086
  have hstable : (prefixWord ++ tailWord_6945086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945086).length < 2 ^ (prefixWord ++ tailWord_6945086).sum := by decide
  have hdescent : baseEnd_6945086 < baseStart_6945086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945130 : List Nat := [3, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3]
def baseStart_6945130 : Nat := 118140960795 + 6945130 * 2 ^ 59
def prefixEnd_6945130 : Nat := 4983230072969 + 3 ^ 40 * 6945130 * 2
def baseEnd_6945130 : Nat := 3566189897960517380634935

theorem tailTrace_6945130 : CollatzResearch.WordTrace tailWord_6945130 prefixEnd_6945130 3566189897960517380634935 := by
  unfold tailWord_6945130
  simp only [CollatzResearch.WordTrace]
  refine ⟨63327425332246904654044211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168873134219325079077451229 63327425332246904654044211)
  ·
    refine ⟨94991137998370356981066317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63327425332246904654044211 94991137998370356981066317)
    ·
      refine ⟨35621676749388883867899869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94991137998370356981066317 35621676749388883867899869)
      ·
        refine ⟨13358128781020831450462451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35621676749388883867899869 13358128781020831450462451)
        ·
          refine ⟨20037193171531247175693677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358128781020831450462451 20037193171531247175693677)
          ·
            refine ⟨7513947439324217690885129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20037193171531247175693677 7513947439324217690885129)
            ·
              refine ⟨5635460579493163268163847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7513947439324217690885129 5635460579493163268163847)
              ·
                refine ⟨8453190869239744902245771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5635460579493163268163847 8453190869239744902245771)
                ·
                  refine ⟨12679786303859617353368657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453190869239744902245771 12679786303859617353368657)
                  ·
                    refine ⟨9509839727894713015026493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12679786303859617353368657 9509839727894713015026493)
                    ·
                      refine ⟨3566189897960517380634935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9509839727894713015026493 3566189897960517380634935)
                      ·
                        rfl

theorem cell23_6945130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_6945130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945130 prefixEnd_6945130 := by exact prefixLift 6945130
  have htrace : WordTrace (prefixWord ++ tailWord_6945130) baseStart_6945130 baseEnd_6945130 := by
    simpa [prefixWord, tailWord_6945130, baseEnd_6945130] using wordTrace_append hprefix tailTrace_6945130
  have hstable : (prefixWord ++ tailWord_6945130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945130).length < 2 ^ (prefixWord ++ tailWord_6945130).sum := by decide
  have hdescent : baseEnd_6945130 < baseStart_6945130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945152 : List Nat := [2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_6945152 : Nat := 118140960795 + 6945152 * 2 ^ 59
def prefixEnd_6945152 : Nat := 4983230072969 + 3 ^ 40 * 6945152 * 2
def baseEnd_6945152 : Nat := 3566201194534916294559833

theorem tailTrace_6945152 : CollatzResearch.WordTrace tailWord_6945152 prefixEnd_6945152 3566201194534916294559833 := by
  unfold tailWord_6945152
  simp only [CollatzResearch.WordTrace]
  refine ⟨126655251867453958186738855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168873669156605277582318473 126655251867453958186738855)
  ·
    refine ⟨189982877801180937280108283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126655251867453958186738855 189982877801180937280108283)
    ·
      refine ⟨284974316701771405920162425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189982877801180937280108283 284974316701771405920162425)
      ·
        refine ⟨213730737526328554440121819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284974316701771405920162425 213730737526328554440121819)
        ·
          refine ⟨320596106289492831660182729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213730737526328554440121819 320596106289492831660182729)
          ·
            refine ⟨240447079717119623745137047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320596106289492831660182729 240447079717119623745137047)
            ·
              refine ⟨360670619575679435617705571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240447079717119623745137047 360670619575679435617705571)
              ·
                refine ⟨541005929363519153426558357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 360670619575679435617705571 541005929363519153426558357)
                ·
                  refine ⟨25359652938914960316869923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 541005929363519153426558357 25359652938914960316869923)
                  ·
                    refine ⟨38039479408372440475304885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25359652938914960316869923 38039479408372440475304885)
                    ·
                      refine ⟨3566201194534916294559833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38039479408372440475304885 3566201194534916294559833)
                      ·
                        rfl

theorem cell23_6945152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_6945152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945152 prefixEnd_6945152 := by exact prefixLift 6945152
  have htrace : WordTrace (prefixWord ++ tailWord_6945152) baseStart_6945152 baseEnd_6945152 := by
    simpa [prefixWord, tailWord_6945152, baseEnd_6945152] using wordTrace_append hprefix tailTrace_6945152
  have hstable : (prefixWord ++ tailWord_6945152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945152).length < 2 ^ (prefixWord ++ tailWord_6945152).sum := by decide
  have hdescent : baseEnd_6945152 < baseStart_6945152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945236 : List Nat := [2, 4, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_6945236 : Nat := 118140960795 + 6945236 * 2 ^ 59
def prefixEnd_6945236 : Nat := 4983230072969 + 3 ^ 40 * 6945236 * 2
def baseEnd_6945236 : Nat := 1188748108969964655303149

theorem tailTrace_6945236 : CollatzResearch.WordTrace tailWord_6945236 prefixEnd_6945236 1188748108969964655303149 := by
  unfold tailWord_6945236
  simp only [CollatzResearch.WordTrace]
  refine ⟨126656783733301799359767781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168875711644402399146357041 126656783733301799359767781)
  ·
    refine ⟨23748146949994087379956459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126656783733301799359767781 23748146949994087379956459)
    ·
      refine ⟨35622220424991131069934689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23748146949994087379956459 35622220424991131069934689)
      ·
        refine ⟨26716665318743348302451017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35622220424991131069934689 26716665318743348302451017)
        ·
          refine ⟨20037498989057511226838263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26716665318743348302451017 20037498989057511226838263)
          ·
            refine ⟨30056248483586266840257395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20037498989057511226838263 30056248483586266840257395)
            ·
              refine ⟨45084372725379400260386093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30056248483586266840257395 45084372725379400260386093)
              ·
                refine ⟨16906639772017275097644785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45084372725379400260386093 16906639772017275097644785)
                ·
                  refine ⟨12679979829012956323233589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16906639772017275097644785 12679979829012956323233589)
                  ·
                    refine ⟨1188748108969964655303149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12679979829012956323233589 1188748108969964655303149)
                    ·
                      rfl

theorem cell23_6945236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_6945236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945236 prefixEnd_6945236 := by exact prefixLift 6945236
  have htrace : WordTrace (prefixWord ++ tailWord_6945236) baseStart_6945236 baseEnd_6945236 := by
    simpa [prefixWord, tailWord_6945236, baseEnd_6945236] using wordTrace_append hprefix tailTrace_6945236
  have hstable : (prefixWord ++ tailWord_6945236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945236).length < 2 ^ (prefixWord ++ tailWord_6945236).sum := by decide
  have hdescent : baseEnd_6945236 < baseStart_6945236 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945256 : List Nat := [2, 1, 4, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6945256 : Nat := 118140960795 + 6945256 * 2 ^ 59
def prefixEnd_6945256 : Nat := 4983230072969 + 3 ^ 40 * 6945256 * 2
def baseEnd_6945256 : Nat := 3566254596522983887659355

theorem tailTrace_6945256 : CollatzResearch.WordTrace tailWord_6945256 prefixEnd_6945256 3566254596522983887659355 := by
  unfold tailWord_6945256
  simp only [CollatzResearch.WordTrace]
  refine ⟨126657148463265571067631811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168876197951020761423509081 126657148463265571067631811)
  ·
    refine ⟨189985722694898356601447717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126657148463265571067631811 189985722694898356601447717)
    ·
      refine ⟨35622323005293441862771447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 189985722694898356601447717 35622323005293441862771447)
      ·
        refine ⟨53433484507940162794157171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35622323005293441862771447 53433484507940162794157171)
        ·
          refine ⟨80150226761910244191235757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53433484507940162794157171 80150226761910244191235757)
          ·
            refine ⟨30056335035716341571713409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80150226761910244191235757 30056335035716341571713409)
            ·
              refine ⟨22542251276787256178785057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30056335035716341571713409 22542251276787256178785057)
              ·
                refine ⟨16906688457590442134088793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22542251276787256178785057 16906688457590442134088793)
                ·
                  refine ⟨12680016343192831600566595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16906688457590442134088793 12680016343192831600566595)
                  ·
                    refine ⟨19020024514789247400849893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12680016343192831600566595 19020024514789247400849893)
                    ·
                      refine ⟨3566254596522983887659355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19020024514789247400849893 3566254596522983887659355)
                      ·
                        rfl

theorem cell23_6945256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6945256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945256 prefixEnd_6945256 := by exact prefixLift 6945256
  have htrace : WordTrace (prefixWord ++ tailWord_6945256) baseStart_6945256 baseEnd_6945256 := by
    simpa [prefixWord, tailWord_6945256, baseEnd_6945256] using wordTrace_append hprefix tailTrace_6945256
  have hstable : (prefixWord ++ tailWord_6945256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945256).length < 2 ^ (prefixWord ++ tailWord_6945256).sum := by decide
  have hdescent : baseEnd_6945256 < baseStart_6945256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945279 : List Nat := [1, 1, 2, 2, 1, 2, 3, 5, 6]
def baseStart_6945279 : Nat := 118140960795 + 6945279 * 2 ^ 59
def prefixEnd_6945279 : Nat := 4983230072969 + 3 ^ 40 * 6945279 * 2
def baseEnd_6945279 : Nat := 396251822953115255296861

theorem tailTrace_6945279 : CollatzResearch.WordTrace tailWord_6945279 prefixEnd_6945279 396251822953115255296861 := by
  unfold tailWord_6945279
  simp only [CollatzResearch.WordTrace]
  refine ⟨253315135805447817063350891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168876757203631878042233927 253315135805447817063350891)
  ·
    refine ⟨379972703708171725595026337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253315135805447817063350891 379972703708171725595026337)
    ·
      refine ⟨284979527781128794196269753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379972703708171725595026337 284979527781128794196269753)
      ·
        refine ⟨213734645835846595647202315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284979527781128794196269753 213734645835846595647202315)
        ·
          refine ⟨320601968753769893470803473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213734645835846595647202315 320601968753769893470803473)
          ·
            refine ⟨240451476565327420103102605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320601968753769893470803473 240451476565327420103102605)
            ·
              refine ⟨90169303711997782538663477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240451476565327420103102605 90169303711997782538663477)
              ·
                refine ⟨8453372222999792112999701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90169303711997782538663477 8453372222999792112999701)
                ·
                  refine ⟨396251822953115255296861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8453372222999792112999701 396251822953115255296861)
                  ·
                    rfl

theorem cell23_6945279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 5, 6].length) (baseStart_6945279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945279 prefixEnd_6945279 := by exact prefixLift 6945279
  have htrace : WordTrace (prefixWord ++ tailWord_6945279) baseStart_6945279 baseEnd_6945279 := by
    simpa [prefixWord, tailWord_6945279, baseEnd_6945279] using wordTrace_append hprefix tailTrace_6945279
  have hstable : (prefixWord ++ tailWord_6945279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945279).length < 2 ^ (prefixWord ++ tailWord_6945279).sum := by decide
  have hdescent : baseEnd_6945279 < baseStart_6945279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945289 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_6945289 : Nat := 118140960795 + 6945289 * 2 ^ 59
def prefixEnd_6945289 : Nat := 4983230072969 + 3 ^ 40 * 6945289 * 2
def baseEnd_6945289 : Nat := 3566271541384582258546703

theorem tailTrace_6945289 : CollatzResearch.WordTrace tailWord_6945289 prefixEnd_6945289 3566271541384582258546703 := by
  unfold tailWord_6945289
  simp only [CollatzResearch.WordTrace]
  refine ⟨253315500535411588771214921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168877000356941059180809947 253315500535411588771214921)
  ·
    refine ⟨189986625401558691578411191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253315500535411588771214921 189986625401558691578411191)
    ·
      refine ⟨284979938102338037367616787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189986625401558691578411191 284979938102338037367616787)
      ·
        refine ⟨427469907153507056051425181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284979938102338037367616787 427469907153507056051425181)
        ·
          refine ⟨160301215182565146019284443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427469907153507056051425181 160301215182565146019284443)
          ·
            refine ⟨240451822773847719028926665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160301215182565146019284443 240451822773847719028926665)
            ·
              refine ⟨180338867080385789271694999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240451822773847719028926665 180338867080385789271694999)
              ·
                refine ⟨270508300620578683907542499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180338867080385789271694999 270508300620578683907542499)
                ·
                  refine ⟨405762450930868025861313749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270508300620578683907542499 405762450930868025861313749)
                  ·
                    refine ⟨9510057443692219356124541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 405762450930868025861313749 9510057443692219356124541)
                    ·
                      refine ⟨3566271541384582258546703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510057443692219356124541 3566271541384582258546703)
                      ·
                        rfl

theorem cell23_6945289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_6945289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945289 prefixEnd_6945289 := by exact prefixLift 6945289
  have htrace : WordTrace (prefixWord ++ tailWord_6945289) baseStart_6945289 baseEnd_6945289 := by
    simpa [prefixWord, tailWord_6945289, baseEnd_6945289] using wordTrace_append hprefix tailTrace_6945289
  have hstable : (prefixWord ++ tailWord_6945289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945289).length < 2 ^ (prefixWord ++ tailWord_6945289).sum := by decide
  have hdescent : baseEnd_6945289 < baseStart_6945289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945356 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 6, 4]
def baseStart_6945356 : Nat := 118140960795 + 6945356 * 2 ^ 59
def prefixEnd_6945356 : Nat := 4983230072969 + 3 ^ 40 * 6945356 * 2
def baseEnd_6945356 : Nat := 1188768648196144498802965

theorem tailTrace_6945356 : CollatzResearch.WordTrace tailWord_6945356 prefixEnd_6945356 1188768648196144498802965 := by
  unfold tailWord_6945356
  simp only [CollatzResearch.WordTrace]
  refine ⟨126658972113084429606951961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168878629484112572809269281 126658972113084429606951961)
  ·
    refine ⟨94994229084813322205213971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126658972113084429606951961 94994229084813322205213971)
    ·
      refine ⟨142491343627219983307820957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94994229084813322205213971 142491343627219983307820957)
      ·
        refine ⟨53434253860207493740432859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142491343627219983307820957 53434253860207493740432859)
        ·
          refine ⟨80151380790311240610649289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53434253860207493740432859 80151380790311240610649289)
          ·
            refine ⟨60113535592733430457986967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80151380790311240610649289 60113535592733430457986967)
            ·
              refine ⟨90170303389100145686980451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60113535592733430457986967 90170303389100145686980451)
              ·
                refine ⟨135255455083650218530470677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90170303389100145686980451 135255455083650218530470677)
                ·
                  refine ⟨6340099457046103993615813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 135255455083650218530470677 6340099457046103993615813)
                  ·
                    refine ⟨1188768648196144498802965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6340099457046103993615813 1188768648196144498802965)
                    ·
                      rfl

theorem cell23_6945356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 6, 4].length) (baseStart_6945356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945356 prefixEnd_6945356 := by exact prefixLift 6945356
  have htrace : WordTrace (prefixWord ++ tailWord_6945356) baseStart_6945356 baseEnd_6945356 := by
    simpa [prefixWord, tailWord_6945356, baseEnd_6945356] using wordTrace_append hprefix tailTrace_6945356
  have hstable : (prefixWord ++ tailWord_6945356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945356).length < 2 ^ (prefixWord ++ tailWord_6945356).sum := by decide
  have hdescent : baseEnd_6945356 < baseStart_6945356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945386 : List Nat := [3, 1, 3, 2, 1, 1, 4, 8]
def baseStart_6945386 : Nat := 118140960795 + 6945386 * 2 ^ 59
def prefixEnd_6945386 : Nat := 4983230072969 + 3 ^ 40 * 6945386 * 2
def baseEnd_6945386 : Nat := 132085975889187717741991

theorem tailTrace_6945386 : CollatzResearch.WordTrace tailWord_6945386 prefixEnd_6945386 132085975889187717741991 := by
  unfold tailWord_6945386
  simp only [CollatzResearch.WordTrace]
  refine ⟨63329759604015043584374003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168879358944040116224997341 63329759604015043584374003)
  ·
    refine ⟨94994639406022565376561005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63329759604015043584374003 94994639406022565376561005)
    ·
      refine ⟨35622989777258462016210377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94994639406022565376561005 35622989777258462016210377)
      ·
        refine ⟨26717242332943846512157783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35622989777258462016210377 26717242332943846512157783)
        ·
          refine ⟨40075863499415769768236675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26717242332943846512157783 40075863499415769768236675)
          ·
            refine ⟨60113795249123654652355013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40075863499415769768236675 60113795249123654652355013)
            ·
              refine ⟨11271336609210685247316565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60113795249123654652355013 11271336609210685247316565)
              ·
                refine ⟨132085975889187717741991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11271336609210685247316565 132085975889187717741991)
                ·
                  rfl

theorem cell23_6945386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_6945386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945386 prefixEnd_6945386 := by exact prefixLift 6945386
  have htrace : WordTrace (prefixWord ++ tailWord_6945386) baseStart_6945386 baseEnd_6945386 := by
    simpa [prefixWord, tailWord_6945386, baseEnd_6945386] using wordTrace_append hprefix tailTrace_6945386
  have hstable : (prefixWord ++ tailWord_6945386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945386).length < 2 ^ (prefixWord ++ tailWord_6945386).sum := by decide
  have hdescent : baseEnd_6945386 < baseStart_6945386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945390 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_6945390 : Nat := 118140960795 + 6945390 * 2 ^ 59
def prefixEnd_6945390 : Nat := 4983230072969 + 3 ^ 40 * 6945390 * 2
def baseEnd_6945390 : Nat := 1188774467643562121127913

theorem tailTrace_6945390 : CollatzResearch.WordTrace tailWord_6945390 prefixEnd_6945390 1188774467643562121127913 := by
  unfold tailWord_6945390
  simp only [CollatzResearch.WordTrace]
  refine ⟨31664898038505710377580203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168879456205363788680427749 31664898038505710377580203)
  ·
    refine ⟨47497347057758565566370305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31664898038505710377580203 47497347057758565566370305)
    ·
      refine ⟨35623010293318924174777729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47497347057758565566370305 35623010293318924174777729)
      ·
        refine ⟨26717257719989193131083297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35623010293318924174777729 26717257719989193131083297)
        ·
          refine ⟨20037943289991894848312473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26717257719989193131083297 20037943289991894848312473)
          ·
            refine ⟨15028457467493921136234355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20037943289991894848312473 15028457467493921136234355)
            ·
              refine ⟨22542686201240881704351533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15028457467493921136234355 22542686201240881704351533)
              ·
                refine ⟨8453507325465330639131825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22542686201240881704351533 8453507325465330639131825)
                ·
                  refine ⟨6340130494098997979348869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8453507325465330639131825 6340130494098997979348869)
                  ·
                    refine ⟨1188774467643562121127913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6340130494098997979348869 1188774467643562121127913)
                    ·
                      rfl

theorem cell23_6945390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_6945390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945390 prefixEnd_6945390 := by exact prefixLift 6945390
  have htrace : WordTrace (prefixWord ++ tailWord_6945390) baseStart_6945390 baseEnd_6945390 := by
    simpa [prefixWord, tailWord_6945390, baseEnd_6945390] using wordTrace_append hprefix tailTrace_6945390
  have hstable : (prefixWord ++ tailWord_6945390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945390).length < 2 ^ (prefixWord ++ tailWord_6945390).sum := by decide
  have hdescent : baseEnd_6945390 < baseStart_6945390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945397 : List Nat := [1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_6945397 : Nat := 118140960795 + 6945397 * 2 ^ 59
def prefixEnd_6945397 : Nat := 4983230072969 + 3 ^ 40 * 6945397 * 2
def baseEnd_6945397 : Nat := 3566326997295267835996207

theorem tailTrace_6945397 : CollatzResearch.WordTrace tailWord_6945397 prefixEnd_6945397 3566326997295267835996207 := by
  unfold tailWord_6945397
  simp only [CollatzResearch.WordTrace]
  refine ⟨253319439619020323216146445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168879626412680215477430963 253319439619020323216146445)
  ·
    refine ⟨94994789857132621206054917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253319439619020323216146445 94994789857132621206054917)
    ·
      refine ⟨17811523098212366476135297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94994789857132621206054917 17811523098212366476135297)
      ·
        refine ⟨13358642323659274857101473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17811523098212366476135297 13358642323659274857101473)
        ·
          refine ⟨10018981742744456142826105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13358642323659274857101473 10018981742744456142826105)
          ·
            refine ⟨7514236307058342107119579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10018981742744456142826105 7514236307058342107119579)
            ·
              refine ⟨11271354460587513160679369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514236307058342107119579 11271354460587513160679369)
              ·
                refine ⟨8453515845440634870509527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11271354460587513160679369 8453515845440634870509527)
                ·
                  refine ⟨12680273768160952305764291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453515845440634870509527 12680273768160952305764291)
                  ·
                    refine ⟨19020410652241428458646437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12680273768160952305764291 19020410652241428458646437)
                    ·
                      refine ⟨3566326997295267835996207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19020410652241428458646437 3566326997295267835996207)
                      ·
                        rfl

theorem cell23_6945397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_6945397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945397 prefixEnd_6945397 := by exact prefixLift 6945397
  have htrace : WordTrace (prefixWord ++ tailWord_6945397) baseStart_6945397 baseEnd_6945397 := by
    simpa [prefixWord, tailWord_6945397, baseEnd_6945397] using wordTrace_append hprefix tailTrace_6945397
  have hstable : (prefixWord ++ tailWord_6945397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945397).length < 2 ^ (prefixWord ++ tailWord_6945397).sum := by decide
  have hdescent : baseEnd_6945397 < baseStart_6945397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945413 : List Nat := [1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 3]
def baseStart_6945413 : Nat := 118140960795 + 6945413 * 2 ^ 59
def prefixEnd_6945413 : Nat := 4983230072969 + 3 ^ 40 * 6945413 * 2
def baseEnd_6945413 : Nat := 3566335212985739773396133

theorem tailTrace_6945413 : CollatzResearch.WordTrace tailWord_6945413 prefixEnd_6945413 3566335212985739773396133 := by
  unfold tailWord_6945413
  simp only [CollatzResearch.WordTrace]
  refine ⟨253320023186962357948728893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168880015457974905299152595 253320023186962357948728893)
  ·
    refine ⟨94995008695110884230773335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253320023186962357948728893 94995008695110884230773335)
    ·
      refine ⟨142492513042666326346160003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94995008695110884230773335 142492513042666326346160003)
      ·
        refine ⟨213738769563999489519240005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142492513042666326346160003 213738769563999489519240005)
        ·
          refine ⟨40076019293249904284857501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213738769563999489519240005 40076019293249904284857501)
          ·
            refine ⟨15028507234968714106821563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40076019293249904284857501 15028507234968714106821563)
            ·
              refine ⟨22542760852453071160232345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15028507234968714106821563 22542760852453071160232345)
              ·
                refine ⟨16907070639339803370174259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22542760852453071160232345 16907070639339803370174259)
                ·
                  refine ⟨25360605959009705055261389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16907070639339803370174259 25360605959009705055261389)
                  ·
                    refine ⟨9510227234628639395723021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25360605959009705055261389 9510227234628639395723021)
                    ·
                      refine ⟨3566335212985739773396133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510227234628639395723021 3566335212985739773396133)
                      ·
                        rfl

theorem cell23_6945413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 3, 3].length) (baseStart_6945413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945413 prefixEnd_6945413 := by exact prefixLift 6945413
  have htrace : WordTrace (prefixWord ++ tailWord_6945413) baseStart_6945413 baseEnd_6945413 := by
    simpa [prefixWord, tailWord_6945413, baseEnd_6945413] using wordTrace_append hprefix tailTrace_6945413
  have hstable : (prefixWord ++ tailWord_6945413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945413).length < 2 ^ (prefixWord ++ tailWord_6945413).sum := by decide
  have hdescent : baseEnd_6945413 < baseStart_6945413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945447 : List Nat := [1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6945447 : Nat := 118140960795 + 6945447 * 2 ^ 59
def prefixEnd_6945447 : Nat := 4983230072969 + 3 ^ 40 * 6945447 * 2
def baseEnd_6945447 : Nat := 3566352671327992640370977

theorem tailTrace_6945447 : CollatzResearch.WordTrace tailWord_6945447 prefixEnd_6945447 3566352671327992640370977 := by
  unfold tailWord_6945447
  simp only [CollatzResearch.WordTrace]
  refine ⟨253321263268839181755466595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168880842179226121170311063 253321263268839181755466595)
  ·
    refine ⟨379981894903258772633199893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253321263268839181755466595 379981894903258772633199893)
    ·
      refine ⟨17811651323590254967181245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 379981894903258772633199893 17811651323590254967181245)
      ·
        refine ⟨6679369246346345612692967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17811651323590254967181245 6679369246346345612692967)
        ·
          refine ⟨10019053869519518419039451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6679369246346345612692967 10019053869519518419039451)
          ·
            refine ⟨15028580804279277628559177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019053869519518419039451 15028580804279277628559177)
            ·
              refine ⟨11271435603209458221419383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15028580804279277628559177 11271435603209458221419383)
              ·
                refine ⟨16907153404814187332129075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271435603209458221419383 16907153404814187332129075)
                ·
                  refine ⟨25360730107221280998193613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16907153404814187332129075 25360730107221280998193613)
                  ·
                    refine ⟨9510273790207980374322605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25360730107221280998193613 9510273790207980374322605)
                    ·
                      refine ⟨3566352671327992640370977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510273790207980374322605 3566352671327992640370977)
                      ·
                        rfl

theorem cell23_6945447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6945447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945447 prefixEnd_6945447 := by exact prefixLift 6945447
  have htrace : WordTrace (prefixWord ++ tailWord_6945447) baseStart_6945447 baseEnd_6945447 := by
    simpa [prefixWord, tailWord_6945447, baseEnd_6945447] using wordTrace_append hprefix tailTrace_6945447
  have hstable : (prefixWord ++ tailWord_6945447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945447).length < 2 ^ (prefixWord ++ tailWord_6945447).sum := by decide
  have hdescent : baseEnd_6945447 < baseStart_6945447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945456 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_6945456 : Nat := 118140960795 + 6945456 * 2 ^ 59
def prefixEnd_6945456 : Nat := 4983230072969 + 3 ^ 40 * 6945456 * 2
def baseEnd_6945456 : Nat := 3566357292653883105158435

theorem tailTrace_6945456 : CollatzResearch.WordTrace tailWord_6945456 prefixEnd_6945456 3566357292653883105158435 := by
  unfold tailWord_6945456
  simp only [CollatzResearch.WordTrace]
  refine ⟨126660795762903288146272111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168881061017204384195029481 126660795762903288146272111)
  ·
    refine ⟨189991193644354932219408167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126660795762903288146272111 189991193644354932219408167)
    ·
      refine ⟨284986790466532398329112251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189991193644354932219408167 284986790466532398329112251)
      ·
        refine ⟨427480185699798597493668377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284986790466532398329112251 427480185699798597493668377)
        ·
          refine ⟨320610139274848948120251283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427480185699798597493668377 320610139274848948120251283)
          ·
            refine ⟨480915208912273422180376925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320610139274848948120251283 480915208912273422180376925)
            ·
              refine ⟨180343203342102533317641347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 480915208912273422180376925 180343203342102533317641347)
              ·
                refine ⟨270514805013153799976462021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180343203342102533317641347 270514805013153799976462021)
                ·
                  refine ⟨50721525939966337495586629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270514805013153799976462021 50721525939966337495586629)
                  ·
                    refine ⟨9510286113743688280422493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50721525939966337495586629 9510286113743688280422493)
                    ·
                      refine ⟨3566357292653883105158435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510286113743688280422493 3566357292653883105158435)
                      ·
                        rfl

theorem cell23_6945456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_6945456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945456 prefixEnd_6945456 := by exact prefixLift 6945456
  have htrace : WordTrace (prefixWord ++ tailWord_6945456) baseStart_6945456 baseEnd_6945456 := by
    simpa [prefixWord, tailWord_6945456, baseEnd_6945456] using wordTrace_append hprefix tailTrace_6945456
  have hstable : (prefixWord ++ tailWord_6945456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945456).length < 2 ^ (prefixWord ++ tailWord_6945456).sum := by decide
  have hdescent : baseEnd_6945456 < baseStart_6945456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945466 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4]
def baseStart_6945466 : Nat := 118140960795 + 6945466 * 2 ^ 59
def prefixEnd_6945466 : Nat := 4983230072969 + 3 ^ 40 * 6945466 * 2
def baseEnd_6945466 : Nat := 3566362427460428066033389

theorem tailTrace_6945466 : CollatzResearch.WordTrace tailWord_6945466 prefixEnd_6945466 3566362427460428066033389 := by
  unfold tailWord_6945466
  simp only [CollatzResearch.WordTrace]
  refine ⟨63330489063942587000102063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168881304170513565333605501 63330489063942587000102063)
  ·
    refine ⟨94995733595913880500153095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63330489063942587000102063 94995733595913880500153095)
    ·
      refine ⟨142493600393870820750229643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94995733595913880500153095 142493600393870820750229643)
      ·
        refine ⟨213740400590806231125344465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142493600393870820750229643 213740400590806231125344465)
        ·
          refine ⟨160305300443104673344008349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213740400590806231125344465 160305300443104673344008349)
          ·
            refine ⟨60114487666164252504003131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160305300443104673344008349 60114487666164252504003131)
            ·
              refine ⟨90171731499246378756004697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60114487666164252504003131 90171731499246378756004697)
              ·
                refine ⟨67628798624434784067003523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90171731499246378756004697 67628798624434784067003523)
                ·
                  refine ⟨101443197936652176100505285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67628798624434784067003523 101443197936652176100505285)
                  ·
                    refine ⟨19020599613122283018844741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101443197936652176100505285 19020599613122283018844741)
                    ·
                      refine ⟨3566362427460428066033389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19020599613122283018844741 3566362427460428066033389)
                      ·
                        rfl

theorem cell23_6945466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_6945466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945466 prefixEnd_6945466 := by exact prefixLift 6945466
  have htrace : WordTrace (prefixWord ++ tailWord_6945466) baseStart_6945466 baseEnd_6945466 := by
    simpa [prefixWord, tailWord_6945466, baseEnd_6945466] using wordTrace_append hprefix tailTrace_6945466
  have hstable : (prefixWord ++ tailWord_6945466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945466).length < 2 ^ (prefixWord ++ tailWord_6945466).sum := by decide
  have hdescent : baseEnd_6945466 < baseStart_6945466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945470 : List Nat := [4, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2]
def baseStart_6945470 : Nat := 118140960795 + 6945470 * 2 ^ 59
def prefixEnd_6945470 : Nat := 4983230072969 + 3 ^ 40 * 6945470 * 2
def baseEnd_6945470 : Nat := 3566364481383046050383371

theorem tailTrace_6945470 : CollatzResearch.WordTrace tailWord_6945470 prefixEnd_6945470 3566364481383046050383371 := by
  unfold tailWord_6945470
  simp only [CollatzResearch.WordTrace]
  refine ⟨31665262768469482085444233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168881401431837237789035909 31665262768469482085444233)
  ·
    refine ⟨23748947076352111564083175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31665262768469482085444233 23748947076352111564083175)
    ·
      refine ⟨35623420614528167346124763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23748947076352111564083175 35623420614528167346124763)
      ·
        refine ⟨53435130921792251019187145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35623420614528167346124763 53435130921792251019187145)
        ·
          refine ⟨40076348191344188264390359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53435130921792251019187145 40076348191344188264390359)
          ·
            refine ⟨60114522287016282396585539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40076348191344188264390359 60114522287016282396585539)
            ·
              refine ⟨90171783430524423594878309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60114522287016282396585539 90171783430524423594878309)
              ·
                refine ⟨16907209393223329424039683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90171783430524423594878309 16907209393223329424039683)
                ·
                  refine ⟨25360814089834994136059525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16907209393223329424039683 25360814089834994136059525)
                  ·
                    refine ⟨4755152641844061400511161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25360814089834994136059525 4755152641844061400511161)
                    ·
                      refine ⟨3566364481383046050383371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755152641844061400511161 3566364481383046050383371)
                      ·
                        rfl

theorem cell23_6945470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_6945470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945470 prefixEnd_6945470 := by exact prefixLift 6945470
  have htrace : WordTrace (prefixWord ++ tailWord_6945470) baseStart_6945470 baseEnd_6945470 := by
    simpa [prefixWord, tailWord_6945470, baseEnd_6945470] using wordTrace_append hprefix tailTrace_6945470
  have hstable : (prefixWord ++ tailWord_6945470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945470).length < 2 ^ (prefixWord ++ tailWord_6945470).sum := by decide
  have hdescent : baseEnd_6945470 < baseStart_6945470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945500 : List Nat := [2, 2, 5, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_6945500 : Nat := 118140960795 + 6945500 * 2 ^ 59
def prefixEnd_6945500 : Nat := 4983230072969 + 3 ^ 40 * 6945500 * 2
def baseEnd_6945500 : Nat := 3566379885802680933008233

theorem tailTrace_6945500 : CollatzResearch.WordTrace tailWord_6945500 prefixEnd_6945500 3566379885802680933008233 := by
  unfold tailWord_6945500
  simp only [CollatzResearch.WordTrace]
  refine ⟨126661598168823585903572977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168882130891764781204763969 126661598168823585903572977)
  ·
    refine ⟨94996198626617689427679733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126661598168823585903572977 94996198626617689427679733)
    ·
      refine ⟨8905893621245408383844975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94996198626617689427679733 8905893621245408383844975)
      ·
        refine ⟨13358840431868112575767463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8905893621245408383844975 13358840431868112575767463)
        ·
          refine ⟨20038260647802168863651195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13358840431868112575767463 20038260647802168863651195)
          ·
            refine ⟨30057390971703253295476793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20038260647802168863651195 30057390971703253295476793)
            ·
              refine ⟨22543043228777439971607595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30057390971703253295476793 22543043228777439971607595)
              ·
                refine ⟨33814564843166159957411393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22543043228777439971607595 33814564843166159957411393)
                ·
                  refine ⟨25360923632374619968058545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33814564843166159957411393 25360923632374619968058545)
                  ·
                    refine ⟨19020692724280964976043909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25360923632374619968058545 19020692724280964976043909)
                    ·
                      refine ⟨3566379885802680933008233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19020692724280964976043909 3566379885802680933008233)
                      ·
                        rfl

theorem cell23_6945500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_6945500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945500 prefixEnd_6945500 := by exact prefixLift 6945500
  have htrace : WordTrace (prefixWord ++ tailWord_6945500) baseStart_6945500 baseEnd_6945500 := by
    simpa [prefixWord, tailWord_6945500, baseEnd_6945500] using wordTrace_append hprefix tailTrace_6945500
  have hstable : (prefixWord ++ tailWord_6945500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945500).length < 2 ^ (prefixWord ++ tailWord_6945500).sum := by decide
  have hdescent : baseEnd_6945500 < baseStart_6945500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945503 : List Nat := [1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_6945503 : Nat := 118140960795 + 6945503 * 2 ^ 59
def prefixEnd_6945503 : Nat := 4983230072969 + 3 ^ 40 * 6945503 * 2
def baseEnd_6945503 : Nat := 3566381426244644421270719

theorem tailTrace_6945503 : CollatzResearch.WordTrace tailWord_6945503 prefixEnd_6945503 3566381426244644421270719 := by
  unfold tailWord_6945503
  simp only [CollatzResearch.WordTrace]
  refine ⟨253323305756636303319505163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168882203837757535546336775 253323305756636303319505163)
  ·
    refine ⟨379984958634954454979257745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253323305756636303319505163 379984958634954454979257745)
    ·
      refine ⟨284988718976215841234443309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379984958634954454979257745 284988718976215841234443309)
      ·
        refine ⟨106870769616080940462916241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 284988718976215841234443309 106870769616080940462916241)
        ·
          refine ⟨80153077212060705347187181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106870769616080940462916241 80153077212060705347187181)
          ·
            refine ⟨30057403954522764505195193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80153077212060705347187181 30057403954522764505195193)
            ·
              refine ⟨22543052965892073378896395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30057403954522764505195193 22543052965892073378896395)
              ·
                refine ⟨33814579448838110068344593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22543052965892073378896395 33814579448838110068344593)
                ·
                  refine ⟨25360934586628582551258445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33814579448838110068344593 25360934586628582551258445)
                  ·
                    refine ⟨9510350469985718456721917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25360934586628582551258445 9510350469985718456721917)
                    ·
                      refine ⟨3566381426244644421270719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510350469985718456721917 3566381426244644421270719)
                      ·
                        rfl

theorem cell23_6945503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_6945503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945503 prefixEnd_6945503 := by exact prefixLift 6945503
  have htrace : WordTrace (prefixWord ++ tailWord_6945503) baseStart_6945503 baseEnd_6945503 := by
    simpa [prefixWord, tailWord_6945503, baseEnd_6945503] using wordTrace_append hprefix tailTrace_6945503
  have hstable : (prefixWord ++ tailWord_6945503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945503).length < 2 ^ (prefixWord ++ tailWord_6945503).sum := by decide
  have hdescent : baseEnd_6945503 < baseStart_6945503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945513 : List Nat := [1, 2, 1, 1, 1, 2, 4, 2, 2, 5, 2]
def baseStart_6945513 : Nat := 118140960795 + 6945513 * 2 ^ 59
def prefixEnd_6945513 : Nat := 4983230072969 + 3 ^ 40 * 6945513 * 2
def baseEnd_6945513 : Nat := 3566386561051189382145673

theorem tailTrace_6945513 : CollatzResearch.WordTrace tailWord_6945513 prefixEnd_6945513 3566386561051189382145673 := by
  unfold tailWord_6945513
  simp only [CollatzResearch.WordTrace]
  refine ⟨253323670486600075027369193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168882446991066716684912795 253323670486600075027369193)
  ·
    refine ⟨189992752864950056270526895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253323670486600075027369193 189992752864950056270526895)
    ·
      refine ⟨284989129297425084405790343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 189992752864950056270526895 284989129297425084405790343)
      ·
        refine ⟨427483693946137626608685515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 284989129297425084405790343 427483693946137626608685515)
        ·
          refine ⟨641225540919206439913028273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427483693946137626608685515 641225540919206439913028273)
          ·
            refine ⟨480919155689404829934771205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641225540919206439913028273 480919155689404829934771205)
            ·
              refine ⟨90172341691763405612769601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480919155689404829934771205 90172341691763405612769601)
              ·
                refine ⟨67629256268822554209577201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90172341691763405612769601 67629256268822554209577201)
                ·
                  refine ⟨50721942201616915657182901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67629256268822554209577201 50721942201616915657182901)
                  ·
                    refine ⟨4755182081401585842860897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50721942201616915657182901 4755182081401585842860897)
                    ·
                      refine ⟨3566386561051189382145673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755182081401585842860897 3566386561051189382145673)
                      ·
                        rfl

theorem cell23_6945513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 2, 2, 5, 2].length) (baseStart_6945513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945513 prefixEnd_6945513 := by exact prefixLift 6945513
  have htrace : WordTrace (prefixWord ++ tailWord_6945513) baseStart_6945513 baseEnd_6945513 := by
    simpa [prefixWord, tailWord_6945513, baseEnd_6945513] using wordTrace_append hprefix tailTrace_6945513
  have hstable : (prefixWord ++ tailWord_6945513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945513).length < 2 ^ (prefixWord ++ tailWord_6945513).sum := by decide
  have hdescent : baseEnd_6945513 < baseStart_6945513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945516 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 5]
def baseStart_6945516 : Nat := 118140960795 + 6945516 * 2 ^ 59
def prefixEnd_6945516 : Nat := 4983230072969 + 3 ^ 40 * 6945516 * 2
def baseEnd_6945516 : Nat := 3566388101493152870408159

theorem tailTrace_6945516 : CollatzResearch.WordTrace tailWord_6945516 prefixEnd_6945516 3566388101493152870408159 := by
  unfold tailWord_6945516
  simp only [CollatzResearch.WordTrace]
  refine ⟨126661889952794603269864201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168882519937059471026485601 126661889952794603269864201)
  ·
    refine ⟨94996417464595952452398151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126661889952794603269864201 94996417464595952452398151)
    ·
      refine ⟨142494626196893928678597227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94996417464595952452398151 142494626196893928678597227)
      ·
        refine ⟨213741939295340893017895841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142494626196893928678597227 213741939295340893017895841)
        ·
          refine ⟨160306454471505669763421881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213741939295340893017895841 160306454471505669763421881)
          ·
            refine ⟨120229840853629252322566411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160306454471505669763421881 120229840853629252322566411)
            ·
              refine ⟨180344761280443878483849617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120229840853629252322566411 180344761280443878483849617)
              ·
                refine ⟨135258570960332908862887213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180344761280443878483849617 135258570960332908862887213)
                ·
                  refine ⟨50721964110124840823582705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135258570960332908862887213 50721964110124840823582705)
                  ·
                    refine ⟨38041473082593630617687029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50721964110124840823582705 38041473082593630617687029)
                    ·
                      refine ⟨3566388101493152870408159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38041473082593630617687029 3566388101493152870408159)
                      ·
                        rfl

theorem cell23_6945516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 5].length) (baseStart_6945516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945516 prefixEnd_6945516 := by exact prefixLift 6945516
  have htrace : WordTrace (prefixWord ++ tailWord_6945516) baseStart_6945516 baseEnd_6945516 := by
    simpa [prefixWord, tailWord_6945516, baseEnd_6945516] using wordTrace_append hprefix tailTrace_6945516
  have hstable : (prefixWord ++ tailWord_6945516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945516).length < 2 ^ (prefixWord ++ tailWord_6945516).sum := by decide
  have hdescent : baseEnd_6945516 < baseStart_6945516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945580 : List Nat := [2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 3]
def baseStart_6945580 : Nat := 118140960795 + 6945580 * 2 ^ 59
def prefixEnd_6945580 : Nat := 4983230072969 + 3 ^ 40 * 6945580 * 2
def baseEnd_6945580 : Nat := 3566420964255040620007865

theorem tailTrace_6945580 : CollatzResearch.WordTrace tailWord_6945580 prefixEnd_6945580 3566420964255040620007865 := by
  unfold tailWord_6945580
  simp only [CollatzResearch.WordTrace]
  refine ⟨126663057088678672735029097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168884076118238230313372129 126663057088678672735029097)
  ·
    refine ⟨94997292816509004551271823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126663057088678672735029097 94997292816509004551271823)
    ·
      refine ⟨142495939224763506826907735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94997292816509004551271823 142495939224763506826907735)
      ·
        refine ⟨213743908837145260240361603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142495939224763506826907735 213743908837145260240361603)
        ·
          refine ⟨320615863255717890360542405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213743908837145260240361603 320615863255717890360542405)
          ·
            refine ⟨60115474360447104442601701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 320615863255717890360542405 60115474360447104442601701)
            ·
              refine ⟨11271651442583832082987819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60115474360447104442601701 11271651442583832082987819)
              ·
                refine ⟨16907477163875748124481729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271651442583832082987819 16907477163875748124481729)
                ·
                  refine ⟨12680607872906811093361297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16907477163875748124481729 12680607872906811093361297)
                  ·
                    refine ⟨9510455904680108320020973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12680607872906811093361297 9510455904680108320020973)
                    ·
                      refine ⟨3566420964255040620007865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510455904680108320020973 3566420964255040620007865)
                      ·
                        rfl

theorem cell23_6945580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 3].length) (baseStart_6945580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945580 prefixEnd_6945580 := by exact prefixLift 6945580
  have htrace : WordTrace (prefixWord ++ tailWord_6945580) baseStart_6945580 baseEnd_6945580 := by
    simpa [prefixWord, tailWord_6945580, baseEnd_6945580] using wordTrace_append hprefix tailTrace_6945580
  have hstable : (prefixWord ++ tailWord_6945580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945580).length < 2 ^ (prefixWord ++ tailWord_6945580).sum := by decide
  have hdescent : baseEnd_6945580 < baseStart_6945580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945637 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 2, 3, 2]
def baseStart_6945637 : Nat := 118140960795 + 6945637 * 2 ^ 59
def prefixEnd_6945637 : Nat := 4983230072969 + 3 ^ 40 * 6945637 * 2
def baseEnd_6945637 : Nat := 3566450232652346896995103

theorem tailTrace_6945637 : CollatzResearch.WordTrace tailWord_6945637 prefixEnd_6945637 3566450232652346896995103 := by
  unfold tailWord_6945637
  simp only [CollatzResearch.WordTrace]
  refine ⟨253328193138150844204883165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168885462092100562803255443 253328193138150844204883165)
  ·
    refine ⟨94998072426806566576831187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253328193138150844204883165 94998072426806566576831187)
    ·
      refine ⟨142497108640209849865246781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94998072426806566576831187 142497108640209849865246781)
      ·
        refine ⟨53436415740078693699467543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142497108640209849865246781 53436415740078693699467543)
        ·
          refine ⟨80154623610118040549201315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53436415740078693699467543 80154623610118040549201315)
          ·
            refine ⟨120231935415177060823801973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80154623610118040549201315 120231935415177060823801973)
            ·
              refine ⟨11271743945172849452231435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120231935415177060823801973 11271743945172849452231435)
              ·
                refine ⟨16907615917759274178347153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11271743945172849452231435 16907615917759274178347153)
                ·
                  refine ⟨12680711938319455633760365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16907615917759274178347153 12680711938319455633760365)
                  ·
                    refine ⟨4755266976869795862660137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12680711938319455633760365 4755266976869795862660137)
                    ·
                      refine ⟨3566450232652346896995103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755266976869795862660137 3566450232652346896995103)
                      ·
                        rfl

theorem cell23_6945637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_6945637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945637 prefixEnd_6945637 := by exact prefixLift 6945637
  have htrace : WordTrace (prefixWord ++ tailWord_6945637) baseStart_6945637 baseEnd_6945637 := by
    simpa [prefixWord, tailWord_6945637, baseEnd_6945637] using wordTrace_append hprefix tailTrace_6945637
  have hstable : (prefixWord ++ tailWord_6945637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945637).length < 2 ^ (prefixWord ++ tailWord_6945637).sum := by decide
  have hdescent : baseEnd_6945637 < baseStart_6945637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945643 : List Nat := [1, 1, 1, 1, 2, 2, 6, 2, 1, 6]
def baseStart_6945643 : Nat := 118140960795 + 6945643 * 2 ^ 59
def prefixEnd_6945643 : Nat := 4983230072969 + 3 ^ 40 * 6945643 * 2
def baseEnd_6945643 : Nat := 1188817771178757957840025

theorem tailTrace_6945643 : CollatzResearch.WordTrace tailWord_6945643 prefixEnd_6945643 1188817771178757957840025 := by
  unfold tailWord_6945643
  simp only [CollatzResearch.WordTrace]
  refine ⟨253328411976129107229601583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168885607984086071486401055 253328411976129107229601583)
  ·
    refine ⟨379992617964193660844402375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253328411976129107229601583 379992617964193660844402375)
    ·
      refine ⟨569988926946290491266603563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 379992617964193660844402375 569988926946290491266603563)
      ·
        refine ⟨854983390419435736899905345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 569988926946290491266603563 854983390419435736899905345)
        ·
          refine ⟨641237542814576802674929009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 854983390419435736899905345 641237542814576802674929009)
          ·
            refine ⟨480928157110932602006196757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641237542814576802674929009 480928157110932602006196757)
            ·
              refine ⟨22543507364574965719040473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 480928157110932602006196757 22543507364574965719040473)
              ·
                refine ⟨16907630523431224289280355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22543507364574965719040473 16907630523431224289280355)
                ·
                  refine ⟨25361445785146836433920533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16907630523431224289280355 25361445785146836433920533)
                  ·
                    refine ⟨1188817771178757957840025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25361445785146836433920533 1188817771178757957840025)
                    ·
                      rfl

theorem cell23_6945643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 1, 6].length) (baseStart_6945643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945643 prefixEnd_6945643 := by exact prefixLift 6945643
  have htrace : WordTrace (prefixWord ++ tailWord_6945643) baseStart_6945643 baseEnd_6945643 := by
    simpa [prefixWord, tailWord_6945643, baseEnd_6945643] using wordTrace_append hprefix tailTrace_6945643
  have hstable : (prefixWord ++ tailWord_6945643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945643).length < 2 ^ (prefixWord ++ tailWord_6945643).sum := by decide
  have hdescent : baseEnd_6945643 < baseStart_6945643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945644 : List Nat := [2, 2, 1, 1, 4, 1, 4, 3, 1, 1, 3]
def baseStart_6945644 : Nat := 118140960795 + 6945644 * 2 ^ 59
def prefixEnd_6945644 : Nat := 4983230072969 + 3 ^ 40 * 6945644 * 2
def baseEnd_6945644 : Nat := 3566453827016928369607571

theorem tailTrace_6945644 : CollatzResearch.WordTrace tailWord_6945644 prefixEnd_6945644 3566453827016928369607571 := by
  unfold tailWord_6945644
  simp only [CollatzResearch.WordTrace]
  refine ⟨126664224224562742200193993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168885632299416989600258657 126664224224562742200193993)
  ·
    refine ⟨94998168168422056650145495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126664224224562742200193993 94998168168422056650145495)
    ·
      refine ⟨142497252252633084975218243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94998168168422056650145495 142497252252633084975218243)
      ·
        refine ⟨213745878378949627462827365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142497252252633084975218243 213745878378949627462827365)
        ·
          refine ⟨40077352196053055149280131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213745878378949627462827365 40077352196053055149280131)
          ·
            refine ⟨60116028294079582723920197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40077352196053055149280131 60116028294079582723920197)
            ·
              refine ⟨11271755305139921760735037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60116028294079582723920197 11271755305139921760735037)
              ·
                refine ⟨4226908239427470660275639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11271755305139921760735037 4226908239427470660275639)
                ·
                  refine ⟨6340362359141205990413459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4226908239427470660275639 6340362359141205990413459)
                  ·
                    refine ⟨9510543538711808985620189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6340362359141205990413459 9510543538711808985620189)
                    ·
                      refine ⟨3566453827016928369607571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510543538711808985620189 3566453827016928369607571)
                      ·
                        rfl

theorem cell23_6945644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 3, 1, 1, 3].length) (baseStart_6945644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945644 prefixEnd_6945644 := by exact prefixLift 6945644
  have htrace : WordTrace (prefixWord ++ tailWord_6945644) baseStart_6945644 baseEnd_6945644 := by
    simpa [prefixWord, tailWord_6945644, baseEnd_6945644] using wordTrace_append hprefix tailTrace_6945644
  have hstable : (prefixWord ++ tailWord_6945644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945644).length < 2 ^ (prefixWord ++ tailWord_6945644).sum := by decide
  have hdescent : baseEnd_6945644 < baseStart_6945644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945663 : List Nat := [1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_6945663 : Nat := 118140960795 + 6945663 * 2 ^ 59
def prefixEnd_6945663 : Nat := 4983230072969 + 3 ^ 40 * 6945663 * 2
def baseEnd_6945663 : Nat := 3566463583149363795269983

theorem tailTrace_6945663 : CollatzResearch.WordTrace tailWord_6945663 prefixEnd_6945663 3566463583149363795269983 := by
  unfold tailWord_6945663
  simp only [CollatzResearch.WordTrace]
  refine ⟨253329141436056650645329643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168886094290704433763553095 253329141436056650645329643)
  ·
    refine ⟨379993712154084975967994465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253329141436056650645329643 379993712154084975967994465)
    ·
      refine ⟨284995284115563731975995849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 379993712154084975967994465 284995284115563731975995849)
      ·
        refine ⟨213746463086672798981996887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 284995284115563731975995849 213746463086672798981996887)
        ·
          refine ⟨320619694630009198472995331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213746463086672798981996887 320619694630009198472995331)
          ·
            refine ⟨480929541945013797709492997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320619694630009198472995331 480929541945013797709492997)
            ·
              refine ⟨90174289114690087070529937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 480929541945013797709492997 90174289114690087070529937)
              ·
                refine ⟨67630716836017565302897453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90174289114690087070529937 67630716836017565302897453)
                ·
                  refine ⟨25361518813506586988586545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67630716836017565302897453 25361518813506586988586545)
                  ·
                    refine ⟨19021139110129940241439909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25361518813506586988586545 19021139110129940241439909)
                    ·
                      refine ⟨3566463583149363795269983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19021139110129940241439909 3566463583149363795269983)
                      ·
                        rfl

theorem cell23_6945663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_6945663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945663 prefixEnd_6945663 := by exact prefixLift 6945663
  have htrace : WordTrace (prefixWord ++ tailWord_6945663) baseStart_6945663 baseEnd_6945663 := by
    simpa [prefixWord, tailWord_6945663, baseEnd_6945663] using wordTrace_append hprefix tailTrace_6945663
  have hstable : (prefixWord ++ tailWord_6945663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945663).length < 2 ^ (prefixWord ++ tailWord_6945663).sum := by decide
  have hdescent : baseEnd_6945663 < baseStart_6945663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945684 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 3, 2, 2]
def baseStart_6945684 : Nat := 118140960795 + 6945684 * 2 ^ 59
def prefixEnd_6945684 : Nat := 4983230072969 + 3 ^ 40 * 6945684 * 2
def baseEnd_6945684 : Nat := 3566474366243108213107387

theorem tailTrace_6945684 : CollatzResearch.WordTrace tailWord_6945684 prefixEnd_6945684 3566474366243108213107387 := by
  unfold tailWord_6945684
  simp only [CollatzResearch.WordTrace]
  refine ⟨126664953684490285615922053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168886604912653714154562737 126664953684490285615922053)
  ·
    refine ⟨23749678815841928552985385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126664953684490285615922053 23749678815841928552985385)
    ·
      refine ⟨17812259111881446414739039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23749678815841928552985385 17812259111881446414739039)
      ·
        refine ⟨26718388667822169622108559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17812259111881446414739039 26718388667822169622108559)
        ·
          refine ⟨40077583001733254433162839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26718388667822169622108559 40077583001733254433162839)
          ·
            refine ⟨60116374502599881649744259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40077583001733254433162839 60116374502599881649744259)
            ·
              refine ⟨90174561753899822474616389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60116374502599881649744259 90174561753899822474616389)
              ·
                refine ⟨16907730328856216713990573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90174561753899822474616389 16907730328856216713990573)
                ·
                  refine ⟨6340398873321081267746465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16907730328856216713990573 6340398873321081267746465)
                  ·
                    refine ⟨4755299154990810950809849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6340398873321081267746465 4755299154990810950809849)
                    ·
                      refine ⟨3566474366243108213107387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755299154990810950809849 3566474366243108213107387)
                      ·
                        rfl

theorem cell23_6945684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_6945684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945684 prefixEnd_6945684 := by exact prefixLift 6945684
  have htrace : WordTrace (prefixWord ++ tailWord_6945684) baseStart_6945684 baseEnd_6945684 := by
    simpa [prefixWord, tailWord_6945684, baseEnd_6945684] using wordTrace_append hprefix tailTrace_6945684
  have hstable : (prefixWord ++ tailWord_6945684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945684).length < 2 ^ (prefixWord ++ tailWord_6945684).sum := by decide
  have hdescent : baseEnd_6945684 < baseStart_6945684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945687 : List Nat := [1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 3]
def baseStart_6945687 : Nat := 118140960795 + 6945687 * 2 ^ 59
def prefixEnd_6945687 : Nat := 4983230072969 + 3 ^ 40 * 6945687 * 2
def baseEnd_6945687 : Nat := 3566475906685071701369873

theorem tailTrace_6945687 : CollatzResearch.WordTrace tailWord_6945687 prefixEnd_6945687 3566475906685071701369873 := by
  unfold tailWord_6945687
  simp only [CollatzResearch.WordTrace]
  refine ⟨253330016787969702744203315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168886677858646468496135543 253330016787969702744203315)
  ·
    refine ⟨379995025181954554116304973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253330016787969702744203315 379995025181954554116304973)
    ·
      refine ⟨142498134443232957793614365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 379995025181954554116304973 142498134443232957793614365)
      ·
        refine ⟨53436800416212359172605387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142498134443232957793614365 53436800416212359172605387)
        ·
          refine ⟨80155200624318538758908081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53436800416212359172605387 80155200624318538758908081)
          ·
            refine ⟨60116400468238904069181061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80155200624318538758908081 60116400468238904069181061)
            ·
              refine ⟨11271825087794794512971449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60116400468238904069181061 11271825087794794512971449)
              ·
                refine ⟨8453868815846095884728587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11271825087794794512971449 8453868815846095884728587)
                ·
                  refine ⟨12680803223769143827092881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8453868815846095884728587 12680803223769143827092881)
                  ·
                    refine ⟨9510602417826857870319661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12680803223769143827092881 9510602417826857870319661)
                    ·
                      refine ⟨3566475906685071701369873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510602417826857870319661 3566475906685071701369873)
                      ·
                        rfl

theorem cell23_6945687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_6945687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945687 prefixEnd_6945687 := by exact prefixLift 6945687
  have htrace : WordTrace (prefixWord ++ tailWord_6945687) baseStart_6945687 baseEnd_6945687 := by
    simpa [prefixWord, tailWord_6945687, baseEnd_6945687] using wordTrace_append hprefix tailTrace_6945687
  have hstable : (prefixWord ++ tailWord_6945687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945687).length < 2 ^ (prefixWord ++ tailWord_6945687).sum := by decide
  have hdescent : baseEnd_6945687 < baseStart_6945687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945690 : List Nat := [3, 1, 1, 4, 3, 1, 1, 9]
def baseStart_6945690 : Nat := 118140960795 + 6945690 * 2 ^ 59
def prefixEnd_6945690 : Nat := 4983230072969 + 3 ^ 40 * 6945690 * 2
def baseEnd_6945690 : Nat := 132091757301001303319717

theorem tailTrace_6945690 : CollatzResearch.WordTrace tailWord_6945690 prefixEnd_6945690 132091757301001303319717 := by
  unfold tailWord_6945690
  simp only [CollatzResearch.WordTrace]
  refine ⟨63332531551739708564140631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168886750804639222837708349 63332531551739708564140631)
  ·
    refine ⟨94998797327609562846210947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63332531551739708564140631 94998797327609562846210947)
    ·
      refine ⟨142498195991414344269316421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94998797327609562846210947 142498195991414344269316421)
      ·
        refine ⟨26718411748390189550496829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142498195991414344269316421 26718411748390189550496829)
        ·
          refine ⟨10019404405646321081436311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26718411748390189550496829 10019404405646321081436311)
          ·
            refine ⟨15029106608469481622154467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10019404405646321081436311 15029106608469481622154467)
            ·
              refine ⟨22543659912704222433231701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15029106608469481622154467 22543659912704222433231701)
              ·
                refine ⟨132091757301001303319717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22543659912704222433231701 132091757301001303319717)
                ·
                  rfl

theorem cell23_6945690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_6945690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945690 prefixEnd_6945690 := by exact prefixLift 6945690
  have htrace : WordTrace (prefixWord ++ tailWord_6945690) baseStart_6945690 baseEnd_6945690 := by
    simpa [prefixWord, tailWord_6945690, baseEnd_6945690] using wordTrace_append hprefix tailTrace_6945690
  have hstable : (prefixWord ++ tailWord_6945690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945690).length < 2 ^ (prefixWord ++ tailWord_6945690).sum := by decide
  have hdescent : baseEnd_6945690 < baseStart_6945690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945700 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 3, 3, 3]
def baseStart_6945700 : Nat := 118140960795 + 6945700 * 2 ^ 59
def prefixEnd_6945700 : Nat := 4983230072969 + 3 ^ 40 * 6945700 * 2
def baseEnd_6945700 : Nat := 3566482581933580150507313

theorem tailTrace_6945700 : CollatzResearch.WordTrace tailWord_6945700 prefixEnd_6945700 3566482581933580150507313 := by
  unfold tailWord_6945700
  simp only [CollatzResearch.WordTrace]
  refine ⟨126665245468461302982213277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168886993957948403976284369 126665245468461302982213277)
  ·
    refine ⟨47499467050672988618329979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126665245468461302982213277 47499467050672988618329979)
    ·
      refine ⟨71249200576009482927494969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47499467050672988618329979 71249200576009482927494969)
      ·
        refine ⟨53436900432007112195621227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71249200576009482927494969 53436900432007112195621227)
        ·
          refine ⟨80155350648010668293431841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53436900432007112195621227 80155350648010668293431841)
          ·
            refine ⟨60116512986008001220073881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80155350648010668293431841 60116512986008001220073881)
            ·
              refine ⟨45087384739506000915055411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60116512986008001220073881 45087384739506000915055411)
              ·
                refine ⟨67631077109259001372583117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45087384739506000915055411 67631077109259001372583117)
                ·
                  refine ⟨25361653915972125514718669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67631077109259001372583117 25361653915972125514718669)
                  ·
                    refine ⟨9510620218489547068019501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25361653915972125514718669 9510620218489547068019501)
                    ·
                      refine ⟨3566482581933580150507313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510620218489547068019501 3566482581933580150507313)
                      ·
                        rfl

theorem cell23_6945700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_6945700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945700 prefixEnd_6945700 := by exact prefixLift 6945700
  have htrace : WordTrace (prefixWord ++ tailWord_6945700) baseStart_6945700 baseEnd_6945700 := by
    simpa [prefixWord, tailWord_6945700, baseEnd_6945700] using wordTrace_append hprefix tailTrace_6945700
  have hstable : (prefixWord ++ tailWord_6945700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945700).length < 2 ^ (prefixWord ++ tailWord_6945700).sum := by decide
  have hdescent : baseEnd_6945700 < baseStart_6945700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945717 : List Nat := [1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_6945717 : Nat := 118140960795 + 6945717 * 2 ^ 59
def prefixEnd_6945717 : Nat := 4983230072969 + 3 ^ 40 * 6945717 * 2
def baseEnd_6945717 : Nat := 3566491311104706583994735

theorem tailTrace_6945717 : CollatzResearch.WordTrace tailWord_6945717 prefixEnd_6945717 3566491311104706583994735 := by
  unfold tailWord_6945717
  simp only [CollatzResearch.WordTrace]
  refine ⟨253331110977861017867795405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168887407318574011911863603 253331110977861017867795405)
  ·
    refine ⟨94999166616697881700423277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253331110977861017867795405 94999166616697881700423277)
    ·
      refine ⟨35624687481261705637658729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94999166616697881700423277 35624687481261705637658729)
      ·
        refine ⟨26718515610946279228244047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35624687481261705637658729 26718515610946279228244047)
        ·
          refine ⟨40077773416419418842366071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26718515610946279228244047 40077773416419418842366071)
          ·
            refine ⟨60116660124629128263549107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40077773416419418842366071 60116660124629128263549107)
            ·
              refine ⟨90174990186943692395323661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60116660124629128263549107 90174990186943692395323661)
              ·
                refine ⟨33815621320103884648246373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90174990186943692395323661 33815621320103884648246373)
                ·
                  refine ⟨6340428997519478371546195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33815621320103884648246373 6340428997519478371546195)
                  ·
                    refine ⟨9510643496279217557319293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6340428997519478371546195 9510643496279217557319293)
                    ·
                      refine ⟨3566491311104706583994735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510643496279217557319293 3566491311104706583994735)
                      ·
                        rfl

theorem cell23_6945717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_6945717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945717 prefixEnd_6945717 := by exact prefixLift 6945717
  have htrace : WordTrace (prefixWord ++ tailWord_6945717) baseStart_6945717 baseEnd_6945717 := by
    simpa [prefixWord, tailWord_6945717, baseEnd_6945717] using wordTrace_append hprefix tailTrace_6945717
  have hstable : (prefixWord ++ tailWord_6945717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945717).length < 2 ^ (prefixWord ++ tailWord_6945717).sum := by decide
  have hdescent : baseEnd_6945717 < baseStart_6945717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945733 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 6, 6]
def baseStart_6945733 : Nat := 118140960795 + 6945733 * 2 ^ 59
def prefixEnd_6945733 : Nat := 4983230072969 + 3 ^ 40 * 6945733 * 2
def baseEnd_6945733 : Nat := 1188833175598392840464887

theorem tailTrace_6945733 : CollatzResearch.WordTrace tailWord_6945733 prefixEnd_6945733 1188833175598392840464887 := by
  unfold tailWord_6945733
  simp only [CollatzResearch.WordTrace]
  refine ⟨253331694545803052600377853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168887796363868701733585235 253331694545803052600377853)
  ·
    refine ⟨94999385454676144725141695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253331694545803052600377853 94999385454676144725141695)
    ·
      refine ⟨142499078182014217087712543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94999385454676144725141695 142499078182014217087712543)
      ·
        refine ⟨213748617273021325631568815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142499078182014217087712543 213748617273021325631568815)
        ·
          refine ⟨320622925909531988447353223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213748617273021325631568815 320622925909531988447353223)
          ·
            refine ⟨480934388864297982671029835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320622925909531988447353223 480934388864297982671029835)
            ·
              refine ⟨721401583296446974006544753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480934388864297982671029835 721401583296446974006544753)
              ·
                refine ⟨541051187472335230504908565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 721401583296446974006544753 541051187472335230504908565)
                ·
                  refine ⟨25361774412765713929917589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 541051187472335230504908565 25361774412765713929917589)
                  ·
                    refine ⟨1188833175598392840464887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25361774412765713929917589 1188833175598392840464887)
                    ·
                      rfl

theorem cell23_6945733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 6].length) (baseStart_6945733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945733 prefixEnd_6945733 := by exact prefixLift 6945733
  have htrace : WordTrace (prefixWord ++ tailWord_6945733) baseStart_6945733 baseEnd_6945733 := by
    simpa [prefixWord, tailWord_6945733, baseEnd_6945733] using wordTrace_append hprefix tailTrace_6945733
  have hstable : (prefixWord ++ tailWord_6945733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945733).length < 2 ^ (prefixWord ++ tailWord_6945733).sum := by decide
  have hdescent : baseEnd_6945733 < baseStart_6945733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945870 : List Nat := [4, 1, 1, 1, 1, 3, 1, 1, 10]
def baseStart_6945870 : Nat := 118140960795 + 6945870 * 2 ^ 59
def prefixEnd_6945870 : Nat := 4983230072969 + 3 ^ 40 * 6945870 * 2
def baseEnd_6945870 : Nat := 396285541516093831709059

theorem tailTrace_6945870 : CollatzResearch.WordTrace tailWord_6945870 prefixEnd_6945870 396285541516093831709059 := by
  unfold tailWord_6945870
  simp only [CollatzResearch.WordTrace]
  refine ⟨31667086418288340624764383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168891127564204483332076709 31667086418288340624764383)
  ·
    refine ⟨47500629627432510937146575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31667086418288340624764383 47500629627432510937146575)
    ·
      refine ⟨71250944441148766405719863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47500629627432510937146575 71250944441148766405719863)
      ·
        refine ⟨106876416661723149608579795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71250944441148766405719863 106876416661723149608579795)
        ·
          refine ⟨160314624992584724412869693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106876416661723149608579795 160314624992584724412869693)
          ·
            refine ⟨60117984372219271654826135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160314624992584724412869693 60117984372219271654826135)
            ·
              refine ⟨90176976558328907482239203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60117984372219271654826135 90176976558328907482239203)
              ·
                refine ⟨135265464837493361223358805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90176976558328907482239203 135265464837493361223358805)
                ·
                  refine ⟨396285541516093831709059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 135265464837493361223358805 396285541516093831709059)
                  ·
                    rfl

theorem cell23_6945870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_6945870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945870 prefixEnd_6945870 := by exact prefixLift 6945870
  have htrace : WordTrace (prefixWord ++ tailWord_6945870) baseStart_6945870 baseEnd_6945870 := by
    simpa [prefixWord, tailWord_6945870, baseEnd_6945870] using wordTrace_append hprefix tailTrace_6945870
  have hstable : (prefixWord ++ tailWord_6945870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945870).length < 2 ^ (prefixWord ++ tailWord_6945870).sum := by decide
  have hdescent : baseEnd_6945870 < baseStart_6945870 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945884 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_6945884 : Nat := 118140960795 + 6945884 * 2 ^ 59
def prefixEnd_6945884 : Nat := 4983230072969 + 3 ^ 40 * 6945884 * 2
def baseEnd_6945884 : Nat := 3566577062374007430606467

theorem tailTrace_6945884 : CollatzResearch.WordTrace tailWord_6945884 prefixEnd_6945884 3566577062374007430606467 := by
  unfold tailWord_6945884
  simp only [CollatzResearch.WordTrace]
  refine ⟨126668600984128002694562353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168891467978837336926083137 126668600984128002694562353)
  ·
    refine ⟨95001450738096002020921765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126668600984128002694562353 95001450738096002020921765)
    ·
      refine ⟨17812772013393000378922831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 95001450738096002020921765 17812772013393000378922831)
      ·
        refine ⟨26719158020089500568384247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17812772013393000378922831 26719158020089500568384247)
        ·
          refine ⟨40078737030134250852576371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26719158020089500568384247 40078737030134250852576371)
          ·
            refine ⟨60118105545201376278864557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40078737030134250852576371 60118105545201376278864557)
            ·
              refine ⟨22544289579450516104574209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60118105545201376278864557 22544289579450516104574209)
              ·
                refine ⟨16908217184587887078430657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22544289579450516104574209 16908217184587887078430657)
                ·
                  refine ⟨12681162888440915308822993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16908217184587887078430657 12681162888440915308822993)
                  ·
                    refine ⟨9510872166330686481617245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12681162888440915308822993 9510872166330686481617245)
                    ·
                      refine ⟨3566577062374007430606467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510872166330686481617245 3566577062374007430606467)
                      ·
                        rfl

theorem cell23_6945884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_6945884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945884 prefixEnd_6945884 := by exact prefixLift 6945884
  have htrace : WordTrace (prefixWord ++ tailWord_6945884) baseStart_6945884 baseEnd_6945884 := by
    simpa [prefixWord, tailWord_6945884, baseEnd_6945884] using wordTrace_append hprefix tailTrace_6945884
  have hstable : (prefixWord ++ tailWord_6945884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945884).length < 2 ^ (prefixWord ++ tailWord_6945884).sum := by decide
  have hdescent : baseEnd_6945884 < baseStart_6945884 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945917 : List Nat := [1, 4, 1, 1, 3, 1, 3, 1, 3, 5]
def baseStart_6945917 : Nat := 118140960795 + 6945917 * 2 ^ 59
def prefixEnd_6945917 : Nat := 4983230072969 + 3 ^ 40 * 6945917 * 2
def baseEnd_6945917 : Nat := 1188864669078535267164605

theorem tailTrace_6945917 : CollatzResearch.WordTrace tailWord_6945917 prefixEnd_6945917 1188864669078535267164605 := by
  unfold tailWord_6945917
  simp only [CollatzResearch.WordTrace]
  refine ⟨253338405577136452025076005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168892270384757634683384003 253338405577136452025076005)
  ·
    refine ⟨47500951045713084754701751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253338405577136452025076005 47500951045713084754701751)
    ·
      refine ⟨71251426568569627132052627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47500951045713084754701751 71251426568569627132052627)
      ·
        refine ⟨106877139852854440698078941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71251426568569627132052627 106877139852854440698078941)
        ·
          refine ⟨40078927444820415261779603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106877139852854440698078941 40078927444820415261779603)
          ·
            refine ⟨60118391167230622892669405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40078927444820415261779603 60118391167230622892669405)
            ·
              refine ⟨22544396687711483584751027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60118391167230622892669405 22544396687711483584751027)
              ·
                refine ⟨33816595031567225377126541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22544396687711483584751027 33816595031567225377126541)
                ·
                  refine ⟨12681223136837709516422453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33816595031567225377126541 12681223136837709516422453)
                  ·
                    refine ⟨1188864669078535267164605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12681223136837709516422453 1188864669078535267164605)
                    ·
                      rfl

theorem cell23_6945917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_6945917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945917 prefixEnd_6945917 := by exact prefixLift 6945917
  have htrace : WordTrace (prefixWord ++ tailWord_6945917) baseStart_6945917 baseEnd_6945917 := by
    simpa [prefixWord, tailWord_6945917, baseEnd_6945917] using wordTrace_append hprefix tailTrace_6945917
  have hstable : (prefixWord ++ tailWord_6945917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945917).length < 2 ^ (prefixWord ++ tailWord_6945917).sum := by decide
  have hdescent : baseEnd_6945917 < baseStart_6945917 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945948 : List Nat := [2, 2, 3, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_6945948 : Nat := 118140960795 + 6945948 * 2 ^ 59
def prefixEnd_6945948 : Nat := 4983230072969 + 3 ^ 40 * 6945948 * 2
def baseEnd_6945948 : Nat := 3566609925135895180206173

theorem tailTrace_6945948 : CollatzResearch.WordTrace tailWord_6945948 prefixEnd_6945948 3566609925135895180206173 := by
  unfold tailWord_6945948
  simp only [CollatzResearch.WordTrace]
  refine ⟨126669768120012072159727249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168893024160016096212969665 126669768120012072159727249)
  ·
    refine ⟨95002326090009054119795437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126669768120012072159727249 95002326090009054119795437)
    ·
      refine ⟨35625872283753395294923289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95002326090009054119795437 35625872283753395294923289)
      ·
        refine ⟨26719404212815046471192467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35625872283753395294923289 26719404212815046471192467)
        ·
          refine ⟨40079106319222569706788701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26719404212815046471192467 40079106319222569706788701)
          ·
            refine ⟨15029664869708463640045763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40079106319222569706788701 15029664869708463640045763)
            ·
              refine ⟨22544497304562695460068645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15029664869708463640045763 22544497304562695460068645)
              ·
                refine ⟨4227093244605505398762871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22544497304562695460068645 4227093244605505398762871)
                ·
                  refine ⟨6340639866908258098144307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227093244605505398762871 6340639866908258098144307)
                  ·
                    refine ⟨9510959800362387147216461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6340639866908258098144307 9510959800362387147216461)
                    ·
                      refine ⟨3566609925135895180206173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9510959800362387147216461 3566609925135895180206173)
                      ·
                        rfl

theorem cell23_6945948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_6945948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945948 prefixEnd_6945948 := by exact prefixLift 6945948
  have htrace : WordTrace (prefixWord ++ tailWord_6945948) baseStart_6945948 baseEnd_6945948 := by
    simpa [prefixWord, tailWord_6945948, baseEnd_6945948] using wordTrace_append hprefix tailTrace_6945948
  have hstable : (prefixWord ++ tailWord_6945948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945948).length < 2 ^ (prefixWord ++ tailWord_6945948).sum := by decide
  have hdescent : baseEnd_6945948 < baseStart_6945948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945967 : List Nat := [1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_6945967 : Nat := 118140960795 + 6945967 * 2 ^ 59
def prefixEnd_6945967 : Nat := 4983230072969 + 3 ^ 40 * 6945967 * 2
def baseEnd_6945967 : Nat := 3566619681268330605868585

theorem tailTrace_6945967 : CollatzResearch.WordTrace tailWord_6945967 prefixEnd_6945967 3566619681268330605868585 := by
  unfold tailWord_6945967
  simp only [CollatzResearch.WordTrace]
  refine ⟨253340229226955310564396155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168893486151303540376264103 253340229226955310564396155)
  ·
    refine ⟨380010343840432965846594233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253340229226955310564396155 380010343840432965846594233)
    ·
      refine ⟨285007757880324724384945675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380010343840432965846594233 285007757880324724384945675)
      ·
        refine ⟨427511636820487086577418513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285007757880324724384945675 427511636820487086577418513)
        ·
          refine ⟨320633727615365314933063885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427511636820487086577418513 320633727615365314933063885)
          ·
            refine ⟨120237647855761993099898957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320633727615365314933063885 120237647855761993099898957)
            ·
              refine ⟨45089117945910747412462109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120237647855761993099898957 45089117945910747412462109)
              ·
                refine ⟨16908419229716530279673291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45089117945910747412462109 16908419229716530279673291)
                ·
                  refine ⟨25362628844574795419509937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16908419229716530279673291 25362628844574795419509937)
                  ·
                    refine ⟨19021971633431096564632453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25362628844574795419509937 19021971633431096564632453)
                    ·
                      refine ⟨3566619681268330605868585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19021971633431096564632453 3566619681268330605868585)
                      ·
                        rfl

theorem cell23_6945967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_6945967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945967 prefixEnd_6945967 := by exact prefixLift 6945967
  have htrace : WordTrace (prefixWord ++ tailWord_6945967) baseStart_6945967 baseEnd_6945967 := by
    simpa [prefixWord, tailWord_6945967, baseEnd_6945967] using wordTrace_append hprefix tailTrace_6945967
  have hstable : (prefixWord ++ tailWord_6945967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945967).length < 2 ^ (prefixWord ++ tailWord_6945967).sum := by decide
  have hdescent : baseEnd_6945967 < baseStart_6945967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945987 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 3]
def baseStart_6945987 : Nat := 118140960795 + 6945987 * 2 ^ 59
def prefixEnd_6945987 : Nat := 4983230072969 + 3 ^ 40 * 6945987 * 2
def baseEnd_6945987 : Nat := 3566629950881420527618493

theorem tailTrace_6945987 : CollatzResearch.WordTrace tailWord_6945987 prefixEnd_6945987 3566629950881420527618493 := by
  unfold tailWord_6945987
  simp only [CollatzResearch.WordTrace]
  refine ⟨253340958686882853980124215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168893972457921902653416143 253340958686882853980124215)
  ·
    refine ⟨380011438030324280970186323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253340958686882853980124215 380011438030324280970186323)
    ·
      refine ⟨570017157045486421455279485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380011438030324280970186323 570017157045486421455279485)
      ·
        refine ⟨213756433892057408045729807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 570017157045486421455279485 213756433892057408045729807)
        ·
          refine ⟨320634650838086112068594711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213756433892057408045729807 320634650838086112068594711)
          ·
            refine ⟨480951976257129168102892067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320634650838086112068594711 480951976257129168102892067)
            ·
              refine ⟨721427964385693752154338101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 480951976257129168102892067 721427964385693752154338101)
              ·
                refine ⟨67633871661158789264469197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 721427964385693752154338101 67633871661158789264469197)
                ·
                  refine ⟨25362701872934545974175949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67633871661158789264469197 25362701872934545974175949)
                  ·
                    refine ⟨9511013202350454740315981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25362701872934545974175949 9511013202350454740315981)
                    ·
                      refine ⟨3566629950881420527618493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9511013202350454740315981 3566629950881420527618493)
                      ·
                        rfl

theorem cell23_6945987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_6945987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945987 prefixEnd_6945987 := by exact prefixLift 6945987
  have htrace : WordTrace (prefixWord ++ tailWord_6945987) baseStart_6945987 baseEnd_6945987 := by
    simpa [prefixWord, tailWord_6945987, baseEnd_6945987] using wordTrace_append hprefix tailTrace_6945987
  have hstable : (prefixWord ++ tailWord_6945987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945987).length < 2 ^ (prefixWord ++ tailWord_6945987).sum := by decide
  have hdescent : baseEnd_6945987 < baseStart_6945987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6945998 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_6945998 : Nat := 118140960795 + 6945998 * 2 ^ 59
def prefixEnd_6945998 : Nat := 4983230072969 + 3 ^ 40 * 6945998 * 2
def baseEnd_6945998 : Nat := 1188878533056206661526981

theorem tailTrace_6945998 : CollatzResearch.WordTrace tailWord_6945998 prefixEnd_6945998 1188878533056206661526981 := by
  unfold tailWord_6945998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31667669986230375357346831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168894239926562001905849765 31667669986230375357346831)
  ·
    refine ⟨47501504979345563036020247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31667669986230375357346831 47501504979345563036020247)
    ·
      refine ⟨71252257469018344554030371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47501504979345563036020247 71252257469018344554030371)
      ·
        refine ⟨106878386203527516831045557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71252257469018344554030371 106878386203527516831045557)
        ·
          refine ⟨10019848706580704702910521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106878386203527516831045557 10019848706580704702910521)
          ·
            refine ⟨7514886529935528527182891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10019848706580704702910521 7514886529935528527182891)
            ·
              refine ⟨11272329794903292790774337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514886529935528527182891 11272329794903292790774337)
              ·
                refine ⟨8454247346177469593080753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11272329794903292790774337 8454247346177469593080753)
                ·
                  refine ⟨6340685509633102194810565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8454247346177469593080753 6340685509633102194810565)
                  ·
                    refine ⟨1188878533056206661526981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6340685509633102194810565 1188878533056206661526981)
                    ·
                      rfl

theorem cell23_6945998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_6945998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6945998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6945998 prefixEnd_6945998 := by exact prefixLift 6945998
  have htrace : WordTrace (prefixWord ++ tailWord_6945998) baseStart_6945998 baseEnd_6945998 := by
    simpa [prefixWord, tailWord_6945998, baseEnd_6945998] using wordTrace_append hprefix tailTrace_6945998
  have hstable : (prefixWord ++ tailWord_6945998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6945998).length < 2 ^ (prefixWord ++ tailWord_6945998).sum := by decide
  have hdescent : baseEnd_6945998 < baseStart_6945998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6945998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946005 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_6946005 : Nat := 118140960795 + 6946005 * 2 ^ 59
def prefixEnd_6946005 : Nat := 4983230072969 + 3 ^ 40 * 6946005 * 2
def baseEnd_6946005 : Nat := 3566639193533201457193411

theorem tailTrace_6946005 : CollatzResearch.WordTrace tailWord_6946005 prefixEnd_6946005 3566639193533201457193411 := by
  unfold tailWord_6946005
  simp only [CollatzResearch.WordTrace]
  refine ⟨253341615200817643054279469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168894410133878428702852979 253341615200817643054279469)
  ·
    refine ⟨95003105700306616145354801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253341615200817643054279469 95003105700306616145354801)
    ·
      refine ⟨71252329275229962109016101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95003105700306616145354801 71252329275229962109016101)
      ·
        refine ⟨13359811739105617895440519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71252329275229962109016101 13359811739105617895440519)
        ·
          refine ⟨20039717608658426843160779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13359811739105617895440519 20039717608658426843160779)
          ·
            refine ⟨30059576412987640264741169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20039717608658426843160779 30059576412987640264741169)
            ·
              refine ⟨22544682309740730198555877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30059576412987640264741169 22544682309740730198555877)
              ·
                refine ⟨4227127933076386912229227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22544682309740730198555877 4227127933076386912229227)
                ·
                  refine ⟨6340691899614580368343841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227127933076386912229227 6340691899614580368343841)
                  ·
                    refine ⟨4755518924710935276257881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6340691899614580368343841 4755518924710935276257881)
                    ·
                      refine ⟨3566639193533201457193411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755518924710935276257881 3566639193533201457193411)
                      ·
                        rfl

theorem cell23_6946005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_6946005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946005 prefixEnd_6946005 := by exact prefixLift 6946005
  have htrace : WordTrace (prefixWord ++ tailWord_6946005) baseStart_6946005 baseEnd_6946005 := by
    simpa [prefixWord, tailWord_6946005, baseEnd_6946005] using wordTrace_append hprefix tailTrace_6946005
  have hstable : (prefixWord ++ tailWord_6946005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946005).length < 2 ^ (prefixWord ++ tailWord_6946005).sum := by decide
  have hdescent : baseEnd_6946005 < baseStart_6946005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946047 : List Nat := [1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_6946047 : Nat := 118140960795 + 6946047 * 2 ^ 59
def prefixEnd_6946047 : Nat := 4983230072969 + 3 ^ 40 * 6946047 * 2
def baseEnd_6946047 : Nat := 3566660759720690292868217

theorem tailTrace_6946047 : CollatzResearch.WordTrace tailWord_6946047 prefixEnd_6946047 3566660759720690292868217 := by
  unfold tailWord_6946047
  simp only [CollatzResearch.WordTrace]
  refine ⟨253343147066665484227308395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168895431377776989484872263 253343147066665484227308395)
  ·
    refine ⟨380014720599998226340962593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253343147066665484227308395 380014720599998226340962593)
    ·
      refine ⟨285011040449998669755721945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380014720599998226340962593 285011040449998669755721945)
      ·
        refine ⟨213758280337499002316791459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285011040449998669755721945 213758280337499002316791459)
        ·
          refine ⟨320637420506248503475187189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213758280337499002316791459 320637420506248503475187189)
          ·
            refine ⟨30059758172460797200798799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320637420506248503475187189 30059758172460797200798799)
            ·
              refine ⟨45089637258691195801198199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30059758172460797200798799 45089637258691195801198199)
              ·
                refine ⟨67634455888036793701797299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45089637258691195801198199 67634455888036793701797299)
                ·
                  refine ⟨101451683832055190552695949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67634455888036793701797299 101451683832055190552695949)
                  ·
                    refine ⟨38044381437020696457260981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101451683832055190552695949 38044381437020696457260981)
                    ·
                      refine ⟨3566660759720690292868217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38044381437020696457260981 3566660759720690292868217)
                      ·
                        rfl

theorem cell23_6946047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_6946047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946047 prefixEnd_6946047 := by exact prefixLift 6946047
  have htrace : WordTrace (prefixWord ++ tailWord_6946047) baseStart_6946047 baseEnd_6946047 := by
    simpa [prefixWord, tailWord_6946047, baseEnd_6946047] using wordTrace_append hprefix tailTrace_6946047
  have hstable : (prefixWord ++ tailWord_6946047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946047).length < 2 ^ (prefixWord ++ tailWord_6946047).sum := by decide
  have hdescent : baseEnd_6946047 < baseStart_6946047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946082 : List Nat := [3, 3, 1, 1, 5, 1, 1, 2, 1, 3, 2]
def baseStart_6946082 : Nat := 118140960795 + 6946082 * 2 ^ 59
def prefixEnd_6946082 : Nat := 4983230072969 + 3 ^ 40 * 6946082 * 2
def baseEnd_6946082 : Nat := 3566678731543597655930557

theorem tailTrace_6946082 : CollatzResearch.WordTrace tailWord_6946082 prefixEnd_6946082 3566678731543597655930557 := by
  unfold tailWord_6946082
  simp only [CollatzResearch.WordTrace]
  refine ⟨63336105905384671301208125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168896282414359123469888333 63336105905384671301208125)
  ·
    refine ⟨23751039714519251737953047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63336105905384671301208125 23751039714519251737953047)
    ·
      refine ⟨35626559571778877606929571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23751039714519251737953047 35626559571778877606929571)
      ·
        refine ⟨53439839357668316410394357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35626559571778877606929571 53439839357668316410394357)
        ·
          refine ⟨5009984939781404663474471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 53439839357668316410394357 5009984939781404663474471)
          ·
            refine ⟨7514977409672106995211707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5009984939781404663474471 7514977409672106995211707)
            ·
              refine ⟨11272466114508160492817561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7514977409672106995211707 11272466114508160492817561)
              ·
                refine ⟨8454349585881120369613171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11272466114508160492817561 8454349585881120369613171)
                ·
                  refine ⟨12681524378821680554419757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8454349585881120369613171 12681524378821680554419757)
                  ·
                    refine ⟨4755571642058130207907409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12681524378821680554419757 4755571642058130207907409)
                    ·
                      refine ⟨3566678731543597655930557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755571642058130207907409 3566678731543597655930557)
                      ·
                        rfl

theorem cell23_6946082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_6946082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946082 prefixEnd_6946082 := by exact prefixLift 6946082
  have htrace : WordTrace (prefixWord ++ tailWord_6946082) baseStart_6946082 baseEnd_6946082 := by
    simpa [prefixWord, tailWord_6946082, baseEnd_6946082] using wordTrace_append hprefix tailTrace_6946082
  have hstable : (prefixWord ++ tailWord_6946082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946082).length < 2 ^ (prefixWord ++ tailWord_6946082).sum := by decide
  have hdescent : baseEnd_6946082 < baseStart_6946082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946124 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_6946124 : Nat := 118140960795 + 6946124 * 2 ^ 59
def prefixEnd_6946124 : Nat := 4983230072969 + 3 ^ 40 * 6946124 * 2
def baseEnd_6946124 : Nat := 3566700297731086491605363

theorem tailTrace_6946124 : CollatzResearch.WordTrace tailWord_6946124 prefixEnd_6946124 3566700297731086491605363 := by
  unfold tailWord_6946124
  simp only [CollatzResearch.WordTrace]
  refine ⟨126672977743693263188930713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168897303658257684251907617 126672977743693263188930713)
  ·
    refine ⟨95004733307769947391698035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126672977743693263188930713 95004733307769947391698035)
    ·
      refine ⟨142507099961654921087547053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95004733307769947391698035 142507099961654921087547053)
      ·
        refine ⟨53440162485620595407830145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142507099961654921087547053 53440162485620595407830145)
        ·
          refine ⟨40080121864215446555872609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53440162485620595407830145 40080121864215446555872609)
          ·
            refine ⟨30060091398161584916904457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40080121864215446555872609 30060091398161584916904457)
            ·
              refine ⟨22545068548621188687678343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30060091398161584916904457 22545068548621188687678343)
              ·
                refine ⟨33817602822931783031517515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22545068548621188687678343 33817602822931783031517515)
                ·
                  refine ⟨50726404234397674547276273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33817602822931783031517515 50726404234397674547276273)
                  ·
                    refine ⟨38044803175798255910457205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50726404234397674547276273 38044803175798255910457205)
                    ·
                      refine ⟨3566700297731086491605363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38044803175798255910457205 3566700297731086491605363)
                      ·
                        rfl

theorem cell23_6946124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_6946124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946124 prefixEnd_6946124 := by exact prefixLift 6946124
  have htrace : WordTrace (prefixWord ++ tailWord_6946124) baseStart_6946124 baseEnd_6946124 := by
    simpa [prefixWord, tailWord_6946124, baseEnd_6946124] using wordTrace_append hprefix tailTrace_6946124
  have hstable : (prefixWord ++ tailWord_6946124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946124).length < 2 ^ (prefixWord ++ tailWord_6946124).sum := by decide
  have hdescent : baseEnd_6946124 < baseStart_6946124 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946151 : List Nat := [1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_6946151 : Nat := 118140960795 + 6946151 * 2 ^ 59
def prefixEnd_6946151 : Nat := 4983230072969 + 3 ^ 40 * 6946151 * 2
def baseEnd_6946151 : Nat := 3566714161708757885967739

theorem tailTrace_6946151 : CollatzResearch.WordTrace tailWord_6946151 prefixEnd_6946151 3566714161708757885967739 := by
  unfold tailWord_6946151
  simp only [CollatzResearch.WordTrace]
  refine ⟨253346940258288709989094307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168897960172192473326062871 253346940258288709989094307)
  ·
    refine ⟨380020410387433064983641461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253346940258288709989094307 380020410387433064983641461)
    ·
      refine ⟨35626913473821849842216387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 380020410387433064983641461 35626913473821849842216387)
      ·
        refine ⟨53440370210732774763324581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35626913473821849842216387 53440370210732774763324581)
        ·
          refine ⟨10020069414512395268123359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53440370210732774763324581 10020069414512395268123359)
          ·
            refine ⟨15030104121768592902185039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10020069414512395268123359 15030104121768592902185039)
            ·
              refine ⟨22545156182652889353277559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15030104121768592902185039 22545156182652889353277559)
              ·
                refine ⟨33817734273979334029916339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22545156182652889353277559 33817734273979334029916339)
                ·
                  refine ⟨50726601410969001044874509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33817734273979334029916339 50726601410969001044874509)
                  ·
                    refine ⟨19022475529113375391827941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50726601410969001044874509 19022475529113375391827941)
                    ·
                      refine ⟨3566714161708757885967739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19022475529113375391827941 3566714161708757885967739)
                      ·
                        rfl

theorem cell23_6946151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_6946151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946151 prefixEnd_6946151 := by exact prefixLift 6946151
  have htrace : WordTrace (prefixWord ++ tailWord_6946151) baseStart_6946151 baseEnd_6946151 := by
    simpa [prefixWord, tailWord_6946151, baseEnd_6946151] using wordTrace_append hprefix tailTrace_6946151
  have hstable : (prefixWord ++ tailWord_6946151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946151).length < 2 ^ (prefixWord ++ tailWord_6946151).sum := by decide
  have hdescent : baseEnd_6946151 < baseStart_6946151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946211 : List Nat := [1, 1, 1, 4, 1, 3, 1, 3, 1, 5, 2]
def baseStart_6946211 : Nat := 118140960795 + 6946211 * 2 ^ 59
def prefixEnd_6946211 : Nat := 4983230072969 + 3 ^ 40 * 6946211 * 2
def baseEnd_6946211 : Nat := 3566744970548027651217463

theorem tailTrace_6946211 : CollatzResearch.WordTrace tailWord_6946211 prefixEnd_6946211 3566744970548027651217463 := by
  unfold tailWord_6946211
  simp only [CollatzResearch.WordTrace]
  refine ⟨253349128638071340236278487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168899419092047560157518991 253349128638071340236278487)
  ·
    refine ⟨380023692957107010354417731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253349128638071340236278487 380023692957107010354417731)
    ·
      refine ⟨570035539435660515531626597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380023692957107010354417731 570035539435660515531626597)
      ·
        refine ⟨106881663644186346662179987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 570035539435660515531626597 106881663644186346662179987)
        ·
          refine ⟨160322495466279519993269981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106881663644186346662179987 160322495466279519993269981)
          ·
            refine ⟨60120935799854819997476243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160322495466279519993269981 60120935799854819997476243)
            ·
              refine ⟨90181403699782229996214365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60120935799854819997476243 90181403699782229996214365)
              ·
                refine ⟨33818026387418336248580387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90181403699782229996214365 33818026387418336248580387)
                ·
                  refine ⟨50727039581127504372870581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33818026387418336248580387 50727039581127504372870581)
                  ·
                    refine ⟨4755659960730703534956617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50727039581127504372870581 4755659960730703534956617)
                    ·
                      refine ⟨3566744970548027651217463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755659960730703534956617 3566744970548027651217463)
                      ·
                        rfl

theorem cell23_6946211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_6946211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946211 prefixEnd_6946211 := by exact prefixLift 6946211
  have htrace : WordTrace (prefixWord ++ tailWord_6946211) baseStart_6946211 baseEnd_6946211 := by
    simpa [prefixWord, tailWord_6946211, baseEnd_6946211] using wordTrace_append hprefix tailTrace_6946211
  have hstable : (prefixWord ++ tailWord_6946211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946211).length < 2 ^ (prefixWord ++ tailWord_6946211).sum := by decide
  have hdescent : baseEnd_6946211 < baseStart_6946211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946262 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2]
def baseStart_6946262 : Nat := 118140960795 + 6946262 * 2 ^ 59
def prefixEnd_6946262 : Nat := 4983230072969 + 3 ^ 40 * 6946262 * 2
def baseEnd_6946262 : Nat := 3566771158061406951679729

theorem tailTrace_6946262 : CollatzResearch.WordTrace tailWord_6946262 prefixEnd_6946262 3566771158061406951679729 := by
  unfold tailWord_6946262
  simp only [CollatzResearch.WordTrace]
  refine ⟨15834436797555410996649065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168900659173924383964256693 15834436797555410996649065)
  ·
    refine ⟨11875827598166558247486799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15834436797555410996649065 11875827598166558247486799)
    ·
      refine ⟨17813741397249837371230199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11875827598166558247486799 17813741397249837371230199)
      ·
        refine ⟨26720612095874756056845299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17813741397249837371230199 26720612095874756056845299)
        ·
          refine ⟨40080918143812134085267949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26720612095874756056845299 40080918143812134085267949)
          ·
            refine ⟨15030344303929550281975481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40080918143812134085267949 15030344303929550281975481)
            ·
              refine ⟨11272758227947162711481611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15030344303929550281975481 11272758227947162711481611)
              ·
                refine ⟨16909137341920744067222417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11272758227947162711481611 16909137341920744067222417)
                ·
                  refine ⟨12681853006440558050416813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16909137341920744067222417 12681853006440558050416813)
                  ·
                    refine ⟨4755694877415209268906305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12681853006440558050416813 4755694877415209268906305)
                    ·
                      refine ⟨3566771158061406951679729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755694877415209268906305 3566771158061406951679729)
                      ·
                        rfl

theorem cell23_6946262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_6946262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946262 prefixEnd_6946262 := by exact prefixLift 6946262
  have htrace : WordTrace (prefixWord ++ tailWord_6946262) baseStart_6946262 baseEnd_6946262 := by
    simpa [prefixWord, tailWord_6946262, baseEnd_6946262] using wordTrace_append hprefix tailTrace_6946262
  have hstable : (prefixWord ++ tailWord_6946262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946262).length < 2 ^ (prefixWord ++ tailWord_6946262).sum := by decide
  have hdescent : baseEnd_6946262 < baseStart_6946262 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946264 : List Nat := [2, 1, 2, 2, 2, 1, 4, 9]
def baseStart_6946264 : Nat := 118140960795 + 6946264 * 2 ^ 59
def prefixEnd_6946264 : Nat := 4983230072969 + 3 ^ 40 * 6946264 * 2
def baseEnd_6946264 : Nat := 132102673519359849772397

theorem tailTrace_6946264 : CollatzResearch.WordTrace tailWord_6946264 prefixEnd_6946264 132102673519359849772397 := by
  unfold tailWord_6946264
  simp only [CollatzResearch.WordTrace]
  refine ⟨126675530853439665143978923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168900707804586220191971897 126675530853439665143978923)
  ·
    refine ⟨190013296280159497715968385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126675530853439665143978923 190013296280159497715968385)
    ·
      refine ⟨142509972210119623286976289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190013296280159497715968385 142509972210119623286976289)
      ·
        refine ⟨106882479157589717465232217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142509972210119623286976289 106882479157589717465232217)
        ·
          refine ⟨80161859368192288098924163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106882479157589717465232217 80161859368192288098924163)
          ·
            refine ⟨120242789052288432148386245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80161859368192288098924163 120242789052288432148386245)
            ·
              refine ⟨22545522947304081027822421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120242789052288432148386245 22545522947304081027822421)
              ·
                refine ⟨132102673519359849772397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22545522947304081027822421 132102673519359849772397)
                ·
                  rfl

theorem cell23_6946264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 9].length) (baseStart_6946264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946264 prefixEnd_6946264 := by exact prefixLift 6946264
  have htrace : WordTrace (prefixWord ++ tailWord_6946264) baseStart_6946264 baseEnd_6946264 := by
    simpa [prefixWord, tailWord_6946264, baseEnd_6946264] using wordTrace_append hprefix tailTrace_6946264
  have hstable : (prefixWord ++ tailWord_6946264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946264).length < 2 ^ (prefixWord ++ tailWord_6946264).sum := by decide
  have hdescent : baseEnd_6946264 < baseStart_6946264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946271 : List Nat := [1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_6946271 : Nat := 118140960795 + 6946271 * 2 ^ 59
def prefixEnd_6946271 : Nat := 4983230072969 + 3 ^ 40 * 6946271 * 2
def baseEnd_6946271 : Nat := 3566775779387297416467187

theorem tailTrace_6946271 : CollatzResearch.WordTrace tailWord_6946271 prefixEnd_6946271 3566775779387297416467187 := by
  unfold tailWord_6946271
  simp only [CollatzResearch.WordTrace]
  refine ⟨253351317017853970483462667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168900878011902646988975111 253351317017853970483462667)
  ·
    refine ⟨380026975526780955725194001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253351317017853970483462667 380026975526780955725194001)
    ·
      refine ⟨285020231645085716793895501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380026975526780955725194001 285020231645085716793895501)
      ·
        refine ⟨106882586866907143797710813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285020231645085716793895501 106882586866907143797710813)
        ·
          refine ⟨40080970075090178924141555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106882586866907143797710813 40080970075090178924141555)
          ·
            refine ⟨60121455112635268386212333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40080970075090178924141555 60121455112635268386212333)
            ·
              refine ⟨22545545667238225644829625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60121455112635268386212333 22545545667238225644829625)
              ·
                refine ⟨16909159250428669233622219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22545545667238225644829625 16909159250428669233622219)
                ·
                  refine ⟨25363738875643003850433329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16909159250428669233622219 25363738875643003850433329)
                  ·
                    refine ⟨19022804156732252887824997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25363738875643003850433329 19022804156732252887824997)
                    ·
                      refine ⟨3566775779387297416467187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19022804156732252887824997 3566775779387297416467187)
                      ·
                        rfl

theorem cell23_6946271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_6946271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946271 prefixEnd_6946271 := by exact prefixLift 6946271
  have htrace : WordTrace (prefixWord ++ tailWord_6946271) baseStart_6946271 baseEnd_6946271 := by
    simpa [prefixWord, tailWord_6946271, baseEnd_6946271] using wordTrace_append hprefix tailTrace_6946271
  have hstable : (prefixWord ++ tailWord_6946271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946271).length < 2 ^ (prefixWord ++ tailWord_6946271).sum := by decide
  have hdescent : baseEnd_6946271 < baseStart_6946271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946275 : List Nat := [1, 1, 1, 6, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6946275 : Nat := 118140960795 + 6946275 * 2 ^ 59
def prefixEnd_6946275 : Nat := 4983230072969 + 3 ^ 40 * 6946275 * 2
def baseEnd_6946275 : Nat := 3566777833309915400817169

theorem tailTrace_6946275 : CollatzResearch.WordTrace tailWord_6946275 prefixEnd_6946275 3566777833309915400817169 := by
  unfold tailWord_6946275
  simp only [CollatzResearch.WordTrace]
  refine ⟨253351462909839479166608279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168900975273226319444405519 253351462909839479166608279)
  ·
    refine ⟨380027194364759218749912419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253351462909839479166608279 380027194364759218749912419)
    ·
      refine ⟨570040791547138828124868629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380027194364759218749912419 570040791547138828124868629)
      ·
        refine ⟨26720662103772132568353217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 570040791547138828124868629 26720662103772132568353217)
        ·
          refine ⟨20040496577829099426264913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26720662103772132568353217 20040496577829099426264913)
          ·
            refine ⟨15030372433371824569698685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20040496577829099426264913 15030372433371824569698685)
            ·
              refine ⟨5636389662514434213637007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15030372433371824569698685 5636389662514434213637007)
              ·
                refine ⟨8454584493771651320455511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636389662514434213637007 8454584493771651320455511)
                ·
                  refine ⟨12681876740657476980683267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8454584493771651320455511 12681876740657476980683267)
                  ·
                    refine ⟨19022815110986215471024901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12681876740657476980683267 19022815110986215471024901)
                    ·
                      refine ⟨3566777833309915400817169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19022815110986215471024901 3566777833309915400817169)
                      ·
                        rfl

theorem cell23_6946275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6946275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946275 prefixEnd_6946275 := by exact prefixLift 6946275
  have htrace : WordTrace (prefixWord ++ tailWord_6946275) baseStart_6946275 baseEnd_6946275 := by
    simpa [prefixWord, tailWord_6946275, baseEnd_6946275] using wordTrace_append hprefix tailTrace_6946275
  have hstable : (prefixWord ++ tailWord_6946275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946275).length < 2 ^ (prefixWord ++ tailWord_6946275).sum := by decide
  have hdescent : baseEnd_6946275 < baseStart_6946275 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946284 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_6946284 : Nat := 118140960795 + 6946284 * 2 ^ 59
def prefixEnd_6946284 : Nat := 4983230072969 + 3 ^ 40 * 6946284 * 2
def baseEnd_6946284 : Nat := 3566782454635805865604627

theorem tailTrace_6946284 : CollatzResearch.WordTrace tailWord_6946284 prefixEnd_6946284 3566782454635805865604627 := by
  unfold tailWord_6946284
  simp only [CollatzResearch.WordTrace]
  refine ⟨126675895583403436851842953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168901194111204582469123937 126675895583403436851842953)
  ·
    refine ⟨95006921687552577638882215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126675895583403436851842953 95006921687552577638882215)
    ·
      refine ⟨142510382531328866458323323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95006921687552577638882215 142510382531328866458323323)
      ·
        refine ⟨213765573796993299687484985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142510382531328866458323323 213765573796993299687484985)
        ·
          refine ⟨160324180347744974765613739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213765573796993299687484985 160324180347744974765613739)
          ·
            refine ⟨240486270521617462148420609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160324180347744974765613739 240486270521617462148420609)
            ·
              refine ⟨180364702891213096611315457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240486270521617462148420609 180364702891213096611315457)
              ·
                refine ⟨135273527168409822458486593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180364702891213096611315457 135273527168409822458486593)
                ·
                  refine ⟨101455145376307366843864945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135273527168409822458486593 101455145376307366843864945)
                  ·
                    refine ⟨76091359032230525132898709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101455145376307366843864945 76091359032230525132898709)
                    ·
                      refine ⟨3566782454635805865604627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76091359032230525132898709 3566782454635805865604627)
                      ·
                        rfl

theorem cell23_6946284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_6946284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946284 prefixEnd_6946284 := by exact prefixLift 6946284
  have htrace : WordTrace (prefixWord ++ tailWord_6946284) baseStart_6946284 baseEnd_6946284 := by
    simpa [prefixWord, tailWord_6946284, baseEnd_6946284] using wordTrace_append hprefix tailTrace_6946284
  have hstable : (prefixWord ++ tailWord_6946284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946284).length < 2 ^ (prefixWord ++ tailWord_6946284).sum := by decide
  have hdescent : baseEnd_6946284 < baseStart_6946284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946492 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 2, 2, 3]
def baseStart_6946492 : Nat := 118140960795 + 6946492 * 2 ^ 59
def prefixEnd_6946492 : Nat := 4983230072969 + 3 ^ 40 * 6946492 * 2
def baseEnd_6946492 : Nat := 3566889258611941051803671

theorem tailTrace_6946492 : CollatzResearch.WordTrace tailWord_6946492 prefixEnd_6946492 3566889258611941051803671 := by
  unfold tailWord_6946492
  simp only [CollatzResearch.WordTrace]
  refine ⟨126679688775026662613628865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168906251700035550151505153 126679688775026662613628865)
  ·
    refine ⟨95009766581269996960221649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126679688775026662613628865 95009766581269996960221649)
    ·
      refine ⟨71257324935952497720166237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95009766581269996960221649 71257324935952497720166237)
      ·
        refine ⟨26721496850982186645062339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71257324935952497720166237 26721496850982186645062339)
        ·
          refine ⟨40082245276473279967593509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26721496850982186645062339 40082245276473279967593509)
          ·
            refine ⟨7515420989338739993923783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40082245276473279967593509 7515420989338739993923783)
            ·
              refine ⟨11273131484008109990885675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7515420989338739993923783 11273131484008109990885675)
              ·
                refine ⟨16909697226012164986328513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11273131484008109990885675 16909697226012164986328513)
                ·
                  refine ⟨12682272919509123739746385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16909697226012164986328513 12682272919509123739746385)
                  ·
                    refine ⟨9511704689631842804809789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12682272919509123739746385 9511704689631842804809789)
                    ·
                      refine ⟨3566889258611941051803671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9511704689631842804809789 3566889258611941051803671)
                      ·
                        rfl

theorem cell23_6946492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_6946492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946492 prefixEnd_6946492 := by exact prefixLift 6946492
  have htrace : WordTrace (prefixWord ++ tailWord_6946492) baseStart_6946492 baseEnd_6946492 := by
    simpa [prefixWord, tailWord_6946492, baseEnd_6946492] using wordTrace_append hprefix tailTrace_6946492
  have hstable : (prefixWord ++ tailWord_6946492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946492).length < 2 ^ (prefixWord ++ tailWord_6946492).sum := by decide
  have hdescent : baseEnd_6946492 < baseStart_6946492 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946501 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_6946501 : Nat := 118140960795 + 6946501 * 2 ^ 59
def prefixEnd_6946501 : Nat := 4983230072969 + 3 ^ 40 * 6946501 * 2
def baseEnd_6946501 : Nat := 3566893879937831516591129

theorem tailTrace_6946501 : CollatzResearch.WordTrace tailWord_6946501 prefixEnd_6946501 3566893879937831516591129 := by
  unfold tailWord_6946501
  simp only [CollatzResearch.WordTrace]
  refine ⟨253359705807020719764335357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168906470538013813176223571 253359705807020719764335357)
  ·
    refine ⟨95009889677632769911625759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253359705807020719764335357 95009889677632769911625759)
    ·
      refine ⟨142514834516449154867438639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95009889677632769911625759 142514834516449154867438639)
      ·
        refine ⟨213772251774673732301157959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142514834516449154867438639 213772251774673732301157959)
        ·
          refine ⟨320658377662010598451736939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213772251774673732301157959 320658377662010598451736939)
          ·
            refine ⟨480987566493015897677605409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320658377662010598451736939 480987566493015897677605409)
            ·
              refine ⟨360740674869761923258204057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 480987566493015897677605409 360740674869761923258204057)
              ·
                refine ⟨270555506152321442443653043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360740674869761923258204057 270555506152321442443653043)
                ·
                  refine ⟨405833259228482163665479565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 270555506152321442443653043 405833259228482163665479565)
                  ·
                    refine ⟨152187472210680811374554837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 405833259228482163665479565 152187472210680811374554837)
                    ·
                      refine ⟨3566893879937831516591129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152187472210680811374554837 3566893879937831516591129)
                      ·
                        rfl

theorem cell23_6946501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_6946501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946501 prefixEnd_6946501 := by exact prefixLift 6946501
  have htrace : WordTrace (prefixWord ++ tailWord_6946501) baseStart_6946501 baseEnd_6946501 := by
    simpa [prefixWord, tailWord_6946501, baseEnd_6946501] using wordTrace_append hprefix tailTrace_6946501
  have hstable : (prefixWord ++ tailWord_6946501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946501).length < 2 ^ (prefixWord ++ tailWord_6946501).sum := by decide
  have hdescent : baseEnd_6946501 < baseStart_6946501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946502 : List Nat := [6, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_6946502 : Nat := 118140960795 + 6946502 * 2 ^ 59
def prefixEnd_6946502 : Nat := 4983230072969 + 3 ^ 40 * 6946502 * 2
def baseEnd_6946502 : Nat := 3566894393418486012678625

theorem tailTrace_6946502 : CollatzResearch.WordTrace tailWord_6946502 prefixEnd_6946502 3566894393418486012678625 := by
  unfold tailWord_6946502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917491946250534279222555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168906494853344731290081173 7917491946250534279222555)
  ·
    refine ⟨11876237919375801418833833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917491946250534279222555 11876237919375801418833833)
    ·
      refine ⟨8907178439531851064125375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11876237919375801418833833 8907178439531851064125375)
      ·
        refine ⟨13360767659297776596188063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8907178439531851064125375 13360767659297776596188063)
        ·
          refine ⟨20041151488946664894282095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13360767659297776596188063 20041151488946664894282095)
          ·
            refine ⟨30061727233419997341423143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20041151488946664894282095 30061727233419997341423143)
            ·
              refine ⟨45092590850129996012134715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30061727233419997341423143 45092590850129996012134715)
              ·
                refine ⟨67638886275194994018202073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45092590850129996012134715 67638886275194994018202073)
                ·
                  refine ⟨50729164706396245513651555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67638886275194994018202073 50729164706396245513651555)
                  ·
                    refine ⟨76093747059594368270477333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50729164706396245513651555 76093747059594368270477333)
                    ·
                      refine ⟨3566894393418486012678625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76093747059594368270477333 3566894393418486012678625)
                      ·
                        rfl

theorem cell23_6946502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_6946502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946502 prefixEnd_6946502 := by exact prefixLift 6946502
  have htrace : WordTrace (prefixWord ++ tailWord_6946502) baseStart_6946502 baseEnd_6946502 := by
    simpa [prefixWord, tailWord_6946502, baseEnd_6946502] using wordTrace_append hprefix tailTrace_6946502
  have hstable : (prefixWord ++ tailWord_6946502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946502).length < 2 ^ (prefixWord ++ tailWord_6946502).sum := by decide
  have hdescent : baseEnd_6946502 < baseStart_6946502 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946522 : List Nat := [3, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3]
def baseStart_6946522 : Nat := 118140960795 + 6946522 * 2 ^ 59
def prefixEnd_6946522 : Nat := 4983230072969 + 3 ^ 40 * 6946522 * 2
def baseEnd_6946522 : Nat := 3566904663031575934428533

theorem tailTrace_6946522 : CollatzResearch.WordTrace tailWord_6946522 prefixEnd_6946522 3566904663031575934428533 := by
  unfold tailWord_6946522
  simp only [CollatzResearch.WordTrace]
  refine ⟨63340117934986160087712455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168906981159963093567233213 63340117934986160087712455)
  ·
    refine ⟨95010176902479240131568683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63340117934986160087712455 95010176902479240131568683)
    ·
      refine ⟨142515265353718860197353025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95010176902479240131568683 142515265353718860197353025)
      ·
        refine ⟨106886449015289145148014769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142515265353718860197353025 106886449015289145148014769)
        ·
          refine ⟨80164836761466858861011077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106886449015289145148014769 80164836761466858861011077)
          ·
            refine ⟨15030906892775036036439577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80164836761466858861011077 15030906892775036036439577)
            ·
              refine ⟨11273180169581277027329683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15030906892775036036439577 11273180169581277027329683)
              ·
                refine ⟨16909770254371915540994525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11273180169581277027329683 16909770254371915540994525)
                ·
                  refine ⟨6341163845389468327872947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16909770254371915540994525 6341163845389468327872947)
                  ·
                    refine ⟨9511745768084202491809421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6341163845389468327872947 9511745768084202491809421)
                    ·
                      refine ⟨3566904663031575934428533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9511745768084202491809421 3566904663031575934428533)
                      ·
                        rfl

theorem cell23_6946522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_6946522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946522 prefixEnd_6946522 := by exact prefixLift 6946522
  have htrace : WordTrace (prefixWord ++ tailWord_6946522) baseStart_6946522 baseEnd_6946522 := by
    simpa [prefixWord, tailWord_6946522, baseEnd_6946522] using wordTrace_append hprefix tailTrace_6946522
  have hstable : (prefixWord ++ tailWord_6946522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946522).length < 2 ^ (prefixWord ++ tailWord_6946522).sum := by decide
  have hdescent : baseEnd_6946522 < baseStart_6946522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946528 : List Nat := [2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_6946528 : Nat := 118140960795 + 6946528 * 2 ^ 59
def prefixEnd_6946528 : Nat := 4983230072969 + 3 ^ 40 * 6946528 * 2
def baseEnd_6946528 : Nat := 3566907743915502910953505

theorem tailTrace_6946528 : CollatzResearch.WordTrace tailWord_6946528 prefixEnd_6946528 3566907743915502910953505 := by
  unfold tailWord_6946528
  simp only [CollatzResearch.WordTrace]
  refine ⟨126680345288961451687784119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168907127051948602250378825 126680345288961451687784119)
  ·
    refine ⟨190020517933442177531676179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126680345288961451687784119 190020517933442177531676179)
    ·
      refine ⟨285030776900163266297514269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190020517933442177531676179 285030776900163266297514269)
      ·
        refine ⟨106886541337561224861567851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285030776900163266297514269 106886541337561224861567851)
        ·
          refine ⟨160329812006341837292351777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106886541337561224861567851 160329812006341837292351777)
          ·
            refine ⟨120247359004756377969263833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160329812006341837292351777 120247359004756377969263833)
            ·
              refine ⟨90185519253567283476947875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120247359004756377969263833 90185519253567283476947875)
              ·
                refine ⟨135278278880350925215421813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90185519253567283476947875 135278278880350925215421813)
                ·
                  refine ⟨12682338645032899238945795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135278278880350925215421813 12682338645032899238945795)
                  ·
                    refine ⟨19023507967549348858418693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12682338645032899238945795 19023507967549348858418693)
                    ·
                      refine ⟨3566907743915502910953505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19023507967549348858418693 3566907743915502910953505)
                      ·
                        rfl

theorem cell23_6946528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_6946528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946528 prefixEnd_6946528 := by exact prefixLift 6946528
  have htrace : WordTrace (prefixWord ++ tailWord_6946528) baseStart_6946528 baseEnd_6946528 := by
    simpa [prefixWord, tailWord_6946528, baseEnd_6946528] using wordTrace_append hprefix tailTrace_6946528
  have hstable : (prefixWord ++ tailWord_6946528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946528).length < 2 ^ (prefixWord ++ tailWord_6946528).sum := by decide
  have hdescent : baseEnd_6946528 < baseStart_6946528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946545 : List Nat := [1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 4]
def baseStart_6946545 : Nat := 118140960795 + 6946545 * 2 ^ 59
def prefixEnd_6946545 : Nat := 4983230072969 + 3 ^ 40 * 6946545 * 2
def baseEnd_6946545 : Nat := 3566916473086629344440927

theorem tailTrace_6946545 : CollatzResearch.WordTrace tailWord_6946545 prefixEnd_6946545 3566916473086629344440927 := by
  unfold tailWord_6946545
  simp only [CollatzResearch.WordTrace]
  refine ⟨253361310618861315278937089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168907540412574210185958059 253361310618861315278937089)
  ·
    refine ⟨190020982964145986459202817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253361310618861315278937089 190020982964145986459202817)
    ·
      refine ⟨142515737223109489844402113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190020982964145986459202817 142515737223109489844402113)
      ·
        refine ⟨106886802917332117383301585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142515737223109489844402113 106886802917332117383301585)
        ·
          refine ⟨80165102187999088037476189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106886802917332117383301585 80165102187999088037476189)
          ·
            refine ⟨30061913320499658014053571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80165102187999088037476189 30061913320499658014053571)
            ·
              refine ⟨45092869980749487021080357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30061913320499658014053571 45092869980749487021080357)
              ·
                refine ⟨8454913121390528816452567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45092869980749487021080357 8454913121390528816452567)
                ·
                  refine ⟨12682369682085793224678851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8454913121390528816452567 12682369682085793224678851)
                  ·
                    refine ⟨19023554523128689837018277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12682369682085793224678851 19023554523128689837018277)
                    ·
                      refine ⟨3566916473086629344440927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19023554523128689837018277 3566916473086629344440927)
                      ·
                        rfl

theorem cell23_6946545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_6946545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946545 prefixEnd_6946545 := by exact prefixLift 6946545
  have htrace : WordTrace (prefixWord ++ tailWord_6946545) baseStart_6946545 baseEnd_6946545 := by
    simpa [prefixWord, tailWord_6946545, baseEnd_6946545] using wordTrace_append hprefix tailTrace_6946545
  have hstable : (prefixWord ++ tailWord_6946545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946545).length < 2 ^ (prefixWord ++ tailWord_6946545).sum := by decide
  have hdescent : baseEnd_6946545 < baseStart_6946545 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946562 : List Nat := [3, 4, 1, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_6946562 : Nat := 118140960795 + 6946562 * 2 ^ 59
def prefixEnd_6946562 : Nat := 4983230072969 + 3 ^ 40 * 6946562 * 2
def baseEnd_6946562 : Nat := 3566925202257755777928349

theorem tailTrace_6946562 : CollatzResearch.WordTrace tailWord_6946562 prefixEnd_6946562 3566925202257755777928349 := by
  unfold tailWord_6946562
  simp only [CollatzResearch.WordTrace]
  refine ⟨63340482664949931795576485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168907953773199818121537293 63340482664949931795576485)
  ·
    refine ⟨11876340499678112211670591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 63340482664949931795576485 11876340499678112211670591)
    ·
      refine ⟨17814510749517168317505887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876340499678112211670591 17814510749517168317505887)
      ·
        refine ⟨26721766124275752476258831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17814510749517168317505887 26721766124275752476258831)
        ·
          refine ⟨40082649186413628714388247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26721766124275752476258831 40082649186413628714388247)
          ·
            refine ⟨60123973779620443071582371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40082649186413628714388247 60123973779620443071582371)
            ·
              refine ⟨90185960669430664607373557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60123973779620443071582371 90185960669430664607373557)
              ·
                refine ⟨8454933812759124806941271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 90185960669430664607373557 8454933812759124806941271)
                ·
                  refine ⟨12682400719138687210411907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8454933812759124806941271 12682400719138687210411907)
                  ·
                    refine ⟨19023601078708030815617861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12682400719138687210411907 19023601078708030815617861)
                    ·
                      refine ⟨3566925202257755777928349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19023601078708030815617861 3566925202257755777928349)
                      ·
                        rfl

theorem cell23_6946562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_6946562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946562 prefixEnd_6946562 := by exact prefixLift 6946562
  have htrace : WordTrace (prefixWord ++ tailWord_6946562) baseStart_6946562 baseEnd_6946562 := by
    simpa [prefixWord, tailWord_6946562, baseEnd_6946562] using wordTrace_append hprefix tailTrace_6946562
  have hstable : (prefixWord ++ tailWord_6946562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946562).length < 2 ^ (prefixWord ++ tailWord_6946562).sum := by decide
  have hdescent : baseEnd_6946562 < baseStart_6946562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946588 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_6946588 : Nat := 118140960795 + 6946588 * 2 ^ 59
def prefixEnd_6946588 : Nat := 4983230072969 + 3 ^ 40 * 6946588 * 2
def baseEnd_6946588 : Nat := 3566938552754772676203229

theorem tailTrace_6946588 : CollatzResearch.WordTrace tailWord_6946588 prefixEnd_6946588 3566938552754772676203229 := by
  unfold tailWord_6946588
  simp only [CollatzResearch.WordTrace]
  refine ⟨126681439478852766811376209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168908585971803689081834945 126681439478852766811376209)
  ·
    refine ⟨95011079609139575108532157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126681439478852766811376209 95011079609139575108532157)
    ·
      refine ⟨35629154853427340665699559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95011079609139575108532157 35629154853427340665699559)
      ·
        refine ⟨53443732280141010998549339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35629154853427340665699559 53443732280141010998549339)
        ·
          refine ⟨80165598420211516497824009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53443732280141010998549339 80165598420211516497824009)
          ·
            refine ⟨60124198815158637373368007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80165598420211516497824009 60124198815158637373368007)
            ·
              refine ⟨90186298222737956060052011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60124198815158637373368007 90186298222737956060052011)
              ·
                refine ⟨135279447334106934090078017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90186298222737956060052011 135279447334106934090078017)
                ·
                  refine ⟨101459585500580200567558513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135279447334106934090078017 101459585500580200567558513)
                  ·
                    refine ⟨76094689125435150425668885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101459585500580200567558513 76094689125435150425668885)
                    ·
                      refine ⟨3566938552754772676203229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76094689125435150425668885 3566938552754772676203229)
                      ·
                        rfl

theorem cell23_6946588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_6946588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946588 prefixEnd_6946588 := by exact prefixLift 6946588
  have htrace : WordTrace (prefixWord ++ tailWord_6946588) baseStart_6946588 baseEnd_6946588 := by
    simpa [prefixWord, tailWord_6946588, baseEnd_6946588] using wordTrace_append hprefix tailTrace_6946588
  have hstable : (prefixWord ++ tailWord_6946588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946588).length < 2 ^ (prefixWord ++ tailWord_6946588).sum := by decide
  have hdescent : baseEnd_6946588 < baseStart_6946588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946612 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 3, 3, 3]
def baseStart_6946612 : Nat := 118140960795 + 6946612 * 2 ^ 59
def prefixEnd_6946612 : Nat := 4983230072969 + 3 ^ 40 * 6946612 * 2
def baseEnd_6946612 : Nat := 3566950876290480582303119

theorem tailTrace_6946612 : CollatzResearch.WordTrace tailWord_6946612 prefixEnd_6946612 3566950876290480582303119 := by
  unfold tailWord_6946612
  simp only [CollatzResearch.WordTrace]
  refine ⟨126681877154809292860813045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168909169539745723814417393 126681877154809292860813045)
  ·
    refine ⟨11876425983263371205701223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126681877154809292860813045 11876425983263371205701223)
    ·
      refine ⟨17814638974895056808551835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876425983263371205701223 17814638974895056808551835)
      ·
        refine ⟨26721958462342585212827753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17814638974895056808551835 26721958462342585212827753)
        ·
          refine ⟨20041468846756938909620815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26721958462342585212827753 20041468846756938909620815)
          ·
            refine ⟨30062203270135408364431223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20041468846756938909620815 30062203270135408364431223)
            ·
              refine ⟨45093304905203112546646835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30062203270135408364431223 45093304905203112546646835)
              ·
                refine ⟨67639957357804668819970253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45093304905203112546646835 67639957357804668819970253)
                ·
                  refine ⟨25364984009176750807488845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67639957357804668819970253 25364984009176750807488845)
                  ·
                    refine ⟨9511869003441281552808317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25364984009176750807488845 9511869003441281552808317)
                    ·
                      refine ⟨3566950876290480582303119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9511869003441281552808317 3566950876290480582303119)
                      ·
                        rfl

theorem cell23_6946612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_6946612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946612 prefixEnd_6946612 := by exact prefixLift 6946612
  have htrace : WordTrace (prefixWord ++ tailWord_6946612) baseStart_6946612 baseEnd_6946612 := by
    simpa [prefixWord, tailWord_6946612, baseEnd_6946612] using wordTrace_append hprefix tailTrace_6946612
  have hstable : (prefixWord ++ tailWord_6946612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946612).length < 2 ^ (prefixWord ++ tailWord_6946612).sum := by decide
  have hdescent : baseEnd_6946612 < baseStart_6946612 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946630 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6946630 : Nat := 118140960795 + 6946630 * 2 ^ 59
def prefixEnd_6946630 : Nat := 4983230072969 + 3 ^ 40 * 6946630 * 2
def baseEnd_6946630 : Nat := 3566960118942261511878037

theorem tailTrace_6946630 : CollatzResearch.WordTrace tailWord_6946630 prefixEnd_6946630 3566960118942261511878037 := by
  unfold tailWord_6946630
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917637838236042962368167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168909607215702249863854229 7917637838236042962368167)
  ·
    refine ⟨11876456757354064443552251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917637838236042962368167 11876456757354064443552251)
    ·
      refine ⟨17814685136031096665328377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876456757354064443552251 17814685136031096665328377)
      ·
        refine ⟨13361013852023322498996283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17814685136031096665328377 13361013852023322498996283)
        ·
          refine ⟨20041520778034983748494425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13361013852023322498996283 20041520778034983748494425)
          ·
            refine ⟨15031140583526237811370819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20041520778034983748494425 15031140583526237811370819)
            ·
              refine ⟨22546710875289356717056229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15031140583526237811370819 22546710875289356717056229)
              ·
                refine ⟨4227508289116754384448043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22546710875289356717056229 4227508289116754384448043)
                ·
                  refine ⟨6341262433675131576672065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4227508289116754384448043 6341262433675131576672065)
                  ·
                    refine ⟨4755946825256348682504049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6341262433675131576672065 4755946825256348682504049)
                    ·
                      refine ⟨3566960118942261511878037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4755946825256348682504049 3566960118942261511878037)
                      ·
                        rfl

theorem cell23_6946630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6946630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946630 prefixEnd_6946630 := by exact prefixLift 6946630
  have htrace : WordTrace (prefixWord ++ tailWord_6946630) baseStart_6946630 baseEnd_6946630 := by
    simpa [prefixWord, tailWord_6946630, baseEnd_6946630] using wordTrace_append hprefix tailTrace_6946630
  have hstable : (prefixWord ++ tailWord_6946630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946630).length < 2 ^ (prefixWord ++ tailWord_6946630).sum := by decide
  have hdescent : baseEnd_6946630 < baseStart_6946630 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946645 : List Nat := [1, 3, 2, 2, 2, 3, 1, 1, 2, 6]
def baseStart_6946645 : Nat := 118140960795 + 6946645 * 2 ^ 59
def prefixEnd_6946645 : Nat := 4983230072969 + 3 ^ 40 * 6946645 * 2
def baseEnd_6946645 : Nat := 1188989273717359651063489

theorem tailTrace_6946645 : CollatzResearch.WordTrace tailWord_6946645 prefixEnd_6946645 1188989273717359651063489 := by
  unfold tailWord_6946645
  simp only [CollatzResearch.WordTrace]
  refine ⟨253364957918499032357577389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168909971945666021571718259 253364957918499032357577389)
  ·
    refine ⟨95011859219437137134091521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253364957918499032357577389 95011859219437137134091521)
    ·
      refine ⟨71258894414577852850568641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95011859219437137134091521 71258894414577852850568641)
      ·
        refine ⟨53444170810933389637926481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71258894414577852850568641 53444170810933389637926481)
        ·
          refine ⟨40083128108200042228444861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53444170810933389637926481 40083128108200042228444861)
          ·
            refine ⟨15031173040575015835666823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40083128108200042228444861 15031173040575015835666823)
            ·
              refine ⟨22546759560862523753500235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15031173040575015835666823 22546759560862523753500235)
              ·
                refine ⟨33820139341293785630250353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22546759560862523753500235 33820139341293785630250353)
                ·
                  refine ⟨25365104505970339222687765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33820139341293785630250353 25365104505970339222687765)
                  ·
                    refine ⟨1188989273717359651063489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25365104505970339222687765 1188989273717359651063489)
                    ·
                      rfl

theorem cell23_6946645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_6946645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946645 prefixEnd_6946645 := by exact prefixLift 6946645
  have htrace : WordTrace (prefixWord ++ tailWord_6946645) baseStart_6946645 baseEnd_6946645 := by
    simpa [prefixWord, tailWord_6946645, baseEnd_6946645] using wordTrace_append hprefix tailTrace_6946645
  have hstable : (prefixWord ++ tailWord_6946645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946645).length < 2 ^ (prefixWord ++ tailWord_6946645).sum := by decide
  have hdescent : baseEnd_6946645 < baseStart_6946645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946692 : List Nat := [2, 3, 2, 1, 1, 1, 4, 4, 5]
def baseStart_6946692 : Nat := 118140960795 + 6946692 * 2 ^ 59
def prefixEnd_6946692 : Nat := 4983230072969 + 3 ^ 40 * 6946692 * 2
def baseEnd_6946692 : Nat := 396332439415871141033639

theorem tailTrace_6946692 : CollatzResearch.WordTrace tailWord_6946692 prefixEnd_6946692 396332439415871141033639 := by
  unfold tailWord_6946692
  simp only [CollatzResearch.WordTrace]
  refine ⟨126683336074664379692269165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168911114766219172923025553 126683336074664379692269165)
  ·
    refine ⟨47506251027999142384600937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126683336074664379692269165 47506251027999142384600937)
    ·
      refine ⟨35629688270999356788450703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47506251027999142384600937 35629688270999356788450703)
      ·
        refine ⟨53444532406499035182676055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35629688270999356788450703 53444532406499035182676055)
        ·
          refine ⟨80166798609748552774014083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53444532406499035182676055 80166798609748552774014083)
          ·
            refine ⟨120250197914622829161021125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80166798609748552774014083 120250197914622829161021125)
            ·
              refine ⟨22546912108991780467691461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120250197914622829161021125 22546912108991780467691461)
              ·
                refine ⟨4227546020435958837692149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22546912108991780467691461 4227546020435958837692149)
                ·
                  refine ⟨396332439415871141033639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227546020435958837692149 396332439415871141033639)
                  ·
                    rfl

theorem cell23_6946692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 4, 5].length) (baseStart_6946692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946692 prefixEnd_6946692 := by exact prefixLift 6946692
  have htrace : WordTrace (prefixWord ++ tailWord_6946692) baseStart_6946692 baseEnd_6946692 := by
    simpa [prefixWord, tailWord_6946692, baseEnd_6946692] using wordTrace_append hprefix tailTrace_6946692
  have hstable : (prefixWord ++ tailWord_6946692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946692).length < 2 ^ (prefixWord ++ tailWord_6946692).sum := by decide
  have hdescent : baseEnd_6946692 < baseStart_6946692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946725 : List Nat := [1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 4]
def baseStart_6946725 : Nat := 118140960795 + 6946725 * 2 ^ 59
def prefixEnd_6946725 : Nat := 4983230072969 + 3 ^ 40 * 6946725 * 2
def baseEnd_6946725 : Nat := 3567008899604438640190099

theorem tailTrace_6946725 : CollatzResearch.WordTrace tailWord_6946725 prefixEnd_6946725 3567008899604438640190099 := by
  unfold tailWord_6946725
  simp only [CollatzResearch.WordTrace]
  refine ⟨253367875758209206020489629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168911917172139470680326419 253367875758209206020489629)
  ·
    refine ⟨95012953409328452257683611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253367875758209206020489629 95012953409328452257683611)
    ·
      refine ⟨142519430113992678386525417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95012953409328452257683611 142519430113992678386525417)
      ·
        refine ⟨106889572585494508789894063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142519430113992678386525417 106889572585494508789894063)
        ·
          refine ⟨160334358878241763184841095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106889572585494508789894063 160334358878241763184841095)
          ·
            refine ⟨240501538317362644777261643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160334358878241763184841095 240501538317362644777261643)
            ·
              refine ⟨360752307476043967165892465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240501538317362644777261643 360752307476043967165892465)
              ·
                refine ⟨270564230607032975374419349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360752307476043967165892465 270564230607032975374419349)
                ·
                  refine ⟨12682698309704670720675907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270564230607032975374419349 12682698309704670720675907)
                  ·
                    refine ⟨19024047464557006081013861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12682698309704670720675907 19024047464557006081013861)
                    ·
                      refine ⟨3567008899604438640190099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19024047464557006081013861 3567008899604438640190099)
                      ·
                        rfl

theorem cell23_6946725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 2, 6, 1, 4].length) (baseStart_6946725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946725 prefixEnd_6946725 := by exact prefixLift 6946725
  have htrace : WordTrace (prefixWord ++ tailWord_6946725) baseStart_6946725 baseEnd_6946725 := by
    simpa [prefixWord, tailWord_6946725, baseEnd_6946725] using wordTrace_append hprefix tailTrace_6946725
  have hstable : (prefixWord ++ tailWord_6946725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946725).length < 2 ^ (prefixWord ++ tailWord_6946725).sum := by decide
  have hdescent : baseEnd_6946725 < baseStart_6946725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946826 : List Nat := [3, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_6946826 : Nat := 118140960795 + 6946826 * 2 ^ 59
def prefixEnd_6946826 : Nat := 4983230072969 + 3 ^ 40 * 6946826 * 2
def baseEnd_6946826 : Nat := 3567060761150542745027135

theorem tailTrace_6946826 : CollatzResearch.WordTrace tailWord_6946826 prefixEnd_6946826 3567060761150542745027135 := by
  unfold tailWord_6946826
  simp only [CollatzResearch.WordTrace]
  refine ⟨63342889882710825067479083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168914373020562200179944221 63342889882710825067479083)
  ·
    refine ⟨95014334824066237601218625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63342889882710825067479083 95014334824066237601218625)
    ·
      refine ⟨71260751118049678200913969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95014334824066237601218625 71260751118049678200913969)
      ·
        refine ⟨53445563338537258650685477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71260751118049678200913969 53445563338537258650685477)
        ·
          refine ⟨10021043125975735997003527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53445563338537258650685477 10021043125975735997003527)
          ·
            refine ⟨15031564688963603995505291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021043125975735997003527 15031564688963603995505291)
            ·
              refine ⟨22547347033445405993257937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15031564688963603995505291 22547347033445405993257937)
              ·
                refine ⟨16910510275084054494943453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22547347033445405993257937 16910510275084054494943453)
                ·
                  refine ⟨6341441353156520435603795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16910510275084054494943453 6341441353156520435603795)
                  ·
                    refine ⟨9512162029734780653405693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6341441353156520435603795 9512162029734780653405693)
                    ·
                      refine ⟨3567060761150542745027135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9512162029734780653405693 3567060761150542745027135)
                      ·
                        rfl

theorem cell23_6946826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_6946826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946826 prefixEnd_6946826 := by exact prefixLift 6946826
  have htrace : WordTrace (prefixWord ++ tailWord_6946826) baseStart_6946826 baseEnd_6946826 := by
    simpa [prefixWord, tailWord_6946826, baseEnd_6946826] using wordTrace_append hprefix tailTrace_6946826
  have hstable : (prefixWord ++ tailWord_6946826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946826).length < 2 ^ (prefixWord ++ tailWord_6946826).sum := by decide
  have hdescent : baseEnd_6946826 < baseStart_6946826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946832 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 2, 6, 2]
def baseStart_6946832 : Nat := 118140960795 + 6946832 * 2 ^ 59
def prefixEnd_6946832 : Nat := 4983230072969 + 3 ^ 40 * 6946832 * 2
def baseEnd_6946832 : Nat := 3567063842034469721552107

theorem tailTrace_6946832 : CollatzResearch.WordTrace tailWord_6946832 prefixEnd_6946832 3567063842034469721552107 := by
  unfold tailWord_6946832
  simp only [CollatzResearch.WordTrace]
  refine ⟨126685889184410781647317375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168914518912547708863089833 126685889184410781647317375)
  ·
    refine ⟨190028833776616172470976063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126685889184410781647317375 190028833776616172470976063)
    ·
      refine ⟨285043250664924258706464095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190028833776616172470976063 285043250664924258706464095)
      ·
        refine ⟨427564875997386388059696143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285043250664924258706464095 427564875997386388059696143)
        ·
          refine ⟨641347313996079582089544215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427564875997386388059696143 641347313996079582089544215)
          ·
            refine ⟨962020970994119373134316323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641347313996079582089544215 962020970994119373134316323)
            ·
              refine ⟨1443031456491179059701474485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962020970994119373134316323 1443031456491179059701474485)
              ·
                refine ⟨135284199046048036847013233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443031456491179059701474485 135284199046048036847013233)
                ·
                  refine ⟨101463149284536027635259925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135284199046048036847013233 101463149284536027635259925)
                  ·
                    refine ⟨4756085122712626295402809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101463149284536027635259925 4756085122712626295402809)
                    ·
                      refine ⟨3567063842034469721552107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756085122712626295402809 3567063842034469721552107)
                      ·
                        rfl

theorem cell23_6946832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 2, 6, 2].length) (baseStart_6946832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946832 prefixEnd_6946832 := by exact prefixLift 6946832
  have htrace : WordTrace (prefixWord ++ tailWord_6946832) baseStart_6946832 baseEnd_6946832 := by
    simpa [prefixWord, tailWord_6946832, baseEnd_6946832] using wordTrace_append hprefix tailTrace_6946832
  have hstable : (prefixWord ++ tailWord_6946832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946832).length < 2 ^ (prefixWord ++ tailWord_6946832).sum := by decide
  have hdescent : baseEnd_6946832 < baseStart_6946832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946842 : List Nat := [3, 1, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_6946842 : Nat := 118140960795 + 6946842 * 2 ^ 59
def prefixEnd_6946842 : Nat := 4983230072969 + 3 ^ 40 * 6946842 * 2
def baseEnd_6946842 : Nat := 1189022992280338227475687

theorem tailTrace_6946842 : CollatzResearch.WordTrace tailWord_6946842 prefixEnd_6946842 1189022992280338227475687 := by
  unfold tailWord_6946842
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343035774696333750624695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168914762065856890001665853 63343035774696333750624695)
  ·
    refine ⟨95014553662044500625937043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63343035774696333750624695 95014553662044500625937043)
    ·
      refine ⟨142521830493066750938905565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95014553662044500625937043 142521830493066750938905565)
      ·
        refine ⟨53445686434900031602089587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142521830493066750938905565 53445686434900031602089587)
        ·
          refine ⟨80168529652350047403134381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53445686434900031602089587 80168529652350047403134381)
          ·
            refine ⟨30063198619631267776175393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80168529652350047403134381 30063198619631267776175393)
            ·
              refine ⟨22547398964723450832131545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30063198619631267776175393 22547398964723450832131545)
              ·
                refine ⟨16910549223542588124098659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22547398964723450832131545 16910549223542588124098659)
                ·
                  refine ⟨25365823835313882186147989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16910549223542588124098659 25365823835313882186147989)
                  ·
                    refine ⟨1189022992280338227475687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25365823835313882186147989 1189022992280338227475687)
                    ·
                      rfl

theorem cell23_6946842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_6946842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946842 prefixEnd_6946842 := by exact prefixLift 6946842
  have htrace : WordTrace (prefixWord ++ tailWord_6946842) baseStart_6946842 baseEnd_6946842 := by
    simpa [prefixWord, tailWord_6946842, baseEnd_6946842] using wordTrace_append hprefix tailTrace_6946842
  have hstable : (prefixWord ++ tailWord_6946842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946842).length < 2 ^ (prefixWord ++ tailWord_6946842).sum := by decide
  have hdescent : baseEnd_6946842 < baseStart_6946842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946866 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2]
def baseStart_6946866 : Nat := 118140960795 + 6946866 * 2 ^ 59
def prefixEnd_6946866 : Nat := 4983230072969 + 3 ^ 40 * 6946866 * 2
def baseEnd_6946866 : Nat := 3567081300376722588526951

theorem tailTrace_6946866 : CollatzResearch.WordTrace tailWord_6946866 prefixEnd_6946866 3567081300376722588526951 := by
  unfold tailWord_6946866
  simp only [CollatzResearch.WordTrace]
  refine ⟨63343254612674596775343113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168915345633798924734248301 63343254612674596775343113)
  ·
    refine ⟨47507440959505947581507335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63343254612674596775343113 47507440959505947581507335)
    ·
      refine ⟨71261161439258921372261003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47507440959505947581507335 71261161439258921372261003)
      ·
        refine ⟨106891742158888382058391505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71261161439258921372261003 106891742158888382058391505)
        ·
          refine ⟨80168806619166286543793629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106891742158888382058391505 80168806619166286543793629)
          ·
            refine ⟨30063302482187357453922611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80168806619166286543793629 30063302482187357453922611)
            ·
              refine ⟨45094953723281036180883917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30063302482187357453922611 45094953723281036180883917)
              ·
                refine ⟨16910607646230388567831469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45094953723281036180883917 16910607646230388567831469)
                ·
                  refine ⟨6341477867336395712936801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16910607646230388567831469 6341477867336395712936801)
                  ·
                    refine ⟨4756108400502296784702601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6341477867336395712936801 4756108400502296784702601)
                    ·
                      refine ⟨3567081300376722588526951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756108400502296784702601 3567081300376722588526951)
                      ·
                        rfl

theorem cell23_6946866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2].length) (baseStart_6946866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946866 prefixEnd_6946866 := by exact prefixLift 6946866
  have htrace : WordTrace (prefixWord ++ tailWord_6946866) baseStart_6946866 baseEnd_6946866 := by
    simpa [prefixWord, tailWord_6946866, baseEnd_6946866] using wordTrace_append hprefix tailTrace_6946866
  have hstable : (prefixWord ++ tailWord_6946866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946866).length < 2 ^ (prefixWord ++ tailWord_6946866).sum := by decide
  have hdescent : baseEnd_6946866 < baseStart_6946866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946875 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_6946875 : Nat := 118140960795 + 6946875 * 2 ^ 59
def prefixEnd_6946875 : Nat := 4983230072969 + 3 ^ 40 * 6946875 * 2
def baseEnd_6946875 : Nat := 3567085921702613053314409

theorem tailTrace_6946875 : CollatzResearch.WordTrace tailWord_6946875 prefixEnd_6946875 3567085921702613053314409 := by
  unfold tailWord_6946875
  simp only [CollatzResearch.WordTrace]
  refine ⟨253373346707665781638450079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168915564471777187758966719 253373346707665781638450079)
  ·
    refine ⟨380060020061498672457675119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253373346707665781638450079 380060020061498672457675119)
    ·
      refine ⟨570090030092248008686512679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380060020061498672457675119 570090030092248008686512679)
      ·
        refine ⟨855135045138372013029769019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570090030092248008686512679 855135045138372013029769019)
        ·
          refine ⟨1282702567707558019544653529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855135045138372013029769019 1282702567707558019544653529)
          ·
            refine ⟨962026925780668514658490147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1282702567707558019544653529 962026925780668514658490147)
            ·
              refine ⟨1443040388671002771987735221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962026925780668514658490147 1443040388671002771987735221)
              ·
                refine ⟨135285036437906509873850177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1443040388671002771987735221 135285036437906509873850177)
                ·
                  refine ⟨101463777328429882405387633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135285036437906509873850177 101463777328429882405387633)
                  ·
                    refine ⟨76097832996322411804040725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101463777328429882405387633 76097832996322411804040725)
                    ·
                      refine ⟨3567085921702613053314409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76097832996322411804040725 3567085921702613053314409)
                      ·
                        rfl

theorem cell23_6946875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_6946875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946875 prefixEnd_6946875 := by exact prefixLift 6946875
  have htrace : WordTrace (prefixWord ++ tailWord_6946875) baseStart_6946875 baseEnd_6946875 := by
    simpa [prefixWord, tailWord_6946875, baseEnd_6946875] using wordTrace_append hprefix tailTrace_6946875
  have hstable : (prefixWord ++ tailWord_6946875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946875).length < 2 ^ (prefixWord ++ tailWord_6946875).sum := by decide
  have hdescent : baseEnd_6946875 < baseStart_6946875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946876 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 2, 4]
def baseStart_6946876 : Nat := 118140960795 + 6946876 * 2 ^ 59
def prefixEnd_6946876 : Nat := 4983230072969 + 3 ^ 40 * 6946876 * 2
def baseEnd_6946876 : Nat := 1189028811727755849800635

theorem tailTrace_6946876 : CollatzResearch.WordTrace tailWord_6946876 prefixEnd_6946876 1189028811727755849800635 := by
  unfold tailWord_6946876
  simp only [CollatzResearch.WordTrace]
  refine ⟨126686691590331079404618241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168915588787108105872824321 126686691590331079404618241)
  ·
    refine ⟨95015018692748309553463681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126686691590331079404618241 95015018692748309553463681)
    ·
      refine ⟨71261264019561232165097761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95015018692748309553463681 71261264019561232165097761)
      ·
        refine ⟨53445948014670924123823321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71261264019561232165097761 53445948014670924123823321)
        ·
          refine ⟨40084461011003193092867491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53445948014670924123823321 40084461011003193092867491)
          ·
            refine ⟨60126691516504789639301237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40084461011003193092867491 60126691516504789639301237)
            ·
              refine ⟨5636877329672324028684491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 60126691516504789639301237 5636877329672324028684491)
              ·
                refine ⟨8455315994508486043026737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5636877329672324028684491 8455315994508486043026737)
                ·
                  refine ⟨6341486995881364532270053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8455315994508486043026737 6341486995881364532270053)
                  ·
                    refine ⟨1189028811727755849800635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6341486995881364532270053 1189028811727755849800635)
                    ·
                      rfl

theorem cell23_6946876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_6946876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946876 prefixEnd_6946876 := by exact prefixLift 6946876
  have htrace : WordTrace (prefixWord ++ tailWord_6946876) baseStart_6946876 baseEnd_6946876 := by
    simpa [prefixWord, tailWord_6946876, baseEnd_6946876] using wordTrace_append hprefix tailTrace_6946876
  have hstable : (prefixWord ++ tailWord_6946876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946876).length < 2 ^ (prefixWord ++ tailWord_6946876).sum := by decide
  have hdescent : baseEnd_6946876 < baseStart_6946876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946926 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_6946926 : Nat := 118140960795 + 6946926 * 2 ^ 59
def prefixEnd_6946926 : Nat := 4983230072969 + 3 ^ 40 * 6946926 * 2
def baseEnd_6946926 : Nat := 3567112109215992353776675

theorem tailTrace_6946926 : CollatzResearch.WordTrace tailWord_6946926 prefixEnd_6946926 3567112109215992353776675 := by
  unfold tailWord_6946926
  simp only [CollatzResearch.WordTrace]
  refine ⟨31671900853810127168569579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168916804553654011565704421 31671900853810127168569579)
  ·
    refine ⟨47507851280715190752854369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31671900853810127168569579 47507851280715190752854369)
    ·
      refine ⟨35630888460536393064640777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47507851280715190752854369 35630888460536393064640777)
      ·
        refine ⟨26723166345402294798480583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35630888460536393064640777 26723166345402294798480583)
        ·
          refine ⟨40084749518103442197720875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26723166345402294798480583 40084749518103442197720875)
          ·
            refine ⟨60127124277155163296581313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40084749518103442197720875 60127124277155163296581313)
            ·
              refine ⟨45095343207866372472435985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60127124277155163296581313 45095343207866372472435985)
              ·
                refine ⟨33821507405899779354326989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45095343207866372472435985 33821507405899779354326989)
                ·
                  refine ⟨12683065277212417257872621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33821507405899779354326989 12683065277212417257872621)
                  ·
                    refine ⟨4756149478954656471702233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12683065277212417257872621 4756149478954656471702233)
                    ·
                      refine ⟨3567112109215992353776675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756149478954656471702233 3567112109215992353776675)
                      ·
                        rfl

theorem cell23_6946926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_6946926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946926 prefixEnd_6946926 := by exact prefixLift 6946926
  have htrace : WordTrace (prefixWord ++ tailWord_6946926) baseStart_6946926 baseEnd_6946926 := by
    simpa [prefixWord, tailWord_6946926, baseEnd_6946926] using wordTrace_append hprefix tailTrace_6946926
  have hstable : (prefixWord ++ tailWord_6946926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946926).length < 2 ^ (prefixWord ++ tailWord_6946926).sum := by decide
  have hdescent : baseEnd_6946926 < baseStart_6946926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6946973 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_6946973 : Nat := 118140960795 + 6946973 * 2 ^ 59
def prefixEnd_6946973 : Nat := 4983230072969 + 3 ^ 40 * 6946973 * 2
def baseEnd_6946973 : Nat := 3567136242806753669888959

theorem tailTrace_6946973 : CollatzResearch.WordTrace tailWord_6946973 prefixEnd_6946973 3567136242806753669888959 := by
  unfold tailWord_6946973
  simp only [CollatzResearch.WordTrace]
  refine ⟨253376921061310744375517573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168917947374207162917011715 253376921061310744375517573)
  ·
    refine ⟨47508172698995764570409545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253376921061310744375517573 47508172698995764570409545)
    ·
      refine ⟨35631129524246823427807159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47508172698995764570409545 35631129524246823427807159)
      ·
        refine ⟨53446694286370235141710739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35631129524246823427807159 53446694286370235141710739)
        ·
          refine ⟨80170041429555352712566109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53446694286370235141710739 80170041429555352712566109)
          ·
            refine ⟨30063765536083257267212291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80170041429555352712566109 30063765536083257267212291)
            ·
              refine ⟨45095648304124885900818437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30063765536083257267212291 45095648304124885900818437)
              ·
                refine ⟨8455434057023416106403457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45095648304124885900818437 8455434057023416106403457)
                ·
                  refine ⟨6341575542767562079802593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8455434057023416106403457 6341575542767562079802593)
                  ·
                    refine ⟨4756181657075671559851945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6341575542767562079802593 4756181657075671559851945)
                    ·
                      refine ⟨3567136242806753669888959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756181657075671559851945 3567136242806753669888959)
                      ·
                        rfl

theorem cell23_6946973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_6946973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6946973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6946973 prefixEnd_6946973 := by exact prefixLift 6946973
  have htrace : WordTrace (prefixWord ++ tailWord_6946973) baseStart_6946973 baseEnd_6946973 := by
    simpa [prefixWord, tailWord_6946973, baseEnd_6946973] using wordTrace_append hprefix tailTrace_6946973
  have hstable : (prefixWord ++ tailWord_6946973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6946973).length < 2 ^ (prefixWord ++ tailWord_6946973).sum := by decide
  have hdescent : baseEnd_6946973 < baseStart_6946973 := by decide
  rcases family_descends (prefixWord ++ tailWord_6946973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947002 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_6947002 : Nat := 118140960795 + 6947002 * 2 ^ 59
def prefixEnd_6947002 : Nat := 4983230072969 + 3 ^ 40 * 6947002 * 2
def baseEnd_6947002 : Nat := 3567151133745734056426325

theorem tailTrace_6947002 : CollatzResearch.WordTrace tailWord_6947002 prefixEnd_6947002 3567151133745734056426325 := by
  unfold tailWord_6947002
  simp only [CollatzResearch.WordTrace]
  refine ⟨63344494694551420582080815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168918652518803788218882173 63344494694551420582080815)
  ·
    refine ⟨95016742041827130873121223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63344494694551420582080815 95016742041827130873121223)
    ·
      refine ⟨142525113062740696309681835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95016742041827130873121223 142525113062740696309681835)
      ·
        refine ⟨213787669594111044464522753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142525113062740696309681835 213787669594111044464522753)
        ·
          refine ⟨160340752195583283348392065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213787669594111044464522753 160340752195583283348392065)
          ·
            refine ⟨120255564146687462511294049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160340752195583283348392065 120255564146687462511294049)
            ·
              refine ⟨90191673110015596883470537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120255564146687462511294049 90191673110015596883470537)
              ·
                refine ⟨67643754832511697662602903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90191673110015596883470537 67643754832511697662602903)
                ·
                  refine ⟨101465632248767546493904355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67643754832511697662602903 101465632248767546493904355)
                  ·
                    refine ⟨152198448373151319740856533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 101465632248767546493904355 152198448373151319740856533)
                    ·
                      refine ⟨3567151133745734056426325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152198448373151319740856533 3567151133745734056426325)
                      ·
                        rfl

theorem cell23_6947002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_6947002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947002 prefixEnd_6947002 := by exact prefixLift 6947002
  have htrace : WordTrace (prefixWord ++ tailWord_6947002) baseStart_6947002 baseEnd_6947002 := by
    simpa [prefixWord, tailWord_6947002, baseEnd_6947002] using wordTrace_append hprefix tailTrace_6947002
  have hstable : (prefixWord ++ tailWord_6947002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947002).length < 2 ^ (prefixWord ++ tailWord_6947002).sum := by decide
  have hdescent : baseEnd_6947002 < baseStart_6947002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947049 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 3]
def baseStart_6947049 : Nat := 118140960795 + 6947049 * 2 ^ 59
def prefixEnd_6947049 : Nat := 4983230072969 + 3 ^ 40 * 6947049 * 2
def baseEnd_6947049 : Nat := 3567175267336495372538609

theorem tailTrace_6947049 : CollatzResearch.WordTrace tailWord_6947049 prefixEnd_6947049 3567175267336495372538609 := by
  unfold tailWord_6947049
  simp only [CollatzResearch.WordTrace]
  refine ⟨253379693009035409355284201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168919795339356939570189467 253379693009035409355284201)
  ·
    refine ⟨190034769756776557016463151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253379693009035409355284201 190034769756776557016463151)
    ·
      refine ⟨285052154635164835524694727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190034769756776557016463151 285052154635164835524694727)
      ·
        refine ⟨427578231952747253287042091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285052154635164835524694727 427578231952747253287042091)
        ·
          refine ⟨641367347929120879930563137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427578231952747253287042091 641367347929120879930563137)
          ·
            refine ⟨481025510946840659947922353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641367347929120879930563137 481025510946840659947922353)
            ·
              refine ⟨360769133210130494960941765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481025510946840659947922353 360769133210130494960941765)
              ·
                refine ⟨67644212476899467805176581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360769133210130494960941765 67644212476899467805176581)
                ·
                  refine ⟨12683289839418650213470609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67644212476899467805176581 12683289839418650213470609)
                  ·
                    refine ⟨9512467379563987660102957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12683289839418650213470609 9512467379563987660102957)
                    ·
                      refine ⟨3567175267336495372538609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9512467379563987660102957 3567175267336495372538609)
                      ·
                        rfl

theorem cell23_6947049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 2, 3].length) (baseStart_6947049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947049 prefixEnd_6947049 := by exact prefixLift 6947049
  have htrace : WordTrace (prefixWord ++ tailWord_6947049) baseStart_6947049 baseEnd_6947049 := by
    simpa [prefixWord, tailWord_6947049, baseEnd_6947049] using wordTrace_append hprefix tailTrace_6947049
  have hstable : (prefixWord ++ tailWord_6947049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947049).length < 2 ^ (prefixWord ++ tailWord_6947049).sum := by decide
  have hdescent : baseEnd_6947049 < baseStart_6947049 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947103 : List Nat := [1, 1, 2, 4, 3, 3, 2, 1, 6]
def baseStart_6947103 : Nat := 118140960795 + 6947103 * 2 ^ 59
def prefixEnd_6947103 : Nat := 4983230072969 + 3 ^ 40 * 6947103 * 2
def baseEnd_6947103 : Nat := 396355888365759795695929

theorem tailTrace_6947103 : CollatzResearch.WordTrace tailWord_6947103 prefixEnd_6947103 396355888365759795695929 := by
  unfold tailWord_6947103
  simp only [CollatzResearch.WordTrace]
  refine ⟨253381662550839776577749963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168921108367226517718499975 253381662550839776577749963)
  ·
    refine ⟨380072493826259664866624945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253381662550839776577749963 380072493826259664866624945)
    ·
      refine ⟨285054370369694748649968709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380072493826259664866624945 285054370369694748649968709)
      ·
        refine ⟨53447694444317765371869133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285054370369694748649968709 53447694444317765371869133)
        ·
          refine ⟨20042885416619162014450925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53447694444317765371869133 20042885416619162014450925)
          ·
            refine ⟨7516082031232185755419097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20042885416619162014450925 7516082031232185755419097)
            ·
              refine ⟨5637061523424139316564323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7516082031232185755419097 5637061523424139316564323)
              ·
                refine ⟨8455592285136208974846485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637061523424139316564323 8455592285136208974846485)
                ·
                  refine ⟨396355888365759795695929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8455592285136208974846485 396355888365759795695929)
                  ·
                    rfl

theorem cell23_6947103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 2, 1, 6].length) (baseStart_6947103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947103 prefixEnd_6947103 := by exact prefixLift 6947103
  have htrace : WordTrace (prefixWord ++ tailWord_6947103) baseStart_6947103 baseEnd_6947103 := by
    simpa [prefixWord, tailWord_6947103, baseEnd_6947103] using wordTrace_append hprefix tailTrace_6947103
  have hstable : (prefixWord ++ tailWord_6947103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947103).length < 2 ^ (prefixWord ++ tailWord_6947103).sum := by decide
  have hdescent : baseEnd_6947103 < baseStart_6947103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947116 : List Nat := [2, 2, 1, 1, 1, 3, 5, 2, 1, 5]
def baseStart_6947116 : Nat := 118140960795 + 6947116 * 2 ^ 59
def prefixEnd_6947116 : Nat := 4983230072969 + 3 ^ 40 * 6947116 * 2
def baseEnd_6947116 : Nat := 1189069890180115536800267

theorem tailTrace_6947116 : CollatzResearch.WordTrace tailWord_6947116 prefixEnd_6947116 1189069890180115536800267 := by
  unfold tailWord_6947116
  simp only [CollatzResearch.WordTrace]
  refine ⟨126691068349896339898986601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168921424466528453198648801 126691068349896339898986601)
  ·
    refine ⟨95018301262422254924239951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126691068349896339898986601 95018301262422254924239951)
    ·
      refine ⟨142527451893633382386359927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95018301262422254924239951 142527451893633382386359927)
      ·
        refine ⟨213791177840450073579539891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142527451893633382386359927 213791177840450073579539891)
        ·
          refine ⟨320686766760675110369309837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213791177840450073579539891 320686766760675110369309837)
          ·
            refine ⟨120257537535253166388491189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320686766760675110369309837 120257537535253166388491189)
            ·
              refine ⟨11274144143929984348921049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 120257537535253166388491189 11274144143929984348921049)
              ·
                refine ⟨8455608107947488261690787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11274144143929984348921049 8455608107947488261690787)
                ·
                  refine ⟨12683412161921232392536181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8455608107947488261690787 12683412161921232392536181)
                  ·
                    refine ⟨1189069890180115536800267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12683412161921232392536181 1189069890180115536800267)
                    ·
                      rfl

theorem cell23_6947116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 5].length) (baseStart_6947116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947116 prefixEnd_6947116 := by exact prefixLift 6947116
  have htrace : WordTrace (prefixWord ++ tailWord_6947116) baseStart_6947116 baseEnd_6947116 := by
    simpa [prefixWord, tailWord_6947116, baseEnd_6947116] using wordTrace_append hprefix tailTrace_6947116
  have hstable : (prefixWord ++ tailWord_6947116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947116).length < 2 ^ (prefixWord ++ tailWord_6947116).sum := by decide
  have hdescent : baseEnd_6947116 < baseStart_6947116 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947123 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 2, 3, 2]
def baseStart_6947123 : Nat := 118140960795 + 6947123 * 2 ^ 59
def prefixEnd_6947123 : Nat := 4983230072969 + 3 ^ 40 * 6947123 * 2
def baseEnd_6947123 : Nat := 3567213264904928083013269

theorem tailTrace_6947123 : CollatzResearch.WordTrace tailWord_6947123 prefixEnd_6947123 3567213264904928083013269 := by
  unfold tailWord_6947123
  simp only [CollatzResearch.WordTrace]
  refine ⟨253382392010767319993478023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168921594673844879995652015 253382392010767319993478023)
  ·
    refine ⟨380073588016150979990217035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253382392010767319993478023 380073588016150979990217035)
    ·
      refine ⟨570110382024226469985325553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380073588016150979990217035 570110382024226469985325553)
      ·
        refine ⟨427582786518169852488994165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570110382024226469985325553 427582786518169852488994165)
        ·
          refine ⟨40085886236078423670843203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427582786518169852488994165 40085886236078423670843203)
          ·
            refine ⟨60128829354117635506264805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40085886236078423670843203 60128829354117635506264805)
            ·
              refine ⟨11274155503897056657424651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 60128829354117635506264805 11274155503897056657424651)
              ·
                refine ⟨16911233255845584986136977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11274155503897056657424651 16911233255845584986136977)
                ·
                  refine ⟨12683424941884188739602733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16911233255845584986136977 12683424941884188739602733)
                  ·
                    refine ⟨4756284353206570777351025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12683424941884188739602733 4756284353206570777351025)
                    ·
                      refine ⟨3567213264904928083013269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756284353206570777351025 3567213264904928083013269)
                      ·
                        rfl

theorem cell23_6947123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3, 2].length) (baseStart_6947123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947123 prefixEnd_6947123 := by exact prefixLift 6947123
  have htrace : WordTrace (prefixWord ++ tailWord_6947123) baseStart_6947123 baseEnd_6947123 := by
    simpa [prefixWord, tailWord_6947123, baseEnd_6947123] using wordTrace_append hprefix tailTrace_6947123
  have hstable : (prefixWord ++ tailWord_6947123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947123).length < 2 ^ (prefixWord ++ tailWord_6947123).sum := by decide
  have hdescent : baseEnd_6947123 < baseStart_6947123 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947170 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 5, 2, 2]
def baseStart_6947170 : Nat := 118140960795 + 6947170 * 2 ^ 59
def prefixEnd_6947170 : Nat := 4983230072969 + 3 ^ 40 * 6947170 * 2
def baseEnd_6947170 : Nat := 3567237398495689399125553

theorem tailTrace_6947170 : CollatzResearch.WordTrace tailWord_6947170 prefixEnd_6947170 3567237398495689399125553 := by
  unfold tailWord_6947170
  simp only [CollatzResearch.WordTrace]
  refine ⟨63346026560399261755109741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168922737494398031346959309 63346026560399261755109741)
  ·
    refine ⟨23754759960149723158166153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63346026560399261755109741 23754759960149723158166153)
    ·
      refine ⟨17816069970112292368624615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23754759960149723158166153 17816069970112292368624615)
      ·
        refine ⟨26724104955168438552936923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17816069970112292368624615 26724104955168438552936923)
        ·
          refine ⟨40086157432752657829405385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26724104955168438552936923 40086157432752657829405385)
          ·
            refine ⟨30064618074564493372054039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40086157432752657829405385 30064618074564493372054039)
            ·
              refine ⟨45096927111846740058081059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30064618074564493372054039 45096927111846740058081059)
              ·
                refine ⟨67645390667770110087121589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45096927111846740058081059 67645390667770110087121589)
                ·
                  refine ⟨6341755375103447820667649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67645390667770110087121589 6341755375103447820667649)
                  ·
                    refine ⟨4756316531327585865500737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6341755375103447820667649 4756316531327585865500737)
                    ·
                      refine ⟨3567237398495689399125553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756316531327585865500737 3567237398495689399125553)
                      ·
                        rfl

theorem cell23_6947170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_6947170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947170 prefixEnd_6947170 := by exact prefixLift 6947170
  have htrace : WordTrace (prefixWord ++ tailWord_6947170) baseStart_6947170 baseEnd_6947170 := by
    simpa [prefixWord, tailWord_6947170, baseEnd_6947170] using wordTrace_append hprefix tailTrace_6947170
  have hstable : (prefixWord ++ tailWord_6947170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947170).length < 2 ^ (prefixWord ++ tailWord_6947170).sum := by decide
  have hdescent : baseEnd_6947170 < baseStart_6947170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947199 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_6947199 : Nat := 118140960795 + 6947199 * 2 ^ 59
def prefixEnd_6947199 : Nat := 4983230072969 + 3 ^ 40 * 6947199 * 2
def baseEnd_6947199 : Nat := 3567252289434669785662919

theorem tailTrace_6947199 : CollatzResearch.WordTrace tailWord_6947199 prefixEnd_6947199 3567252289434669785662919 := by
  unfold tailWord_6947199
  simp only [CollatzResearch.WordTrace]
  refine ⟨253385163958491984973244651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168923442638994656648829767 253385163958491984973244651)
  ·
    refine ⟨380077745937737977459866977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253385163958491984973244651 380077745937737977459866977)
    ·
      refine ⟨285058309453303483094900233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380077745937737977459866977 285058309453303483094900233)
      ·
        refine ⟨213793732089977612321175175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285058309453303483094900233 213793732089977612321175175)
        ·
          refine ⟨320690598134966418481762763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213793732089977612321175175 320690598134966418481762763)
          ·
            refine ⟨481035897202449627722644145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320690598134966418481762763 481035897202449627722644145)
            ·
              refine ⟨360776922901837220791983109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 481035897202449627722644145 360776922901837220791983109)
              ·
                refine ⟨67645673044094478898496833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360776922901837220791983109 67645673044094478898496833)
                ·
                  refine ⟨50734254783070859173872625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67645673044094478898496833 50734254783070859173872625)
                  ·
                    refine ⟨38050691087303144380404469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50734254783070859173872625 38050691087303144380404469)
                    ·
                      refine ⟨3567252289434669785662919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38050691087303144380404469 3567252289434669785662919)
                      ·
                        rfl

theorem cell23_6947199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_6947199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947199 prefixEnd_6947199 := by exact prefixLift 6947199
  have htrace : WordTrace (prefixWord ++ tailWord_6947199) baseStart_6947199 baseEnd_6947199 := by
    simpa [prefixWord, tailWord_6947199, baseEnd_6947199] using wordTrace_append hprefix tailTrace_6947199
  have hstable : (prefixWord ++ tailWord_6947199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947199).length < 2 ^ (prefixWord ++ tailWord_6947199).sum := by decide
  have hdescent : baseEnd_6947199 < baseStart_6947199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947317 : List Nat := [1, 3, 5, 1, 2, 1, 1, 4, 5]
def baseStart_6947317 : Nat := 118140960795 + 6947317 * 2 ^ 59
def prefixEnd_6947317 : Nat := 4983230072969 + 3 ^ 40 * 6947317 * 2
def baseEnd_6947317 : Nat := 396368097794655591554153

theorem tailTrace_6947317 : CollatzResearch.WordTrace tailWord_6947317 prefixEnd_6947317 396368097794655591554153 := by
  unfold tailWord_6947317
  simp only [CollatzResearch.WordTrace]
  refine ⟨253389467772064491126040205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168926311848042994084026803 253389467772064491126040205)
  ·
    refine ⟨95021050414524184172265077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253389467772064491126040205 95021050414524184172265077)
    ·
      refine ⟨8908223476361642266149851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95021050414524184172265077 8908223476361642266149851)
      ·
        refine ⟨13362335214542463399224777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8908223476361642266149851 13362335214542463399224777)
        ·
          refine ⟨10021751410906847549418583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13362335214542463399224777 10021751410906847549418583)
          ·
            refine ⟨15032627116360271324127875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10021751410906847549418583 15032627116360271324127875)
            ·
              refine ⟨22548940674540406986191813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15032627116360271324127875 22548940674540406986191813)
              ·
                refine ⟨4227926376476326309910965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22548940674540406986191813 4227926376476326309910965)
                ·
                  refine ⟨396368097794655591554153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4227926376476326309910965 396368097794655591554153)
                  ·
                    rfl

theorem cell23_6947317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 5].length) (baseStart_6947317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947317 prefixEnd_6947317 := by exact prefixLift 6947317
  have htrace : WordTrace (prefixWord ++ tailWord_6947317) baseStart_6947317 baseEnd_6947317 := by
    simpa [prefixWord, tailWord_6947317, baseEnd_6947317] using wordTrace_append hprefix tailTrace_6947317
  have hstable : (prefixWord ++ tailWord_6947317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947317).length < 2 ^ (prefixWord ++ tailWord_6947317).sum := by decide
  have hdescent : baseEnd_6947317 < baseStart_6947317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947333 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 1, 6, 2]
def baseStart_6947333 : Nat := 118140960795 + 6947333 * 2 ^ 59
def prefixEnd_6947333 : Nat := 4983230072969 + 3 ^ 40 * 6947333 * 2
def baseEnd_6947333 : Nat := 3567321095842372261387303

theorem tailTrace_6947333 : CollatzResearch.WordTrace tailWord_6947333 prefixEnd_6947333 3567321095842372261387303 := by
  unfold tailWord_6947333
  simp only [CollatzResearch.WordTrace]
  refine ⟨253390051340006525858622653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168926700893337683905748435 253390051340006525858622653)
  ·
    refine ⟨95021269252502447196983495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253390051340006525858622653 95021269252502447196983495)
    ·
      refine ⟨142531903878753670795475243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95021269252502447196983495 142531903878753670795475243)
      ·
        refine ⟨213797855818130506193212865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142531903878753670795475243 213797855818130506193212865)
        ·
          refine ⟨160348391863597879644909649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213797855818130506193212865 160348391863597879644909649)
          ·
            refine ⟨120261293897698409733682237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160348391863597879644909649 120261293897698409733682237)
            ·
              refine ⟨45097985211636903650130839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120261293897698409733682237 45097985211636903650130839)
              ·
                refine ⟨67646977817455355475196259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45097985211636903650130839 67646977817455355475196259)
                ·
                  refine ⟨101470466726183033212794389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67646977817455355475196259 101470466726183033212794389)
                  ·
                    refine ⟨4756428127789829681849737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 101470466726183033212794389 4756428127789829681849737)
                    ·
                      refine ⟨3567321095842372261387303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756428127789829681849737 3567321095842372261387303)
                      ·
                        rfl

theorem cell23_6947333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 1, 6, 2].length) (baseStart_6947333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947333 prefixEnd_6947333 := by exact prefixLift 6947333
  have htrace : WordTrace (prefixWord ++ tailWord_6947333) baseStart_6947333 baseEnd_6947333 := by
    simpa [prefixWord, tailWord_6947333, baseEnd_6947333] using wordTrace_append hprefix tailTrace_6947333
  have hstable : (prefixWord ++ tailWord_6947333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947333).length < 2 ^ (prefixWord ++ tailWord_6947333).sum := by decide
  have hdescent : baseEnd_6947333 < baseStart_6947333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947376 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_6947376 : Nat := 118140960795 + 6947376 * 2 ^ 59
def prefixEnd_6947376 : Nat := 4983230072969 + 3 ^ 40 * 6947376 * 2
def baseEnd_6947376 : Nat := 3567343175510515593149605

theorem tailTrace_6947376 : CollatzResearch.WordTrace tailWord_6947376 prefixEnd_6947376 3567343175510515593149605 := by
  unfold tailWord_6947376
  simp only [CollatzResearch.WordTrace]
  refine ⟨126695809839425372101218991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168927746452567162801625321 126695809839425372101218991)
  ·
    refine ⟨190043714759138058151828487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126695809839425372101218991 190043714759138058151828487)
    ·
      refine ⟨285065572138707087227742731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190043714759138058151828487 285065572138707087227742731)
      ·
        refine ⟨427598358208060630841614097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285065572138707087227742731 427598358208060630841614097)
        ·
          refine ⟨320698768656045473131210573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427598358208060630841614097 320698768656045473131210573)
          ·
            refine ⟨120262038246017052424203965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320698768656045473131210573 120262038246017052424203965)
            ·
              refine ⟨45098264342256394659076487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120262038246017052424203965 45098264342256394659076487)
              ·
                refine ⟨67647396513384591988614731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45098264342256394659076487 67647396513384591988614731)
                ·
                  refine ⟨101471094770076887982922097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67647396513384591988614731 101471094770076887982922097)
                  ·
                    refine ⟨76103321077557665987191573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 101471094770076887982922097 76103321077557665987191573)
                    ·
                      refine ⟨3567343175510515593149605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76103321077557665987191573 3567343175510515593149605)
                      ·
                        rfl

theorem cell23_6947376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_6947376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947376 prefixEnd_6947376 := by exact prefixLift 6947376
  have htrace : WordTrace (prefixWord ++ tailWord_6947376) baseStart_6947376 baseEnd_6947376 := by
    simpa [prefixWord, tailWord_6947376, baseEnd_6947376] using wordTrace_append hprefix tailTrace_6947376
  have hstable : (prefixWord ++ tailWord_6947376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947376).length < 2 ^ (prefixWord ++ tailWord_6947376).sum := by decide
  have hdescent : baseEnd_6947376 < baseStart_6947376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947403 : List Nat := [1, 1, 1, 1, 3, 1, 5, 4, 1, 5]
def baseStart_6947403 : Nat := 118140960795 + 6947403 * 2 ^ 59
def prefixEnd_6947403 : Nat := 4983230072969 + 3 ^ 40 * 6947403 * 2
def baseEnd_6947403 : Nat := 1189119013162728995837327

theorem tailTrace_6947403 : CollatzResearch.WordTrace tailWord_6947403 prefixEnd_6947403 1189119013162728995837327 := by
  unfold tailWord_6947403
  simp only [CollatzResearch.WordTrace]
  refine ⟨253392604449752927813670863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168928402966501951875780575 253392604449752927813670863)
  ·
    refine ⟨380088906674629391720506295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253392604449752927813670863 380088906674629391720506295)
    ·
      refine ⟨570133360011944087580759443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380088906674629391720506295 570133360011944087580759443)
      ·
        refine ⟨855200040017916131371139165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570133360011944087580759443 855200040017916131371139165)
        ·
          refine ⟨320700015006718549264177187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855200040017916131371139165 320700015006718549264177187)
          ·
            refine ⟨481050022510077823896265781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320700015006718549264177187 481050022510077823896265781)
            ·
              refine ⟨45098439610319795990274917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 481050022510077823896265781 45098439610319795990274917)
              ·
                refine ⟨8455957426934961748176547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45098439610319795990274917 8455957426934961748176547)
                ·
                  refine ⟨12683936140402442622264821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8455957426934961748176547 12683936140402442622264821)
                  ·
                    refine ⟨1189119013162728995837327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12683936140402442622264821 1189119013162728995837327)
                    ·
                      rfl

theorem cell23_6947403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 5].length) (baseStart_6947403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947403 prefixEnd_6947403 := by exact prefixLift 6947403
  have htrace : WordTrace (prefixWord ++ tailWord_6947403) baseStart_6947403 baseEnd_6947403 := by
    simpa [prefixWord, tailWord_6947403, baseEnd_6947403] using wordTrace_append hprefix tailTrace_6947403
  have hstable : (prefixWord ++ tailWord_6947403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947403).length < 2 ^ (prefixWord ++ tailWord_6947403).sum := by decide
  have hdescent : baseEnd_6947403 < baseStart_6947403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947410 : List Nat := [3, 2, 2, 1, 2, 1, 1, 3, 1, 5, 2]
def baseStart_6947410 : Nat := 118140960795 + 6947410 * 2 ^ 59
def prefixEnd_6947410 : Nat := 4983230072969 + 3 ^ 40 * 6947410 * 2
def baseEnd_6947410 : Nat := 3567360633852768460124449

theorem tailTrace_6947410 : CollatzResearch.WordTrace tailWord_6947410 prefixEnd_6947410 3567360633852768460124449 := by
  unfold tailWord_6947410
  simp only [CollatzResearch.WordTrace]
  refine ⟨63348214940181892002293921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168928573173818378672783789 63348214940181892002293921)
  ·
    refine ⟨47511161205136419001720441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63348214940181892002293921 47511161205136419001720441)
    ·
      refine ⟨35633370903852314251290331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47511161205136419001720441 35633370903852314251290331)
      ·
        refine ⟨53450056355778471376935497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35633370903852314251290331 53450056355778471376935497)
        ·
          refine ⟨40087542266833853532701623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53450056355778471376935497 40087542266833853532701623)
          ·
            refine ⟨60131313400250780299052435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40087542266833853532701623 60131313400250780299052435)
            ·
              refine ⟨90196970100376170448578653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60131313400250780299052435 90196970100376170448578653)
              ·
                refine ⟨33823863787641063918216995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90196970100376170448578653 33823863787641063918216995)
                ·
                  refine ⟨50735795681461595877325493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33823863787641063918216995 50735795681461595877325493)
                  ·
                    refine ⟨4756480845137024613499265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50735795681461595877325493 4756480845137024613499265)
                    ·
                      refine ⟨3567360633852768460124449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756480845137024613499265 3567360633852768460124449)
                      ·
                        rfl

theorem cell23_6947410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 3, 1, 5, 2].length) (baseStart_6947410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947410 prefixEnd_6947410 := by exact prefixLift 6947410
  have htrace : WordTrace (prefixWord ++ tailWord_6947410) baseStart_6947410 baseEnd_6947410 := by
    simpa [prefixWord, tailWord_6947410, baseEnd_6947410] using wordTrace_append hprefix tailTrace_6947410
  have hstable : (prefixWord ++ tailWord_6947410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947410).length < 2 ^ (prefixWord ++ tailWord_6947410).sum := by decide
  have hdescent : baseEnd_6947410 < baseStart_6947410 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947457 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 5, 2, 2]
def baseStart_6947457 : Nat := 118140960795 + 6947457 * 2 ^ 59
def prefixEnd_6947457 : Nat := 4983230072969 + 3 ^ 40 * 6947457 * 2
def baseEnd_6947457 : Nat := 3567384767443529776236733

theorem tailTrace_6947457 : CollatzResearch.WordTrace tailWord_6947457 prefixEnd_6947457 3567384767443529776236733 := by
  unfold tailWord_6947457
  simp only [CollatzResearch.WordTrace]
  refine ⟨253394573991557295036136625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168929715994371530024091083 253394573991557295036136625)
  ·
    refine ⟨190045930493667971277102469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253394573991557295036136625 190045930493667971277102469)
    ·
      refine ⟨35633611967562744614456713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190045930493667971277102469 35633611967562744614456713)
      ·
        refine ⟨26725208975672058460842535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35633611967562744614456713 26725208975672058460842535)
        ·
          refine ⟨40087813463508087691263803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26725208975672058460842535 40087813463508087691263803)
          ·
            refine ⟨60131720195262131536895705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40087813463508087691263803 60131720195262131536895705)
            ·
              refine ⟨45098790146446598652671779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60131720195262131536895705 45098790146446598652671779)
              ·
                refine ⟨67648185219669897979007669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45098790146446598652671779 67648185219669897979007669)
                ·
                  refine ⟨6342017364344052935531969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67648185219669897979007669 6342017364344052935531969)
                  ·
                    refine ⟨4756513023258039701648977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6342017364344052935531969 4756513023258039701648977)
                    ·
                      refine ⟨3567384767443529776236733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756513023258039701648977 3567384767443529776236733)
                      ·
                        rfl

theorem cell23_6947457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_6947457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947457 prefixEnd_6947457 := by exact prefixLift 6947457
  have htrace : WordTrace (prefixWord ++ tailWord_6947457) baseStart_6947457 baseEnd_6947457 := by
    simpa [prefixWord, tailWord_6947457, baseEnd_6947457] using wordTrace_append hprefix tailTrace_6947457
  have hstable : (prefixWord ++ tailWord_6947457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947457).length < 2 ^ (prefixWord ++ tailWord_6947457).sum := by decide
  have hdescent : baseEnd_6947457 < baseStart_6947457 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947470 : List Nat := [4, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_6947470 : Nat := 118140960795 + 6947470 * 2 ^ 59
def prefixEnd_6947470 : Nat := 4983230072969 + 3 ^ 40 * 6947470 * 2
def baseEnd_6947470 : Nat := 3567391442692038225374173

theorem tailTrace_6947470 : CollatzResearch.WordTrace tailWord_6947470 prefixEnd_6947470 3567391442692038225374173 := by
  unfold tailWord_6947470
  simp only [CollatzResearch.WordTrace]
  refine ⟨31674381017563774782044983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168930032093673465504239909 31674381017563774782044983)
  ·
    refine ⟨47511571526345662173067475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31674381017563774782044983 47511571526345662173067475)
    ·
      refine ⟨71267357289518493259601213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47511571526345662173067475 71267357289518493259601213)
      ·
        refine ⟨26725258983569434972350455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71267357289518493259601213 26725258983569434972350455)
        ·
          refine ⟨40087888475354152458525683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26725258983569434972350455 40087888475354152458525683)
          ·
            refine ⟨60131832713031228687788525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40087888475354152458525683 60131832713031228687788525)
            ·
              refine ⟨22549437267386710757920697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60131832713031228687788525 22549437267386710757920697)
              ·
                refine ⟨16912077950540033068440523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22549437267386710757920697 16912077950540033068440523)
                ·
                  refine ⟨25368116925810049602660785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16912077950540033068440523 25368116925810049602660785)
                  ·
                    refine ⟨19026087694357537201995589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25368116925810049602660785 19026087694357537201995589)
                    ·
                      refine ⟨3567391442692038225374173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19026087694357537201995589 3567391442692038225374173)
                      ·
                        rfl

theorem cell23_6947470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_6947470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947470 prefixEnd_6947470 := by exact prefixLift 6947470
  have htrace : WordTrace (prefixWord ++ tailWord_6947470) baseStart_6947470 baseEnd_6947470 := by
    simpa [prefixWord, tailWord_6947470, baseEnd_6947470] using wordTrace_append hprefix tailTrace_6947470
  have hstable : (prefixWord ++ tailWord_6947470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947470).length < 2 ^ (prefixWord ++ tailWord_6947470).sum := by decide
  have hdescent : baseEnd_6947470 < baseStart_6947470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947474 : List Nat := [3, 2, 3, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_6947474 : Nat := 118140960795 + 6947474 * 2 ^ 59
def prefixEnd_6947474 : Nat := 4983230072969 + 3 ^ 40 * 6947474 * 2
def baseEnd_6947474 : Nat := 3567393496614656209724155

theorem tailTrace_6947474 : CollatzResearch.WordTrace tailWord_6947474 prefixEnd_6947474 3567393496614656209724155 := by
  unfold tailWord_6947474
  simp only [CollatzResearch.WordTrace]
  refine ⟨63348798508123926734876369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168930129354997137959670317 63348798508123926734876369)
  ·
    refine ⟨47511598881092945051157277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63348798508123926734876369 47511598881092945051157277)
    ·
      refine ⟨17816849580409854394183979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47511598881092945051157277 17816849580409854394183979)
      ·
        refine ⟨26725274370614781591275969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17816849580409854394183979 26725274370614781591275969)
        ·
          refine ⟨20043955777961086193456977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26725274370614781591275969 20043955777961086193456977)
          ·
            refine ⟨15032966833470814645092733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20043955777961086193456977 15032966833470814645092733)
            ·
              refine ⟨5637362562551555491909775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15032966833470814645092733 5637362562551555491909775)
              ·
                refine ⟨8456043843827333237864663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637362562551555491909775 8456043843827333237864663)
                ·
                  refine ⟨12684065765740999856796995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456043843827333237864663 12684065765740999856796995)
                  ·
                    refine ⟨19026098648611499785195493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12684065765740999856796995 19026098648611499785195493)
                    ·
                      refine ⟨3567393496614656209724155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19026098648611499785195493 3567393496614656209724155)
                      ·
                        rfl

theorem cell23_6947474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_6947474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947474 prefixEnd_6947474 := by exact prefixLift 6947474
  have htrace : WordTrace (prefixWord ++ tailWord_6947474) baseStart_6947474 baseEnd_6947474 := by
    simpa [prefixWord, tailWord_6947474, baseEnd_6947474] using wordTrace_append hprefix tailTrace_6947474
  have hstable : (prefixWord ++ tailWord_6947474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947474).length < 2 ^ (prefixWord ++ tailWord_6947474).sum := by decide
  have hdescent : baseEnd_6947474 < baseStart_6947474 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947507 : List Nat := [1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 3]
def baseStart_6947507 : Nat := 118140960795 + 6947507 * 2 ^ 59
def prefixEnd_6947507 : Nat := 4983230072969 + 3 ^ 40 * 6947507 * 2
def baseEnd_6947507 : Nat := 3567410441476254580611503

theorem tailTrace_6947507 : CollatzResearch.WordTrace tailWord_6947507 prefixEnd_6947507 3567410441476254580611503 := by
  unfold tailWord_6947507
  simp only [CollatzResearch.WordTrace]
  refine ⟨253396397641376153575456775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168930931760917435716971183 253396397641376153575456775)
  ·
    refine ⟨380094596462064230363185163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253396397641376153575456775 380094596462064230363185163)
    ·
      refine ⟨570141894693096345544777745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380094596462064230363185163 570141894693096345544777745)
      ·
        refine ⟨427606421019822259158583309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570141894693096345544777745 427606421019822259158583309)
        ·
          refine ⟨160352407882433347184468741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427606421019822259158583309 160352407882433347184468741)
          ·
            refine ⟨30066076477956252597087889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160352407882433347184468741 30066076477956252597087889)
            ·
              refine ⟨22549557358467189447815917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30066076477956252597087889 22549557358467189447815917)
              ·
                refine ⟨8456084009425196042930969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22549557358467189447815917 8456084009425196042930969)
                ·
                  refine ⟨6342063007068897032198227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456084009425196042930969 6342063007068897032198227)
                  ·
                    refine ⟨9513094510603345548297341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6342063007068897032198227 9513094510603345548297341)
                    ·
                      refine ⟨3567410441476254580611503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9513094510603345548297341 3567410441476254580611503)
                      ·
                        rfl

theorem cell23_6947507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 3, 2, 1, 3].length) (baseStart_6947507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947507 prefixEnd_6947507 := by exact prefixLift 6947507
  have htrace : WordTrace (prefixWord ++ tailWord_6947507) baseStart_6947507 baseEnd_6947507 := by
    simpa [prefixWord, tailWord_6947507, baseEnd_6947507] using wordTrace_append hprefix tailTrace_6947507
  have hstable : (prefixWord ++ tailWord_6947507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947507).length < 2 ^ (prefixWord ++ tailWord_6947507).sum := by decide
  have hdescent : baseEnd_6947507 < baseStart_6947507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947513 : List Nat := [1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 4]
def baseStart_6947513 : Nat := 118140960795 + 6947513 * 2 ^ 59
def prefixEnd_6947513 : Nat := 4983230072969 + 3 ^ 40 * 6947513 * 2
def baseEnd_6947513 : Nat := 3567413522360181557136475

theorem tailTrace_6947513 : CollatzResearch.WordTrace tailWord_6947513 prefixEnd_6947513 3567413522360181557136475 := by
  unfold tailWord_6947513
  simp only [CollatzResearch.WordTrace]
  refine ⟨253396616479354416600175193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168931077652902944400116795 253396616479354416600175193)
  ·
    refine ⟨190047462359515812450131395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253396616479354416600175193 190047462359515812450131395)
    ·
      refine ⟨285071193539273718675197093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190047462359515812450131395 285071193539273718675197093)
      ·
        refine ⟨53450848788613822251599455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285071193539273718675197093 53450848788613822251599455)
        ·
          refine ⟨80176273182920733377399183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53450848788613822251599455 80176273182920733377399183)
          ·
            refine ⟨120264409774381100066098775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80176273182920733377399183 120264409774381100066098775)
            ·
              refine ⟨180396614661571650099148163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120264409774381100066098775 180396614661571650099148163)
              ·
                refine ⟨270594921992357475148722245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180396614661571650099148163 270594921992357475148722245)
                ·
                  refine ⟨50736547873567026590385421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270594921992357475148722245 50736547873567026590385421)
                  ·
                    refine ⟨19026205452587634971394533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50736547873567026590385421 19026205452587634971394533)
                    ·
                      refine ⟨3567413522360181557136475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19026205452587634971394533 3567413522360181557136475)
                      ·
                        rfl

theorem cell23_6947513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_6947513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947513 prefixEnd_6947513 := by exact prefixLift 6947513
  have htrace : WordTrace (prefixWord ++ tailWord_6947513) baseStart_6947513 baseEnd_6947513 := by
    simpa [prefixWord, tailWord_6947513, baseEnd_6947513] using wordTrace_append hprefix tailTrace_6947513
  have hstable : (prefixWord ++ tailWord_6947513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947513).length < 2 ^ (prefixWord ++ tailWord_6947513).sum := by decide
  have hdescent : baseEnd_6947513 < baseStart_6947513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947517 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_6947517 : Nat := 118140960795 + 6947517 * 2 ^ 59
def prefixEnd_6947517 : Nat := 4983230072969 + 3 ^ 40 * 6947517 * 2
def baseEnd_6947517 : Nat := 3567415576282799541486457

theorem tailTrace_6947517 : CollatzResearch.WordTrace tailWord_6947517 prefixEnd_6947517 3567415576282799541486457 := by
  unfold tailWord_6947517
  simp only [CollatzResearch.WordTrace]
  refine ⟨253396762371339925283320805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168931174914226616855547203 253396762371339925283320805)
  ·
    refine ⟨47511892944626235990622651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253396762371339925283320805 47511892944626235990622651)
    ·
      refine ⟨71267839416939353985933977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47511892944626235990622651 71267839416939353985933977)
      ·
        refine ⟨53450879562704515489450483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71267839416939353985933977 53450879562704515489450483)
        ·
          refine ⟨80176319344056773234175725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53450879562704515489450483 80176319344056773234175725)
          ·
            refine ⟨30066119754021289962815897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80176319344056773234175725 30066119754021289962815897)
            ·
              refine ⟨22549589815515967472111923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30066119754021289962815897 22549589815515967472111923)
              ·
                refine ⟨33824384723273951208167885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22549589815515967472111923 33824384723273951208167885)
                ·
                  refine ⟨12684144271227731703062957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33824384723273951208167885 12684144271227731703062957)
                  ·
                    refine ⟨4756554101710399388648609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12684144271227731703062957 4756554101710399388648609)
                    ·
                      refine ⟨3567415576282799541486457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756554101710399388648609 3567415576282799541486457)
                      ·
                        rfl

theorem cell23_6947517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_6947517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947517 prefixEnd_6947517 := by exact prefixLift 6947517
  have htrace : WordTrace (prefixWord ++ tailWord_6947517) baseStart_6947517 baseEnd_6947517 := by
    simpa [prefixWord, tailWord_6947517, baseEnd_6947517] using wordTrace_append hprefix tailTrace_6947517
  have hstable : (prefixWord ++ tailWord_6947517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947517).length < 2 ^ (prefixWord ++ tailWord_6947517).sum := by decide
  have hdescent : baseEnd_6947517 < baseStart_6947517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947534 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_6947534 : Nat := 118140960795 + 6947534 * 2 ^ 59
def prefixEnd_6947534 : Nat := 4983230072969 + 3 ^ 40 * 6947534 * 2
def baseEnd_6947534 : Nat := 3567424305453925974973879

theorem tailTrace_6947534 : CollatzResearch.WordTrace tailWord_6947534 prefixEnd_6947534 3567424305453925974973879 := by
  unfold tailWord_6947534
  simp only [CollatzResearch.WordTrace]
  refine ⟨31674672801534792148336207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168931588274852224791126437 31674672801534792148336207)
  ·
    refine ⟨47512009202302188222504311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31674672801534792148336207 47512009202302188222504311)
    ·
      refine ⟨71268013803453282333756467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47512009202302188222504311 71268013803453282333756467)
      ·
        refine ⟨106902020705179923500634701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71268013803453282333756467 106902020705179923500634701)
        ·
          refine ⟨40088257764442471312738013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106902020705179923500634701 40088257764442471312738013)
          ·
            refine ⟨15033096661665926742276755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40088257764442471312738013 15033096661665926742276755)
            ·
              refine ⟨22549644992498890113415133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15033096661665926742276755 22549644992498890113415133)
              ·
                refine ⟨8456116872187083792530675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22549644992498890113415133 8456116872187083792530675)
                ·
                  refine ⟨12684175308280625688796013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456116872187083792530675 12684175308280625688796013)
                  ·
                    refine ⟨4756565740605234633298505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12684175308280625688796013 4756565740605234633298505)
                    ·
                      refine ⟨3567424305453925974973879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756565740605234633298505 3567424305453925974973879)
                      ·
                        rfl

theorem cell23_6947534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_6947534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947534 prefixEnd_6947534 := by exact prefixLift 6947534
  have htrace : WordTrace (prefixWord ++ tailWord_6947534) baseStart_6947534 baseEnd_6947534 := by
    simpa [prefixWord, tailWord_6947534, baseEnd_6947534] using wordTrace_append hprefix tailTrace_6947534
  have hstable : (prefixWord ++ tailWord_6947534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947534).length < 2 ^ (prefixWord ++ tailWord_6947534).sum := by decide
  have hdescent : baseEnd_6947534 < baseStart_6947534 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947570 : List Nat := [3, 2, 1, 3, 1, 2, 2, 2, 7]
def baseStart_6947570 : Nat := 118140960795 + 6947570 * 2 ^ 59
def prefixEnd_6947570 : Nat := 4983230072969 + 3 ^ 40 * 6947570 * 2
def baseEnd_6947570 : Nat := 396382532306387537124857

theorem tailTrace_6947570 : CollatzResearch.WordTrace tailWord_6947570 prefixEnd_6947570 396382532306387537124857 := by
  unfold tailWord_6947570
  simp only [CollatzResearch.WordTrace]
  refine ⟨63349673860036978833750041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168932463626765276890000109 63349673860036978833750041)
  ·
    refine ⟨47512255395027734125312531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63349673860036978833750041 47512255395027734125312531)
    ·
      refine ⟨71268383092541601187968797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47512255395027734125312531 71268383092541601187968797)
      ·
        refine ⟨26725643659703100445488299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71268383092541601187968797 26725643659703100445488299)
        ·
          refine ⟨40088465489554650668232449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26725643659703100445488299 40088465489554650668232449)
          ·
            refine ⟨30066349117165988001174337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40088465489554650668232449 30066349117165988001174337)
            ·
              refine ⟨22549761837874491000880753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30066349117165988001174337 22549761837874491000880753)
              ·
                refine ⟨16912321378405868250660565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22549761837874491000880753 16912321378405868250660565)
                ·
                  refine ⟨396382532306387537124857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16912321378405868250660565 396382532306387537124857)
                  ·
                    rfl

theorem cell23_6947570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_6947570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947570 prefixEnd_6947570 := by exact prefixLift 6947570
  have htrace : WordTrace (prefixWord ++ tailWord_6947570) baseStart_6947570 baseEnd_6947570 := by
    simpa [prefixWord, tailWord_6947570, baseEnd_6947570] using wordTrace_append hprefix tailTrace_6947570
  have hstable : (prefixWord ++ tailWord_6947570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947570).length < 2 ^ (prefixWord ++ tailWord_6947570).sum := by decide
  have hdescent : baseEnd_6947570 < baseStart_6947570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947610 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_6947610 : Nat := 118140960795 + 6947610 * 2 ^ 59
def prefixEnd_6947610 : Nat := 4983230072969 + 3 ^ 40 * 6947610 * 2
def baseEnd_6947610 : Nat := 3567463329983667677623529

theorem tailTrace_6947610 : CollatzResearch.WordTrace tailWord_6947610 prefixEnd_6947610 3567463329983667677623529 := by
  unfold tailWord_6947610
  simp only [CollatzResearch.WordTrace]
  refine ⟨63350038590000750541614071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168933436240002001444304189 63350038590000750541614071)
  ·
    refine ⟨95025057885001125812421107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63350038590000750541614071 95025057885001125812421107)
    ·
      refine ⟨142537586827501688718631661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95025057885001125812421107 142537586827501688718631661)
      ·
        refine ⟨53451595060313133269486873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142537586827501688718631661 53451595060313133269486873)
        ·
          refine ⟨40088696295234849952115155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53451595060313133269486873 40088696295234849952115155)
          ·
            refine ⟨60133044442852274928172733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40088696295234849952115155 60133044442852274928172733)
            ·
              refine ⟨22549891666069603098064775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60133044442852274928172733 22549891666069603098064775)
              ·
                refine ⟨33824837499104404647097163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22549891666069603098064775 33824837499104404647097163)
                ·
                  refine ⟨50737256248656606970645745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33824837499104404647097163 50737256248656606970645745)
                  ·
                    refine ⟨38052942186492455227984309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50737256248656606970645745 38052942186492455227984309)
                    ·
                      refine ⟨3567463329983667677623529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38052942186492455227984309 3567463329983667677623529)
                      ·
                        rfl

theorem cell23_6947610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_6947610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947610 prefixEnd_6947610 := by exact prefixLift 6947610
  have htrace : WordTrace (prefixWord ++ tailWord_6947610) baseStart_6947610 baseEnd_6947610 := by
    simpa [prefixWord, tailWord_6947610, baseEnd_6947610] using wordTrace_append hprefix tailTrace_6947610
  have hstable : (prefixWord ++ tailWord_6947610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947610).length < 2 ^ (prefixWord ++ tailWord_6947610).sum := by decide
  have hdescent : baseEnd_6947610 < baseStart_6947610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947637 : List Nat := [1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_6947637 : Nat := 118140960795 + 6947637 * 2 ^ 59
def prefixEnd_6947637 : Nat := 4983230072969 + 3 ^ 40 * 6947637 * 2
def baseEnd_6947637 : Nat := 3567477193961339071985905

theorem tailTrace_6947637 : CollatzResearch.WordTrace tailWord_6947637 prefixEnd_6947637 3567477193961339071985905 := by
  unfold tailWord_6947637
  simp only [CollatzResearch.WordTrace]
  refine ⟨253401139130905185777689165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168934092753936790518459443 253401139130905185777689165)
  ·
    refine ⟨95025427174089444666633437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253401139130905185777689165 95025427174089444666633437)
    ·
      refine ⟨35634535190283541749987539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95025427174089444666633437 35634535190283541749987539)
      ·
        refine ⟨53451802785425312624981309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35634535190283541749987539 53451802785425312624981309)
        ·
          refine ⟨20044426044534492234367991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53451802785425312624981309 20044426044534492234367991)
          ·
            refine ⟨30066639066801738351551987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20044426044534492234367991 30066639066801738351551987)
            ·
              refine ⟨45099958600202607527327981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30066639066801738351551987 45099958600202607527327981)
              ·
                refine ⟨16912484475075977822747993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45099958600202607527327981 16912484475075977822747993)
                ·
                  refine ⟨12684363356306983367060995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16912484475075977822747993 12684363356306983367060995)
                  ·
                    refine ⟨19026545034460475050591493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12684363356306983367060995 19026545034460475050591493)
                    ·
                      refine ⟨3567477193961339071985905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19026545034460475050591493 3567477193961339071985905)
                      ·
                        rfl

theorem cell23_6947637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_6947637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947637 prefixEnd_6947637 := by exact prefixLift 6947637
  have htrace : WordTrace (prefixWord ++ tailWord_6947637) baseStart_6947637 baseEnd_6947637 := by
    simpa [prefixWord, tailWord_6947637, baseEnd_6947637] using wordTrace_append hprefix tailTrace_6947637
  have hstable : (prefixWord ++ tailWord_6947637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947637).length < 2 ^ (prefixWord ++ tailWord_6947637).sum := by decide
  have hdescent : baseEnd_6947637 < baseStart_6947637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947657 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 3]
def baseStart_6947657 : Nat := 118140960795 + 6947657 * 2 ^ 59
def prefixEnd_6947657 : Nat := 4983230072969 + 3 ^ 40 * 6947657 * 2
def baseEnd_6947657 : Nat := 3567487463574428993735813

theorem tailTrace_6947657 : CollatzResearch.WordTrace tailWord_6947657 prefixEnd_6947657 3567487463574428993735813 := by
  unfold tailWord_6947657
  simp only [CollatzResearch.WordTrace]
  refine ⟨253401868590832729193417225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168934579060555152795611483 253401868590832729193417225)
  ·
    refine ⟨190051401443124546895062919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253401868590832729193417225 190051401443124546895062919)
    ·
      refine ⟨285077102164686820342594379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190051401443124546895062919 285077102164686820342594379)
      ·
        refine ⟨427615653247030230513891569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285077102164686820342594379 427615653247030230513891569)
        ·
          refine ⟨320711739935272672885418677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427615653247030230513891569 320711739935272672885418677)
          ·
            refine ⟨30066725618931813083008001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 320711739935272672885418677 30066725618931813083008001)
            ·
              refine ⟨22550044214198859812256001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30066725618931813083008001 22550044214198859812256001)
              ·
                refine ⟨16912533160649144859192001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22550044214198859812256001 16912533160649144859192001)
                ·
                  refine ⟨12684399870486858644394001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16912533160649144859192001 12684399870486858644394001)
                  ·
                    refine ⟨9513299902865143983295501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12684399870486858644394001 9513299902865143983295501)
                    ·
                      refine ⟨3567487463574428993735813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9513299902865143983295501 3567487463574428993735813)
                      ·
                        rfl

theorem cell23_6947657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 2, 3].length) (baseStart_6947657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947657 prefixEnd_6947657 := by exact prefixLift 6947657
  have htrace : WordTrace (prefixWord ++ tailWord_6947657) baseStart_6947657 baseEnd_6947657 := by
    simpa [prefixWord, tailWord_6947657, baseEnd_6947657] using wordTrace_append hprefix tailTrace_6947657
  have hstable : (prefixWord ++ tailWord_6947657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947657).length < 2 ^ (prefixWord ++ tailWord_6947657).sum := by decide
  have hdescent : baseEnd_6947657 < baseStart_6947657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947721 : List Nat := [1, 2, 1, 1, 5, 2, 2, 4, 1, 1, 3]
def baseStart_6947721 : Nat := 118140960795 + 6947721 * 2 ^ 59
def prefixEnd_6947721 : Nat := 4983230072969 + 3 ^ 40 * 6947721 * 2
def baseEnd_6947721 : Nat := 3567520326336316743335519

theorem tailTrace_6947721 : CollatzResearch.WordTrace tailWord_6947721 prefixEnd_6947721 3567520326336316743335519 := by
  unfold tailWord_6947721
  simp only [CollatzResearch.WordTrace]
  refine ⟨253404202862600868123747017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168936135241733912082498011 253404202862600868123747017)
  ·
    refine ⟨190053152146950651092810263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253404202862600868123747017 190053152146950651092810263)
    ·
      refine ⟨285079728220425976639215395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190053152146950651092810263 285079728220425976639215395)
      ·
        refine ⟨427619592330638964958823093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285079728220425976639215395 427619592330638964958823093)
        ·
          refine ⟨40089336780997402964889665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 427619592330638964958823093 40089336780997402964889665)
          ·
            refine ⟨30067002585748052223667249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40089336780997402964889665 30067002585748052223667249)
            ·
              refine ⟨22550251939311039167750437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30067002585748052223667249 22550251939311039167750437)
              ·
                refine ⟨4228172238620819843953207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22550251939311039167750437 4228172238620819843953207)
                ·
                  refine ⟨6342258357931229765929811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228172238620819843953207 6342258357931229765929811)
                  ·
                    refine ⟨9513387536896844648894717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6342258357931229765929811 9513387536896844648894717)
                    ·
                      refine ⟨3567520326336316743335519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9513387536896844648894717 3567520326336316743335519)
                      ·
                        rfl

theorem cell23_6947721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 4, 1, 1, 3].length) (baseStart_6947721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947721 prefixEnd_6947721 := by exact prefixLift 6947721
  have htrace : WordTrace (prefixWord ++ tailWord_6947721) baseStart_6947721 baseEnd_6947721 := by
    simpa [prefixWord, tailWord_6947721, baseEnd_6947721] using wordTrace_append hprefix tailTrace_6947721
  have hstable : (prefixWord ++ tailWord_6947721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947721).length < 2 ^ (prefixWord ++ tailWord_6947721).sum := by decide
  have hdescent : baseEnd_6947721 < baseStart_6947721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947747 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 3]
def baseStart_6947747 : Nat := 118140960795 + 6947747 * 2 ^ 59
def prefixEnd_6947747 : Nat := 4983230072969 + 3 ^ 40 * 6947747 * 2
def baseEnd_6947747 : Nat := 3567533676833333641610399

theorem tailTrace_6947747 : CollatzResearch.WordTrace tailWord_6947747 prefixEnd_6947747 3567533676833333641610399 := by
  unfold tailWord_6947747
  simp only [CollatzResearch.WordTrace]
  refine ⟨253405151160506674564193495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168936767440337783042795663 253405151160506674564193495)
  ·
    refine ⟨380107726740760011846290243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253405151160506674564193495 380107726740760011846290243)
    ·
      refine ⟨570161590111140017769435365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380107726740760011846290243 570161590111140017769435365)
      ·
        refine ⟨106905298145838753331769131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 570161590111140017769435365 106905298145838753331769131)
        ·
          refine ⟨160357947218758129997653697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106905298145838753331769131 160357947218758129997653697)
          ·
            refine ⟨120268460414068597498240273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160357947218758129997653697 120268460414068597498240273)
            ·
              refine ⟨90201345310551448123680205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120268460414068597498240273 90201345310551448123680205)
              ·
                refine ⟨33825504491456793046380077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 90201345310551448123680205 33825504491456793046380077)
                ·
                  refine ⟨12684564184296297392392529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33825504491456793046380077 12684564184296297392392529)
                  ·
                    refine ⟨9513423138222223044294397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12684564184296297392392529 9513423138222223044294397)
                    ·
                      refine ⟨3567533676833333641610399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9513423138222223044294397 3567533676833333641610399)
                      ·
                        rfl

theorem cell23_6947747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_6947747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947747 prefixEnd_6947747 := by exact prefixLift 6947747
  have htrace : WordTrace (prefixWord ++ tailWord_6947747) baseStart_6947747 baseEnd_6947747 := by
    simpa [prefixWord, tailWord_6947747, baseEnd_6947747] using wordTrace_append hprefix tailTrace_6947747
  have hstable : (prefixWord ++ tailWord_6947747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947747).length < 2 ^ (prefixWord ++ tailWord_6947747).sum := by decide
  have hdescent : baseEnd_6947747 < baseStart_6947747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947798 : List Nat := [5, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3]
def baseStart_6947798 : Nat := 118140960795 + 6947798 * 2 ^ 59
def prefixEnd_6947798 : Nat := 4983230072969 + 3 ^ 40 * 6947798 * 2
def baseEnd_6947798 : Nat := 3567559864346712942072665

theorem tailTrace_6947798 : CollatzResearch.WordTrace tailWord_6947798 prefixEnd_6947798 3567559864346712942072665 := by
  unfold tailWord_6947798
  simp only [CollatzResearch.WordTrace]
  refine ⟨15837938205207619392143753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 168938007522214606849533365 15837938205207619392143753)
  ·
    refine ⟨11878453653905714544107815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15837938205207619392143753 11878453653905714544107815)
    ·
      refine ⟨17817680480858571816161723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11878453653905714544107815 17817680480858571816161723)
      ·
        refine ⟨26726520721287857724242585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17817680480858571816161723 26726520721287857724242585)
        ·
          refine ⟨20044890540965893293181939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26726520721287857724242585 20044890540965893293181939)
          ·
            refine ⟨30067335811448839939772909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20044890540965893293181939 30067335811448839939772909)
            ·
              refine ⟨11275250929293314977414841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30067335811448839939772909 11275250929293314977414841)
              ·
                refine ⟨8456438196969986233061131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11275250929293314977414841 8456438196969986233061131)
                ·
                  refine ⟨12684657295454979349591697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456438196969986233061131 12684657295454979349591697)
                  ·
                    refine ⟨9513492971591234512193773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12684657295454979349591697 9513492971591234512193773)
                    ·
                      refine ⟨3567559864346712942072665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9513492971591234512193773 3567559864346712942072665)
                      ·
                        rfl

theorem cell23_6947798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_6947798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947798 prefixEnd_6947798 := by exact prefixLift 6947798
  have htrace : WordTrace (prefixWord ++ tailWord_6947798) baseStart_6947798 baseEnd_6947798 := by
    simpa [prefixWord, tailWord_6947798, baseEnd_6947798] using wordTrace_append hprefix tailTrace_6947798
  have hstable : (prefixWord ++ tailWord_6947798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947798).length < 2 ^ (prefixWord ++ tailWord_6947798).sum := by decide
  have hdescent : baseEnd_6947798 < baseStart_6947798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947851 : List Nat := [1, 1, 1, 1, 6, 3, 2, 1, 1, 4, 2]
def baseStart_6947851 : Nat := 118140960795 + 6947851 * 2 ^ 59
def prefixEnd_6947851 : Nat := 4983230072969 + 3 ^ 40 * 6947851 * 2
def baseEnd_6947851 : Nat := 3567587078821401234709921

theorem tailTrace_6947851 : CollatzResearch.WordTrace tailWord_6947851 prefixEnd_6947851 3567587078821401234709921 := by
  unfold tailWord_6947851
  simp only [CollatzResearch.WordTrace]
  refine ⟨253408944352129900325979407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168939296234753266883986271 253408944352129900325979407)
  ·
    refine ⟨380113416528194850488969111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253408944352129900325979407 380113416528194850488969111)
    ·
      refine ⟨570170124792292275733453667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380113416528194850488969111 570170124792292275733453667)
      ·
        refine ⟨855255187188438413600180501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570170124792292275733453667 855255187188438413600180501)
        ·
          refine ⟨40090086899458050637508461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 855255187188438413600180501 40090086899458050637508461)
          ·
            refine ⟨15033782587296768989065673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40090086899458050637508461 15033782587296768989065673)
            ·
              refine ⟨11275336940472576741799255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15033782587296768989065673 11275336940472576741799255)
              ·
                refine ⟨16913005410708865112698883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11275336940472576741799255 16913005410708865112698883)
                ·
                  refine ⟨25369508116063297669048325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16913005410708865112698883 25369508116063297669048325)
                  ·
                    refine ⟨4756782771761868312946561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25369508116063297669048325 4756782771761868312946561)
                    ·
                      refine ⟨3567587078821401234709921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756782771761868312946561 3567587078821401234709921)
                      ·
                        rfl

theorem cell23_6947851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 2, 1, 1, 4, 2].length) (baseStart_6947851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947851 prefixEnd_6947851 := by exact prefixLift 6947851
  have htrace : WordTrace (prefixWord ++ tailWord_6947851) baseStart_6947851 baseEnd_6947851 := by
    simpa [prefixWord, tailWord_6947851, baseEnd_6947851] using wordTrace_append hprefix tailTrace_6947851
  have hstable : (prefixWord ++ tailWord_6947851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947851).length < 2 ^ (prefixWord ++ tailWord_6947851).sum := by decide
  have hdescent : baseEnd_6947851 < baseStart_6947851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947872 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6947872 : Nat := 118140960795 + 6947872 * 2 ^ 59
def prefixEnd_6947872 : Nat := 4983230072969 + 3 ^ 40 * 6947872 * 2
def baseEnd_6947872 : Nat := 3567597861915145652547325

theorem tailTrace_6947872 : CollatzResearch.WordTrace tailWord_6947872 prefixEnd_6947872 3567597861915145652547325 := by
  unfold tailWord_6947872
  simp only [CollatzResearch.WordTrace]
  refine ⟨126704855142526910456246935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168939806856702547274995913 126704855142526910456246935)
  ·
    refine ⟨190057282713790365684370403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126704855142526910456246935 190057282713790365684370403)
    ·
      refine ⟨285085924070685548526555605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190057282713790365684370403 285085924070685548526555605)
      ·
        refine ⟨6681701345406692543591147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 285085924070685548526555605 6681701345406692543591147)
        ·
          refine ⟨10022552018110038815386721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681701345406692543591147 10022552018110038815386721)
          ·
            refine ⟨7516914013582529111540041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10022552018110038815386721 7516914013582529111540041)
            ·
              refine ⟨5637685510186896833655031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7516914013582529111540041 5637685510186896833655031)
              ·
                refine ⟨8456528265280345250482547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637685510186896833655031 8456528265280345250482547)
                ·
                  refine ⟨12684792397920517875723821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456528265280345250482547 12684792397920517875723821)
                  ·
                    refine ⟨4756797149220194203396433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12684792397920517875723821 4756797149220194203396433)
                    ·
                      refine ⟨3567597861915145652547325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756797149220194203396433 3567597861915145652547325)
                      ·
                        rfl

theorem cell23_6947872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6947872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947872 prefixEnd_6947872 := by exact prefixLift 6947872
  have htrace : WordTrace (prefixWord ++ tailWord_6947872) baseStart_6947872 baseEnd_6947872 := by
    simpa [prefixWord, tailWord_6947872, baseEnd_6947872] using wordTrace_append hprefix tailTrace_6947872
  have hstable : (prefixWord ++ tailWord_6947872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947872).length < 2 ^ (prefixWord ++ tailWord_6947872).sum := by decide
  have hdescent : baseEnd_6947872 < baseStart_6947872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947902 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 2, 2, 2]
def baseStart_6947902 : Nat := 118140960795 + 6947902 * 2 ^ 59
def prefixEnd_6947902 : Nat := 4983230072969 + 3 ^ 40 * 6947902 * 2
def baseEnd_6947902 : Nat := 3567613266334780535172187

theorem tailTrace_6947902 : CollatzResearch.WordTrace tailWord_6947902 prefixEnd_6947902 3567613266334780535172187 := by
  unfold tailWord_6947902
  simp only [CollatzResearch.WordTrace]
  refine ⟨31676350559368142004510745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168940536316630090690723973 31676350559368142004510745)
  ·
    refine ⟨23757262919526106503383059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31676350559368142004510745 23757262919526106503383059)
    ·
      refine ⟨35635894379289159755074589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23757262919526106503383059 35635894379289159755074589)
      ·
        refine ⟨13363460392233434908152971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35635894379289159755074589 13363460392233434908152971)
        ·
          refine ⟨20045190588350152362229457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13363460392233434908152971 20045190588350152362229457)
          ·
            refine ⟨15033892941262614271672093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20045190588350152362229457 15033892941262614271672093)
            ·
              refine ⟨5637709852973480351877035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15033892941262614271672093 5637709852973480351877035)
              ·
                refine ⟨8456564779460220527815553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637709852973480351877035 8456564779460220527815553)
                ·
                  refine ⟨6342423584595165395861665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456564779460220527815553 6342423584595165395861665)
                  ·
                    refine ⟨4756817688446374046896249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6342423584595165395861665 4756817688446374046896249)
                    ·
                      refine ⟨3567613266334780535172187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756817688446374046896249 3567613266334780535172187)
                      ·
                        rfl

theorem cell23_6947902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_6947902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947902 prefixEnd_6947902 := by exact prefixLift 6947902
  have htrace : WordTrace (prefixWord ++ tailWord_6947902) baseStart_6947902 baseEnd_6947902 := by
    simpa [prefixWord, tailWord_6947902, baseEnd_6947902] using wordTrace_append hprefix tailTrace_6947902
  have hstable : (prefixWord ++ tailWord_6947902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947902).length < 2 ^ (prefixWord ++ tailWord_6947902).sum := by decide
  have hdescent : baseEnd_6947902 < baseStart_6947902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947907 : List Nat := [1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4]
def baseStart_6947907 : Nat := 118140960795 + 6947907 * 2 ^ 59
def prefixEnd_6947907 : Nat := 4983230072969 + 3 ^ 40 * 6947907 * 2
def baseEnd_6947907 : Nat := 3567615833738053015609663

theorem tailTrace_6947907 : CollatzResearch.WordTrace tailWord_6947907 prefixEnd_6947907 3567615833738053015609663 := by
  unfold tailWord_6947907
  simp only [CollatzResearch.WordTrace]
  refine ⟨253410986839927021890017975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168940657893284681260011983 253410986839927021890017975)
  ·
    refine ⟨380116480259890532835026963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253410986839927021890017975 380116480259890532835026963)
    ·
      refine ⟨570174720389835799252540445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380116480259890532835026963 570174720389835799252540445)
      ·
        refine ⟨213815520146188424719702667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 570174720389835799252540445 213815520146188424719702667)
        ·
          refine ⟨320723280219282637079554001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213815520146188424719702667 320723280219282637079554001)
          ·
            refine ⟨240542460164461977809665501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320723280219282637079554001 240542460164461977809665501)
            ·
              refine ⟨90203422561673241678624563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240542460164461977809665501 90203422561673241678624563)
              ·
                refine ⟨135305133842509862517936845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90203422561673241678624563 135305133842509862517936845)
                ·
                  refine ⟨50739425190941198444226317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135305133842509862517936845 50739425190941198444226317)
                  ·
                    refine ⟨19027284446602949416584869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50739425190941198444226317 19027284446602949416584869)
                    ·
                      refine ⟨3567615833738053015609663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19027284446602949416584869 3567615833738053015609663)
                      ·
                        rfl

theorem cell23_6947907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_6947907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947907 prefixEnd_6947907 := by exact prefixLift 6947907
  have htrace : WordTrace (prefixWord ++ tailWord_6947907) baseStart_6947907 baseEnd_6947907 := by
    simpa [prefixWord, tailWord_6947907, baseEnd_6947907] using wordTrace_append hprefix tailTrace_6947907
  have hstable : (prefixWord ++ tailWord_6947907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947907).length < 2 ^ (prefixWord ++ tailWord_6947907).sum := by decide
  have hdescent : baseEnd_6947907 < baseStart_6947907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947924 : List Nat := [2, 4, 1, 1, 1, 1, 4, 1, 1, 3, 4]
def baseStart_6947924 : Nat := 118140960795 + 6947924 * 2 ^ 59
def prefixEnd_6947924 : Nat := 4983230072969 + 3 ^ 40 * 6947924 * 2
def baseEnd_6947924 : Nat := 3567624562909179449097085

theorem tailTrace_6947924 : CollatzResearch.WordTrace tailWord_6947924 prefixEnd_6947924 3567624562909179449097085 := by
  unfold tailWord_6947924
  simp only [CollatzResearch.WordTrace]
  refine ⟨126705803440432716896693413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168941071253910289195591217 126705803440432716896693413)
  ·
    refine ⟨23757338145081134418130015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126705803440432716896693413 23757338145081134418130015)
    ·
      refine ⟨35636007217621701627195023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23757338145081134418130015 35636007217621701627195023)
      ·
        refine ⟨53454010826432552440792535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35636007217621701627195023 53454010826432552440792535)
        ·
          refine ⟨80181016239648828661188803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53454010826432552440792535 80181016239648828661188803)
          ·
            refine ⟨120271524359473242991783205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80181016239648828661188803 120271524359473242991783205)
            ·
              refine ⟨22550910817401233060959351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120271524359473242991783205 22550910817401233060959351)
              ·
                refine ⟨33826366226101849591439027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22550910817401233060959351 33826366226101849591439027)
                ·
                  refine ⟨50739549339152774387158541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33826366226101849591439027 50739549339152774387158541)
                  ·
                    refine ⟨19027331002182290395184453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50739549339152774387158541 19027331002182290395184453)
                    ·
                      refine ⟨3567624562909179449097085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19027331002182290395184453 3567624562909179449097085)
                      ·
                        rfl

theorem cell23_6947924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_6947924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947924 prefixEnd_6947924 := by exact prefixLift 6947924
  have htrace : WordTrace (prefixWord ++ tailWord_6947924) baseStart_6947924 baseEnd_6947924 := by
    simpa [prefixWord, tailWord_6947924, baseEnd_6947924] using wordTrace_append hprefix tailTrace_6947924
  have hstable : (prefixWord ++ tailWord_6947924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947924).length < 2 ^ (prefixWord ++ tailWord_6947924).sum := by decide
  have hdescent : baseEnd_6947924 < baseStart_6947924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947927 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_6947927 : Nat := 118140960795 + 6947927 * 2 ^ 59
def prefixEnd_6947927 : Nat := 4983230072969 + 3 ^ 40 * 6947927 * 2
def baseEnd_6947927 : Nat := 3567626103351142937359571

theorem tailTrace_6947927 : CollatzResearch.WordTrace tailWord_6947927 prefixEnd_6947927 3567626103351142937359571 := by
  unfold tailWord_6947927
  simp only [CollatzResearch.WordTrace]
  refine ⟨253411716299854565305746035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168941144199903043537164023 253411716299854565305746035)
  ·
    refine ⟨380117574449781847958619053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253411716299854565305746035 380117574449781847958619053)
    ·
      refine ⟨142544090418668192984482145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380117574449781847958619053 142544090418668192984482145)
      ·
        refine ⟨106908067814001144738361609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142544090418668192984482145 106908067814001144738361609)
        ·
          refine ⟨80181050860500858553771207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106908067814001144738361609 80181050860500858553771207)
          ·
            refine ⟨120271576290751287830656811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80181050860500858553771207 120271576290751287830656811)
            ·
              refine ⟨180407364436126931745985217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120271576290751287830656811 180407364436126931745985217)
              ·
                refine ⟨135305523327095198809488913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180407364436126931745985217 135305523327095198809488913)
                ·
                  refine ⟨101479142495321399107116685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135305523327095198809488913 101479142495321399107116685)
                  ·
                    refine ⟨38054678435745524665168757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101479142495321399107116685 38054678435745524665168757)
                    ·
                      refine ⟨3567626103351142937359571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38054678435745524665168757 3567626103351142937359571)
                      ·
                        rfl

theorem cell23_6947927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_6947927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947927 prefixEnd_6947927 := by exact prefixLift 6947927
  have htrace : WordTrace (prefixWord ++ tailWord_6947927) baseStart_6947927 baseEnd_6947927 := by
    simpa [prefixWord, tailWord_6947927, baseEnd_6947927] using wordTrace_append hprefix tailTrace_6947927
  have hstable : (prefixWord ++ tailWord_6947927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947927).length < 2 ^ (prefixWord ++ tailWord_6947927).sum := by decide
  have hdescent : baseEnd_6947927 < baseStart_6947927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947937 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 6]
def baseStart_6947937 : Nat := 118140960795 + 6947937 * 2 ^ 59
def prefixEnd_6947937 : Nat := 4983230072969 + 3 ^ 40 * 6947937 * 2
def baseEnd_6947937 : Nat := 3567631238157687898234525

theorem tailTrace_6947937 : CollatzResearch.WordTrace tailWord_6947937 prefixEnd_6947937 3567631238157687898234525 := by
  unfold tailWord_6947937
  simp only [CollatzResearch.WordTrace]
  refine ⟨253412081029818337013610065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168941387353212224675740043 253412081029818337013610065)
  ·
    refine ⟨190059060772363752760207549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253412081029818337013610065 190059060772363752760207549)
    ·
      refine ⟨71272147789636407285077831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190059060772363752760207549 71272147789636407285077831)
      ·
        refine ⟨106908221684454610927616747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71272147789636407285077831 106908221684454610927616747)
        ·
          refine ⟨160362332526681916391425121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106908221684454610927616747 160362332526681916391425121)
          ·
            refine ⟨120271749395011437293568841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160362332526681916391425121 120271749395011437293568841)
            ·
              refine ⟨90203812046258577970176631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 120271749395011437293568841 90203812046258577970176631)
              ·
                refine ⟨135305718069387866955264947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90203812046258577970176631 135305718069387866955264947)
                ·
                  refine ⟨202958577104081800432897421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 135305718069387866955264947 202958577104081800432897421)
                  ·
                    refine ⟨76109466414030675162336533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 202958577104081800432897421 76109466414030675162336533)
                    ·
                      refine ⟨3567631238157687898234525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76109466414030675162336533 3567631238157687898234525)
                      ·
                        rfl

theorem cell23_6947937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 3, 6].length) (baseStart_6947937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947937 prefixEnd_6947937 := by exact prefixLift 6947937
  have htrace : WordTrace (prefixWord ++ tailWord_6947937) baseStart_6947937 baseEnd_6947937 := by
    simpa [prefixWord, tailWord_6947937, baseEnd_6947937] using wordTrace_append hprefix tailTrace_6947937
  have hstable : (prefixWord ++ tailWord_6947937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947937).length < 2 ^ (prefixWord ++ tailWord_6947937).sum := by decide
  have hdescent : baseEnd_6947937 < baseStart_6947937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947964 : List Nat := [2, 2, 2, 1, 1, 3, 3, 3, 6]
def baseStart_6947964 : Nat := 118140960795 + 6947964 * 2 ^ 59
def prefixEnd_6947964 : Nat := 4983230072969 + 3 ^ 40 * 6947964 * 2
def baseEnd_6947964 : Nat := 396405011348373254732989

theorem tailTrace_6947964 : CollatzResearch.WordTrace tailWord_6947964 prefixEnd_6947964 396405011348373254732989 := by
  unfold tailWord_6947964
  simp only [CollatzResearch.WordTrace]
  refine ⟨126706532900360260312421473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168942043867147013749895297 126706532900360260312421473)
  ·
    refine ⟨95029899675270195234316105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126706532900360260312421473 95029899675270195234316105)
    ·
      refine ⟨71272424756452646425737079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95029899675270195234316105 71272424756452646425737079)
      ·
        refine ⟨106908637134678969638605619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71272424756452646425737079 106908637134678969638605619)
        ·
          refine ⟨160362955702018454457908429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106908637134678969638605619 160362955702018454457908429)
          ·
            refine ⟨60136108388256920421715661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160362955702018454457908429 60136108388256920421715661)
            ·
              refine ⟨22551040645596345158143373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60136108388256920421715661 22551040645596345158143373)
              ·
                refine ⟨8456640242098629434303765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22551040645596345158143373 8456640242098629434303765)
                ·
                  refine ⟨396405011348373254732989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8456640242098629434303765 396405011348373254732989)
                  ·
                    rfl

theorem cell23_6947964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3, 6].length) (baseStart_6947964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947964 prefixEnd_6947964 := by exact prefixLift 6947964
  have htrace : WordTrace (prefixWord ++ tailWord_6947964) baseStart_6947964 baseEnd_6947964 := by
    simpa [prefixWord, tailWord_6947964, baseEnd_6947964] using wordTrace_append hprefix tailTrace_6947964
  have hstable : (prefixWord ++ tailWord_6947964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947964).length < 2 ^ (prefixWord ++ tailWord_6947964).sum := by decide
  have hdescent : baseEnd_6947964 < baseStart_6947964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6947998 : List Nat := [4, 3, 1, 1, 2, 2, 2, 2, 6]
def baseStart_6947998 : Nat := 118140960795 + 6947998 * 2 ^ 59
def prefixEnd_6947998 : Nat := 4983230072969 + 3 ^ 40 * 6947998 * 2
def baseEnd_6947998 : Nat := 396406951164179128841305

theorem tailTrace_6947998 : CollatzResearch.WordTrace tailWord_6947998 prefixEnd_6947998 396406951164179128841305 := by
  unfold tailWord_6947998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31676788235324668053947581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168942870588398229621053765 31676788235324668053947581)
  ·
    refine ⟨11878795588246750520230343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31676788235324668053947581 11878795588246750520230343)
    ·
      refine ⟨17818193382370125780345515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11878795588246750520230343 17818193382370125780345515)
      ·
        refine ⟨26727290073555188670518273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17818193382370125780345515 26727290073555188670518273)
        ·
          refine ⟨20045467555166391502888705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26727290073555188670518273 20045467555166391502888705)
          ·
            refine ⟨15034100666374793627166529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20045467555166391502888705 15034100666374793627166529)
            ·
              refine ⟨11275575499781095220374897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15034100666374793627166529 11275575499781095220374897)
              ·
                refine ⟨8456681624835821415281173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11275575499781095220374897 8456681624835821415281173)
                ·
                  refine ⟨396406951164179128841305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8456681624835821415281173 396406951164179128841305)
                  ·
                    rfl

theorem cell23_6947998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_6947998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6947998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6947998 prefixEnd_6947998 := by exact prefixLift 6947998
  have htrace : WordTrace (prefixWord ++ tailWord_6947998) baseStart_6947998 baseEnd_6947998 := by
    simpa [prefixWord, tailWord_6947998, baseEnd_6947998] using wordTrace_append hprefix tailTrace_6947998
  have hstable : (prefixWord ++ tailWord_6947998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6947998).length < 2 ^ (prefixWord ++ tailWord_6947998).sum := by decide
  have hdescent : baseEnd_6947998 < baseStart_6947998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6947998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948051 : List Nat := [1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 3]
def baseStart_6948051 : Nat := 118140960795 + 6948051 * 2 ^ 59
def prefixEnd_6948051 : Nat := 4983230072969 + 3 ^ 40 * 6948051 * 2
def baseEnd_6948051 : Nat := 3567689774952300452209001

theorem tailTrace_6948051 : CollatzResearch.WordTrace tailWord_6948051 prefixEnd_6948051 3567689774952300452209001 := by
  unfold tailWord_6948051
  simp only [CollatzResearch.WordTrace]
  refine ⟨253416238951405334483260007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168944159300936889655506671 253416238951405334483260007)
  ·
    refine ⟨380124358427108001724890011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253416238951405334483260007 380124358427108001724890011)
    ·
      refine ⟨570186537640662002587335017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380124358427108001724890011 570186537640662002587335017)
      ·
        refine ⟨427639903230496501940501263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570186537640662002587335017 427639903230496501940501263)
        ·
          refine ⟨641459854845744752910751895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427639903230496501940501263 641459854845744752910751895)
          ·
            refine ⟨962189782268617129366127843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641459854845744752910751895 962189782268617129366127843)
            ·
              refine ⟨1443284673402925694049191765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 962189782268617129366127843 1443284673402925694049191765)
              ·
                refine ⟨8456746133220267738569483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1443284673402925694049191765 8456746133220267738569483)
                ·
                  refine ⟨12685119199830401607854225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8456746133220267738569483 12685119199830401607854225)
                  ·
                    refine ⟨9513839399872801205890669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12685119199830401607854225 9513839399872801205890669)
                    ·
                      refine ⟨3567689774952300452209001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9513839399872801205890669 3567689774952300452209001)
                      ·
                        rfl

theorem cell23_6948051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 2, 3].length) (baseStart_6948051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948051 prefixEnd_6948051 := by exact prefixLift 6948051
  have htrace : WordTrace (prefixWord ++ tailWord_6948051) baseStart_6948051 baseEnd_6948051 := by
    simpa [prefixWord, tailWord_6948051, baseEnd_6948051] using wordTrace_append hprefix tailTrace_6948051
  have hstable : (prefixWord ++ tailWord_6948051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948051).length < 2 ^ (prefixWord ++ tailWord_6948051).sum := by decide
  have hdescent : baseEnd_6948051 < baseStart_6948051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948065 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 3, 2, 2]
def baseStart_6948065 : Nat := 118140960795 + 6948065 * 2 ^ 59
def prefixEnd_6948065 : Nat := 4983230072969 + 3 ^ 40 * 6948065 * 2
def baseEnd_6948065 : Nat := 3567696963681463397433937

theorem tailTrace_6948065 : CollatzResearch.WordTrace tailWord_6948065 prefixEnd_6948065 3567696963681463397433937 := by
  unfold tailWord_6948065
  simp only [CollatzResearch.WordTrace]
  refine ⟨253416749573354614874269649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168944499715569743249513099 253416749573354614874269649)
  ·
    refine ⟨190062562180015961155702237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253416749573354614874269649 190062562180015961155702237)
    ·
      refine ⟨71273460817505985433388339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190062562180015961155702237 71273460817505985433388339)
      ·
        refine ⟨106910191226258978150082509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71273460817505985433388339 106910191226258978150082509)
        ·
          refine ⟨40091321709847116806280941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106910191226258978150082509 40091321709847116806280941)
          ·
            refine ⟨15034245641192668802355353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40091321709847116806280941 15034245641192668802355353)
            ·
              refine ⟨11275684230894501601766515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15034245641192668802355353 11275684230894501601766515)
              ·
                refine ⟨16913526346341752402649773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11275684230894501601766515 16913526346341752402649773)
                ·
                  refine ⟨6342572379878157150993665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16913526346341752402649773 6342572379878157150993665)
                  ·
                    refine ⟨4756929284908617863245249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6342572379878157150993665 4756929284908617863245249)
                    ·
                      refine ⟨3567696963681463397433937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4756929284908617863245249 3567696963681463397433937)
                      ·
                        rfl

theorem cell23_6948065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 3, 2, 2].length) (baseStart_6948065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948065 prefixEnd_6948065 := by exact prefixLift 6948065
  have htrace : WordTrace (prefixWord ++ tailWord_6948065) baseStart_6948065 baseEnd_6948065 := by
    simpa [prefixWord, tailWord_6948065, baseEnd_6948065] using wordTrace_append hprefix tailTrace_6948065
  have hstable : (prefixWord ++ tailWord_6948065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948065).length < 2 ^ (prefixWord ++ tailWord_6948065).sum := by decide
  have hdescent : baseEnd_6948065 < baseStart_6948065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948126 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6948126 : Nat := 118140960795 + 6948126 * 2 ^ 59
def prefixEnd_6948126 : Nat := 4983230072969 + 3 ^ 40 * 6948126 * 2
def baseEnd_6948126 : Nat := 1189242762000462552923719

theorem tailTrace_6948126 : CollatzResearch.WordTrace tailWord_6948126 prefixEnd_6948126 1189242762000462552923719 := by
  unfold tailWord_6948126
  simp only [CollatzResearch.WordTrace]
  refine ⟨31677371803266702786530029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168945982950755748194826821 31677371803266702786530029)
  ·
    refine ⟨11879014426225013544948761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31677371803266702786530029 11879014426225013544948761)
    ·
      refine ⟨8909260819668760158711571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11879014426225013544948761 8909260819668760158711571)
      ·
        refine ⟨13363891229503140238067357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8909260819668760158711571 13363891229503140238067357)
        ·
          refine ⟨5011459211063677589275259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13363891229503140238067357 5011459211063677589275259)
          ·
            refine ⟨7517188816595516383912889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5011459211063677589275259 7517188816595516383912889)
            ·
              refine ⟨5637891612446637287934667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7517188816595516383912889 5637891612446637287934667)
              ·
                refine ⟨8456837418669955931902001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5637891612446637287934667 8456837418669955931902001)
                ·
                  refine ⟨6342628064002466948926501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456837418669955931902001 6342628064002466948926501)
                  ·
                    refine ⟨1189242762000462552923719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6342628064002466948926501 1189242762000462552923719)
                    ·
                      rfl

theorem cell23_6948126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6948126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948126 prefixEnd_6948126 := by exact prefixLift 6948126
  have htrace : WordTrace (prefixWord ++ tailWord_6948126) baseStart_6948126 baseEnd_6948126 := by
    simpa [prefixWord, tailWord_6948126, baseEnd_6948126] using wordTrace_append hprefix tailTrace_6948126
  have hstable : (prefixWord ++ tailWord_6948126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948126).length < 2 ^ (prefixWord ++ tailWord_6948126).sum := by decide
  have hdescent : baseEnd_6948126 < baseStart_6948126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948144 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 9]
def baseStart_6948144 : Nat := 118140960795 + 6948144 * 2 ^ 59
def prefixEnd_6948144 : Nat := 4983230072969 + 3 ^ 40 * 6948144 * 2
def baseEnd_6948144 : Nat := 396415280961463176482897

theorem tailTrace_6948144 : CollatzResearch.WordTrace tailWord_6948144 prefixEnd_6948144 396415280961463176482897 := by
  unfold tailWord_6948144
  simp only [CollatzResearch.WordTrace]
  refine ⟨126709815470034205683197743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168946420626712274244263657 126709815470034205683197743)
  ·
    refine ⟨190064723205051308524796615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126709815470034205683197743 190064723205051308524796615)
    ·
      refine ⟨285097084807576962787194923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190064723205051308524796615 285097084807576962787194923)
      ·
        refine ⟨427645627211365444180792385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285097084807576962787194923 427645627211365444180792385)
        ·
          refine ⟨320734220408524083135594289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427645627211365444180792385 320734220408524083135594289)
          ·
            refine ⟨240550665306393062351695717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320734220408524083135594289 240550665306393062351695717)
            ·
              refine ⟨45103249744948699190942947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 240550665306393062351695717 45103249744948699190942947)
              ·
                refine ⟨67654874617423048786414421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45103249744948699190942947 67654874617423048786414421)
                ·
                  refine ⟨396415280961463176482897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 67654874617423048786414421 396415280961463176482897)
                  ·
                    rfl

theorem cell23_6948144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 9].length) (baseStart_6948144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948144 prefixEnd_6948144 := by exact prefixLift 6948144
  have htrace : WordTrace (prefixWord ++ tailWord_6948144) baseStart_6948144 baseEnd_6948144 := by
    simpa [prefixWord, tailWord_6948144, baseEnd_6948144] using wordTrace_append hprefix tailTrace_6948144
  have hstable : (prefixWord ++ tailWord_6948144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948144).length < 2 ^ (prefixWord ++ tailWord_6948144).sum := by decide
  have hdescent : baseEnd_6948144 < baseStart_6948144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948166 : List Nat := [6, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6948166 : Nat := 118140960795 + 6948166 * 2 ^ 59
def prefixEnd_6948166 : Nat := 4983230072969 + 3 ^ 40 * 6948166 * 2
def baseEnd_6948166 : Nat := 3567748825227567502270973

theorem tailTrace_6948166 : CollatzResearch.WordTrace tailWord_6948166 prefixEnd_6948166 3567748825227567502270973 := by
  unfold tailWord_6948166
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919388542062147160115511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168946955563992472749130901 7919388542062147160115511)
  ·
    refine ⟨11879082813093220740173267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7919388542062147160115511 11879082813093220740173267)
    ·
      refine ⟨17818624219639831110259901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11879082813093220740173267 17818624219639831110259901)
      ·
        refine ⟨6681984082364936666347463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17818624219639831110259901 6681984082364936666347463)
        ·
          refine ⟨10022976123547404999521195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6681984082364936666347463 10022976123547404999521195)
          ·
            refine ⟨15034464185321107499281793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10022976123547404999521195 15034464185321107499281793)
            ·
              refine ⟨11275848138990830624461345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15034464185321107499281793 11275848138990830624461345)
              ·
                refine ⟨8456886104243122968346009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11275848138990830624461345 8456886104243122968346009)
                ·
                  refine ⟨6342664578182342226259507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456886104243122968346009 6342664578182342226259507)
                  ·
                    refine ⟨9513996867273513339389261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6342664578182342226259507 9513996867273513339389261)
                    ·
                      refine ⟨3567748825227567502270973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9513996867273513339389261 3567748825227567502270973)
                      ·
                        rfl

theorem cell23_6948166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6948166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948166 prefixEnd_6948166 := by exact prefixLift 6948166
  have htrace : WordTrace (prefixWord ++ tailWord_6948166) baseStart_6948166 baseEnd_6948166 := by
    simpa [prefixWord, tailWord_6948166, baseEnd_6948166] using wordTrace_append hprefix tailTrace_6948166
  have hstable : (prefixWord ++ tailWord_6948166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948166).length < 2 ^ (prefixWord ++ tailWord_6948166).sum := by decide
  have hdescent : baseEnd_6948166 < baseStart_6948166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948172 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 2, 2, 2]
def baseStart_6948172 : Nat := 118140960795 + 6948172 * 2 ^ 59
def prefixEnd_6948172 : Nat := 4983230072969 + 3 ^ 40 * 6948172 * 2
def baseEnd_6948172 : Nat := 3567751906111494478795945

theorem tailTrace_6948172 : CollatzResearch.WordTrace tailWord_6948172 prefixEnd_6948172 3567751906111494478795945 := by
  unfold tailWord_6948172
  simp only [CollatzResearch.WordTrace]
  refine ⟨126710326091983486074207385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168947101455977981432276513 126710326091983486074207385)
  ·
    refine ⟨95032744568987614555655539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126710326091983486074207385 95032744568987614555655539)
    ·
      refine ⟨142549116853481421833483309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95032744568987614555655539 142549116853481421833483309)
      ·
        refine ⟨53455918820055533187556241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142549116853481421833483309 53455918820055533187556241)
        ·
          refine ⟨40091939115041649890667181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53455918820055533187556241 40091939115041649890667181)
          ·
            refine ⟨15034477168140618709000193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40091939115041649890667181 15034477168140618709000193)
            ·
              refine ⟨11275857876105464031750145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15034477168140618709000193 11275857876105464031750145)
              ·
                refine ⟨8456893407079098023812609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11275857876105464031750145 8456893407079098023812609)
                ·
                  refine ⟨6342670055309323517859457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8456893407079098023812609 6342670055309323517859457)
                  ·
                    refine ⟨4757002541481992638394593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6342670055309323517859457 4757002541481992638394593)
                    ·
                      refine ⟨3567751906111494478795945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757002541481992638394593 3567751906111494478795945)
                      ·
                        rfl

theorem cell23_6948172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_6948172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948172 prefixEnd_6948172 := by exact prefixLift 6948172
  have htrace : WordTrace (prefixWord ++ tailWord_6948172) baseStart_6948172 baseEnd_6948172 := by
    simpa [prefixWord, tailWord_6948172, baseEnd_6948172] using wordTrace_append hprefix tailTrace_6948172
  have hstable : (prefixWord ++ tailWord_6948172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948172).length < 2 ^ (prefixWord ++ tailWord_6948172).sum := by decide
  have hdescent : baseEnd_6948172 < baseStart_6948172 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948311 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 5, 6]
def baseStart_6948311 : Nat := 118140960795 + 6948311 * 2 ^ 59
def prefixEnd_6948311 : Nat := 4983230072969 + 3 ^ 40 * 6948311 * 2
def baseEnd_6948311 : Nat := 1189274426640823144985935

theorem tailTrace_6948311 : CollatzResearch.WordTrace tailWord_6948311 prefixEnd_6948311 1189274426640823144985935 := by
  unfold tailWord_6948311
  simp only [CollatzResearch.WordTrace]
  refine ⟨253425721930463398887724787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168950481286975599258483191 253425721930463398887724787)
  ·
    refine ⟨380138582895695098331587181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253425721930463398887724787 380138582895695098331587181)
    ·
      refine ⟨142551968585885661874345193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380138582895695098331587181 142551968585885661874345193)
      ·
        refine ⟨106913976439414246405758895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142551968585885661874345193 106913976439414246405758895)
        ·
          refine ⟨160370964659121369608638343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106913976439414246405758895 160370964659121369608638343)
          ·
            refine ⟨240556446988682054412957515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160370964659121369608638343 240556446988682054412957515)
            ·
              refine ⟨360834670483023081619436273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240556446988682054412957515 360834670483023081619436273)
              ·
                refine ⟨270626002862267311214577205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 360834670483023081619436273 270626002862267311214577205)
                ·
                  refine ⟨25371187768337560426366613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 270626002862267311214577205 25371187768337560426366613)
                  ·
                    refine ⟨1189274426640823144985935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25371187768337560426366613 1189274426640823144985935)
                    ·
                      rfl

theorem cell23_6948311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_6948311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948311 prefixEnd_6948311 := by exact prefixLift 6948311
  have htrace : WordTrace (prefixWord ++ tailWord_6948311) baseStart_6948311 baseEnd_6948311 := by
    simpa [prefixWord, tailWord_6948311, baseEnd_6948311] using wordTrace_append hprefix tailTrace_6948311
  have hstable : (prefixWord ++ tailWord_6948311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948311).length < 2 ^ (prefixWord ++ tailWord_6948311).sum := by decide
  have hdescent : baseEnd_6948311 < baseStart_6948311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948328 : List Nat := [2, 1, 4, 1, 1, 2, 3, 2, 1, 6]
def baseStart_6948328 : Nat := 118140960795 + 6948328 * 2 ^ 59
def prefixEnd_6948328 : Nat := 4983230072969 + 3 ^ 40 * 6948328 * 2
def baseEnd_6948328 : Nat := 1189277336364531956148409

theorem tailTrace_6948328 : CollatzResearch.WordTrace tailWord_6948328 prefixEnd_6948328 1189277336364531956148409 := by
  unfold tailWord_6948328
  simp only [CollatzResearch.WordTrace]
  refine ⟨126713170985700905395546819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168950894647601207194062425 126713170985700905395546819)
  ·
    refine ⟨190069756478551358093320229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126713170985700905395546819 190069756478551358093320229)
    ·
      refine ⟨35638079339728379642497543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190069756478551358093320229 35638079339728379642497543)
      ·
        refine ⟨53457119009592569463746315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35638079339728379642497543 53457119009592569463746315)
        ·
          refine ⟨80185678514388854195619473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53457119009592569463746315 80185678514388854195619473)
          ·
            refine ⟨60139258885791640646714605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80185678514388854195619473 60139258885791640646714605)
            ·
              refine ⟨22552222082171865242517977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60139258885791640646714605 22552222082171865242517977)
              ·
                refine ⟨16914166561628898931888483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22552222082171865242517977 16914166561628898931888483)
                ·
                  refine ⟨25371249842443348397832725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16914166561628898931888483 25371249842443348397832725)
                  ·
                    refine ⟨1189277336364531956148409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25371249842443348397832725 1189277336364531956148409)
                    ·
                      rfl

theorem cell23_6948328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_6948328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948328 prefixEnd_6948328 := by exact prefixLift 6948328
  have htrace : WordTrace (prefixWord ++ tailWord_6948328) baseStart_6948328 baseEnd_6948328 := by
    simpa [prefixWord, tailWord_6948328, baseEnd_6948328] using wordTrace_append hprefix tailTrace_6948328
  have hstable : (prefixWord ++ tailWord_6948328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948328).length < 2 ^ (prefixWord ++ tailWord_6948328).sum := by decide
  have hdescent : baseEnd_6948328 < baseStart_6948328 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948331 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_6948331 : Nat := 118140960795 + 6948331 * 2 ^ 59
def prefixEnd_6948331 : Nat := 4983230072969 + 3 ^ 40 * 6948331 * 2
def baseEnd_6948331 : Nat := 3567833549535559356707713

theorem tailTrace_6948331 : CollatzResearch.WordTrace tailWord_6948331 prefixEnd_6948331 3567833549535559356707713 := by
  unfold tailWord_6948331
  simp only [CollatzResearch.WordTrace]
  refine ⟨253426451390390942303452847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168950967593593961535635231 253426451390390942303452847)
  ·
    refine ⟨380139677085586413455179271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253426451390390942303452847 380139677085586413455179271)
    ·
      refine ⟨570209515628379620182768907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380139677085586413455179271 570209515628379620182768907)
      ·
        refine ⟨855314273442569430274153361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570209515628379620182768907 855314273442569430274153361)
        ·
          refine ⟨641485705081927072705615021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 855314273442569430274153361 641485705081927072705615021)
          ·
            refine ⟨240557139405722652264605633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 641485705081927072705615021 240557139405722652264605633)
            ·
              refine ⟨180417854554291989198454225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240557139405722652264605633 180417854554291989198454225)
              ·
                refine ⟨135313390915718991898840669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 180417854554291989198454225 135313390915718991898840669)
                ·
                  refine ⟨50742521593394621962065251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 135313390915718991898840669 50742521593394621962065251)
                  ·
                    refine ⟨76113782390091932943097877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 50742521593394621962065251 76113782390091932943097877)
                    ·
                      refine ⟨3567833549535559356707713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 76113782390091932943097877 3567833549535559356707713)
                      ·
                        rfl

theorem cell23_6948331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_6948331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948331 prefixEnd_6948331 := by exact prefixLift 6948331
  have htrace : WordTrace (prefixWord ++ tailWord_6948331) baseStart_6948331 baseEnd_6948331 := by
    simpa [prefixWord, tailWord_6948331, baseEnd_6948331] using wordTrace_append hprefix tailTrace_6948331
  have hstable : (prefixWord ++ tailWord_6948331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948331).length < 2 ^ (prefixWord ++ tailWord_6948331).sum := by decide
  have hdescent : baseEnd_6948331 < baseStart_6948331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948351 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_6948351 : Nat := 118140960795 + 6948351 * 2 ^ 59
def prefixEnd_6948351 : Nat := 4983230072969 + 3 ^ 40 * 6948351 * 2
def baseEnd_6948351 : Nat := 3567843819148649278457621

theorem tailTrace_6948351 : CollatzResearch.WordTrace tailWord_6948351 prefixEnd_6948351 3567843819148649278457621 := by
  unfold tailWord_6948351
  simp only [CollatzResearch.WordTrace]
  refine ⟨253427180850318485719180907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168951453900212323812787271 253427180850318485719180907)
  ·
    refine ⟨380140771275477728578771361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253427180850318485719180907 380140771275477728578771361)
    ·
      refine ⟨285105578456608296434078521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380140771275477728578771361 285105578456608296434078521)
      ·
        refine ⟨213829183842456222325558891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285105578456608296434078521 213829183842456222325558891)
        ·
          refine ⟨320743775763684333488338337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213829183842456222325558891 320743775763684333488338337)
          ·
            refine ⟨240557831822763250116253753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 320743775763684333488338337 240557831822763250116253753)
            ·
              refine ⟨180418373867072437587190315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240557831822763250116253753 180418373867072437587190315)
              ·
                refine ⟨270627560800608656380785473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180418373867072437587190315 270627560800608656380785473)
                ·
                  refine ⟨202970670600456492285589105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 270627560800608656380785473 202970670600456492285589105)
                  ·
                    refine ⟨152228002950342369214191829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 202970670600456492285589105 152228002950342369214191829)
                    ·
                      refine ⟨3567843819148649278457621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 152228002950342369214191829 3567843819148649278457621)
                      ·
                        rfl

theorem cell23_6948351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_6948351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948351 prefixEnd_6948351 := by exact prefixLift 6948351
  have htrace : WordTrace (prefixWord ++ tailWord_6948351) baseStart_6948351 baseEnd_6948351 := by
    simpa [prefixWord, tailWord_6948351, baseEnd_6948351] using wordTrace_append hprefix tailTrace_6948351
  have hstable : (prefixWord ++ tailWord_6948351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948351).length < 2 ^ (prefixWord ++ tailWord_6948351).sum := by decide
  have hdescent : baseEnd_6948351 < baseStart_6948351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948385 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 3]
def baseStart_6948385 : Nat := 118140960795 + 6948385 * 2 ^ 59
def prefixEnd_6948385 : Nat := 4983230072969 + 3 ^ 40 * 6948385 * 2
def baseEnd_6948385 : Nat := 3567861277490902145432465

theorem tailTrace_6948385 : CollatzResearch.WordTrace tailWord_6948385 prefixEnd_6948385 3567861277490902145432465 := by
  unfold tailWord_6948385
  simp only [CollatzResearch.WordTrace]
  refine ⟨253428420932195309525918609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168952280621463539683945739 253428420932195309525918609)
  ·
    refine ⟨190071315699146482144438957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253428420932195309525918609 190071315699146482144438957)
    ·
      refine ⟨71276743387179930804164609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190071315699146482144438957 71276743387179930804164609)
      ·
        refine ⟨53457557540384948103123457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71276743387179930804164609 53457557540384948103123457)
        ·
          refine ⟨40093168155288711077342593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53457557540384948103123457 40093168155288711077342593)
          ·
            refine ⟨30069876116466533308006945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40093168155288711077342593 30069876116466533308006945)
            ·
              refine ⟨22552407087349899981005209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30069876116466533308006945 22552407087349899981005209)
              ·
                refine ⟨16914305315512424985753907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22552407087349899981005209 16914305315512424985753907)
                ·
                  refine ⟨25371457973268637478630861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16914305315512424985753907 25371457973268637478630861)
                  ·
                    refine ⟨9514296739975739054486573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25371457973268637478630861 9514296739975739054486573)
                    ·
                      refine ⟨3567861277490902145432465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9514296739975739054486573 3567861277490902145432465)
                      ·
                        rfl

theorem cell23_6948385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_6948385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948385 prefixEnd_6948385 := by exact prefixLift 6948385
  have htrace : WordTrace (prefixWord ++ tailWord_6948385) baseStart_6948385 baseEnd_6948385 := by
    simpa [prefixWord, tailWord_6948385, baseEnd_6948385] using wordTrace_append hprefix tailTrace_6948385
  have hstable : (prefixWord ++ tailWord_6948385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948385).length < 2 ^ (prefixWord ++ tailWord_6948385).sum := by decide
  have hdescent : baseEnd_6948385 < baseStart_6948385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948465 : List Nat := [1, 2, 2, 2, 1, 1, 1, 8, 5]
def baseStart_6948465 : Nat := 118140960795 + 6948465 * 2 ^ 59
def prefixEnd_6948465 : Nat := 4983230072969 + 3 ^ 40 * 6948465 * 2
def baseEnd_6948465 : Nat := 396433595104806870270233

theorem tailTrace_6948465 : CollatzResearch.WordTrace tailWord_6948465 prefixEnd_6948465 396433595104806870270233 := by
  unfold tailWord_6948465
  simp only [CollatzResearch.WordTrace]
  refine ⟨253431338771905483188830849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168954225847936988792553899 253431338771905483188830849)
  ·
    refine ⟨190073504078929112391623137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253431338771905483188830849 190073504078929112391623137)
    ·
      refine ⟨142555128059196834293717353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190073504078929112391623137 142555128059196834293717353)
      ·
        refine ⟨106916346044397625720288015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142555128059196834293717353 106916346044397625720288015)
        ·
          refine ⟨160374519066596438580432023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106916346044397625720288015 160374519066596438580432023)
          ·
            refine ⟨240561778599894657870648035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160374519066596438580432023 240561778599894657870648035)
            ·
              refine ⟨360842667899841986805972053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240561778599894657870648035 360842667899841986805972053)
              ·
                refine ⟨4228625014451273282882485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 360842667899841986805972053 4228625014451273282882485)
                ·
                  refine ⟨396433595104806870270233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4228625014451273282882485 396433595104806870270233)
                  ·
                    rfl

theorem cell23_6948465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 8, 5].length) (baseStart_6948465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948465 prefixEnd_6948465 := by exact prefixLift 6948465
  have htrace : WordTrace (prefixWord ++ tailWord_6948465) baseStart_6948465 baseEnd_6948465 := by
    simpa [prefixWord, tailWord_6948465, baseEnd_6948465] using wordTrace_append hprefix tailTrace_6948465
  have hstable : (prefixWord ++ tailWord_6948465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948465).length < 2 ^ (prefixWord ++ tailWord_6948465).sum := by decide
  have hdescent : baseEnd_6948465 < baseStart_6948465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948515 : List Nat := [1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 4]
def baseStart_6948515 : Nat := 118140960795 + 6948515 * 2 ^ 59
def prefixEnd_6948515 : Nat := 4983230072969 + 3 ^ 40 * 6948515 * 2
def baseEnd_6948515 : Nat := 3567928029975986636806867

theorem tailTrace_6948515 : CollatzResearch.WordTrace tailWord_6948515 prefixEnd_6948515 3567928029975986636806867 := by
  unfold tailWord_6948515
  simp only [CollatzResearch.WordTrace]
  refine ⟨253433162421724341728150999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168955441614482894485433999 253433162421724341728150999)
  ·
    refine ⟨380149743632586512592226499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253433162421724341728150999 380149743632586512592226499)
    ·
      refine ⟨570224615448879768888339749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380149743632586512592226499 570224615448879768888339749)
      ·
        refine ⟨106917115396664956666563703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 570224615448879768888339749 106917115396664956666563703)
        ·
          refine ⟨160375673094997434999845555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106917115396664956666563703 160375673094997434999845555)
          ·
            refine ⟨240563509642496152499768333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160375673094997434999845555 240563509642496152499768333)
            ·
              refine ⟨90211316115936057187413125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 240563509642496152499768333 90211316115936057187413125)
              ·
                refine ⟨16914621771738010722639961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90211316115936057187413125 16914621771738010722639961)
                ·
                  refine ⟨12685966328803508041979971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16914621771738010722639961 12685966328803508041979971)
                  ·
                    refine ⟨19028949493205262062969957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12685966328803508041979971 19028949493205262062969957)
                    ·
                      refine ⟨3567928029975986636806867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19028949493205262062969957 3567928029975986636806867)
                      ·
                        rfl

theorem cell23_6948515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_6948515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948515 prefixEnd_6948515 := by exact prefixLift 6948515
  have htrace : WordTrace (prefixWord ++ tailWord_6948515) baseStart_6948515 baseEnd_6948515 := by
    simpa [prefixWord, tailWord_6948515, baseEnd_6948515] using wordTrace_append hprefix tailTrace_6948515
  have hstable : (prefixWord ++ tailWord_6948515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948515).length < 2 ^ (prefixWord ++ tailWord_6948515).sum := by decide
  have hdescent : baseEnd_6948515 < baseStart_6948515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948542 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_6948542 : Nat := 118140960795 + 6948542 * 2 ^ 59
def prefixEnd_6948542 : Nat := 4983230072969 + 3 ^ 40 * 6948542 * 2
def baseEnd_6948542 : Nat := 1189313964651219343723081

theorem tailTrace_6948542 : CollatzResearch.WordTrace tailWord_6948542 prefixEnd_6948542 1189313964651219343723081 := by
  unfold tailWord_6948542
  simp only [CollatzResearch.WordTrace]
  refine ⟨31679268399078315667422985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168956098128417683559589253 31679268399078315667422985)
  ·
    refine ⟨23759451299308736750567239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31679268399078315667422985 23759451299308736750567239)
    ·
      refine ⟨35639176948963105125850859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23759451299308736750567239 35639176948963105125850859)
      ·
        refine ⟨53458765423444657688776289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35639176948963105125850859 53458765423444657688776289)
        ·
          refine ⟨40094074067583493266582217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53458765423444657688776289 40094074067583493266582217)
          ·
            refine ⟨30070555550687619949936663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40094074067583493266582217 30070555550687619949936663)
            ·
              refine ⟨45105833326031429924904995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30070555550687619949936663 45105833326031429924904995)
              ·
                refine ⟨67658749989047144887357493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45105833326031429924904995 67658749989047144887357493)
                ·
                  refine ⟨6343007811473169833189765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 67658749989047144887357493 6343007811473169833189765)
                  ·
                    refine ⟨1189313964651219343723081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6343007811473169833189765 1189313964651219343723081)
                    ·
                      rfl

theorem cell23_6948542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_6948542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948542 prefixEnd_6948542 := by exact prefixLift 6948542
  have htrace : WordTrace (prefixWord ++ tailWord_6948542) baseStart_6948542 baseEnd_6948542 := by
    simpa [prefixWord, tailWord_6948542, baseEnd_6948542] using wordTrace_append hprefix tailTrace_6948542
  have hstable : (prefixWord ++ tailWord_6948542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948542).length < 2 ^ (prefixWord ++ tailWord_6948542).sum := by decide
  have hdescent : baseEnd_6948542 < baseStart_6948542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948546 : List Nat := [3, 5, 1, 2, 1, 1, 1, 1, 1, 7]
def baseStart_6948546 : Nat := 118140960795 + 6948546 * 2 ^ 59
def prefixEnd_6948546 : Nat := 4983230072969 + 3 ^ 40 * 6948546 * 2
def baseEnd_6948546 : Nat := 1189314649292092005173075

theorem tailTrace_6948546 : CollatzResearch.WordTrace tailWord_6948546 prefixEnd_6948546 1189314649292092005173075 := by
  unfold tailWord_6948546
  simp only [CollatzResearch.WordTrace]
  refine ⟨63358573271153008505632373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168956195389741356015019661 63358573271153008505632373)
  ·
    refine ⟨5939866244170594547403035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 63358573271153008505632373 5939866244170594547403035)
    ·
      refine ⟨8909799366255891821104553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5939866244170594547403035 8909799366255891821104553)
      ·
        refine ⟨6682349524691918865828415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8909799366255891821104553 6682349524691918865828415)
        ·
          refine ⟨10023524287037878298742623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682349524691918865828415 10023524287037878298742623)
          ·
            refine ⟨15035286430556817448113935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023524287037878298742623 15035286430556817448113935)
            ·
              refine ⟨22552929645835226172170903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15035286430556817448113935 22552929645835226172170903)
              ·
                refine ⟨33829394468752839258256355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22552929645835226172170903 33829394468752839258256355)
                ·
                  refine ⟨50744091703129258887384533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33829394468752839258256355 50744091703129258887384533)
                  ·
                    refine ⟨1189314649292092005173075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50744091703129258887384533 1189314649292092005173075)
                    ·
                      rfl

theorem cell23_6948546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_6948546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948546 prefixEnd_6948546 := by exact prefixLift 6948546
  have htrace : WordTrace (prefixWord ++ tailWord_6948546) baseStart_6948546 baseEnd_6948546 := by
    simpa [prefixWord, tailWord_6948546, baseEnd_6948546] using wordTrace_append hprefix tailTrace_6948546
  have hstable : (prefixWord ++ tailWord_6948546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948546).length < 2 ^ (prefixWord ++ tailWord_6948546).sum := by decide
  have hdescent : baseEnd_6948546 < baseStart_6948546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948589 : List Nat := [1, 5, 1, 2, 1, 3, 3, 1, 6]
def baseStart_6948589 : Nat := 118140960795 + 6948589 * 2 ^ 59
def prefixEnd_6948589 : Nat := 4983230072969 + 3 ^ 40 * 6948589 * 2
def baseEnd_6948589 : Nat := 396440669727157705253503

theorem tailTrace_6948589 : CollatzResearch.WordTrace tailWord_6948589 prefixEnd_6948589 396440669727157705253503 := by
  unfold tailWord_6948589
  simp only [CollatzResearch.WordTrace]
  refine ⟨253435861423456252366344821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168957240948970834910896547 253435861423456252366344821)
  ·
    refine ⟨23759612008449023659344827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 253435861423456252366344821 23759612008449023659344827)
    ·
      refine ⟨35639418012673535489017241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23759612008449023659344827 35639418012673535489017241)
      ·
        refine ⟨26729563509505151616762931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35639418012673535489017241 26729563509505151616762931)
        ·
          refine ⟨40094345264257727425144397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26729563509505151616762931 40094345264257727425144397)
          ·
            refine ⟨15035379474096647784429149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40094345264257727425144397 15035379474096647784429149)
            ·
              refine ⟨5638267302786242919160931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15035379474096647784429149 5638267302786242919160931)
              ·
                refine ⟨8457400954179364378741397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5638267302786242919160931 8457400954179364378741397)
                ·
                  refine ⟨396440669727157705253503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8457400954179364378741397 396440669727157705253503)
                  ·
                    rfl

theorem cell23_6948589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_6948589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948589 prefixEnd_6948589 := by exact prefixLift 6948589
  have htrace : WordTrace (prefixWord ++ tailWord_6948589) baseStart_6948589 baseEnd_6948589 := by
    simpa [prefixWord, tailWord_6948589, baseEnd_6948589] using wordTrace_append hprefix tailTrace_6948589
  have hstable : (prefixWord ++ tailWord_6948589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948589).length < 2 ^ (prefixWord ++ tailWord_6948589).sum := by decide
  have hdescent : baseEnd_6948589 < baseStart_6948589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948592 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 6, 3, 2]
def baseStart_6948592 : Nat := 118140960795 + 6948592 * 2 ^ 59
def prefixEnd_6948592 : Nat := 4983230072969 + 3 ^ 40 * 6948592 * 2
def baseEnd_6948592 : Nat := 3567967567986382835544013

theorem tailTrace_6948592 : CollatzResearch.WordTrace tailWord_6948592 prefixEnd_6948592 3567967567986382835544013 := by
  unfold tailWord_6948592
  simp only [CollatzResearch.WordTrace]
  refine ⟨126717985421222691939352015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168957313894963589252469353 126717985421222691939352015)
  ·
    refine ⟨190076978131834037909028023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126717985421222691939352015 190076978131834037909028023)
    ·
      refine ⟨285115467197751056863542035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190076978131834037909028023 285115467197751056863542035)
      ·
        refine ⟨427673200796626585295313053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285115467197751056863542035 427673200796626585295313053)
        ·
          refine ⟨160377450298734969485742395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427673200796626585295313053 160377450298734969485742395)
          ·
            refine ⟨240566175448102454228613593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160377450298734969485742395 240566175448102454228613593)
            ·
              refine ⟨180424631586076840671460195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 240566175448102454228613593 180424631586076840671460195)
              ·
                refine ⟨270636947379115261007190293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180424631586076840671460195 270636947379115261007190293)
                ·
                  refine ⟨12686106908396027859712045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 270636947379115261007190293 12686106908396027859712045)
                  ·
                    refine ⟨4757290090648510447392017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12686106908396027859712045 4757290090648510447392017)
                    ·
                      refine ⟨3567967567986382835544013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757290090648510447392017 3567967567986382835544013)
                      ·
                        rfl

theorem cell23_6948592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 6, 3, 2].length) (baseStart_6948592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948592 prefixEnd_6948592 := by exact prefixLift 6948592
  have htrace : WordTrace (prefixWord ++ tailWord_6948592) baseStart_6948592 baseEnd_6948592 := by
    simpa [prefixWord, tailWord_6948592, baseEnd_6948592] using wordTrace_append hprefix tailTrace_6948592
  have hstable : (prefixWord ++ tailWord_6948592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948592).length < 2 ^ (prefixWord ++ tailWord_6948592).sum := by decide
  have hdescent : baseEnd_6948592 < baseStart_6948592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948626 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_6948626 : Nat := 118140960795 + 6948626 * 2 ^ 59
def prefixEnd_6948626 : Nat := 4983230072969 + 3 ^ 40 * 6948626 * 2
def baseEnd_6948626 : Nat := 3567985026328635702518857

theorem tailTrace_6948626 : CollatzResearch.WordTrace tailWord_6948626 prefixEnd_6948626 3567985026328635702518857 := by
  unfold tailWord_6948626
  simp only [CollatzResearch.WordTrace]
  refine ⟨63359302731080551921360433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168958140616214805123627821 63359302731080551921360433)
  ·
    refine ⟨47519477048310413941020325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63359302731080551921360433 47519477048310413941020325)
    ·
      refine ⟨8909901946558202613941311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47519477048310413941020325 8909901946558202613941311)
      ·
        refine ⟨13364852919837303920911967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8909901946558202613941311 13364852919837303920911967)
        ·
          refine ⟨20047279379755955881367951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13364852919837303920911967 20047279379755955881367951)
          ·
            refine ⟨30070919069633933822051927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20047279379755955881367951 30070919069633933822051927)
            ·
              refine ⟨45106378604450900733077891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30070919069633933822051927 45106378604450900733077891)
              ·
                refine ⟨67659567906676351099616837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45106378604450900733077891 67659567906676351099616837)
                ·
                  refine ⟨12686168982501815831178157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67659567906676351099616837 12686168982501815831178157)
                  ·
                    refine ⟨4757313368438180936691809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12686168982501815831178157 4757313368438180936691809)
                    ·
                      refine ⟨3567985026328635702518857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757313368438180936691809 3567985026328635702518857)
                      ·
                        rfl

theorem cell23_6948626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_6948626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948626 prefixEnd_6948626 := by exact prefixLift 6948626
  have htrace : WordTrace (prefixWord ++ tailWord_6948626) baseStart_6948626 baseEnd_6948626 := by
    simpa [prefixWord, tailWord_6948626, baseEnd_6948626] using wordTrace_append hprefix tailTrace_6948626
  have hstable : (prefixWord ++ tailWord_6948626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948626).length < 2 ^ (prefixWord ++ tailWord_6948626).sum := by decide
  have hdescent : baseEnd_6948626 < baseStart_6948626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948632 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 4, 4]
def baseStart_6948632 : Nat := 118140960795 + 6948632 * 2 ^ 59
def prefixEnd_6948632 : Nat := 4983230072969 + 3 ^ 40 * 6948632 * 2
def baseEnd_6948632 : Nat := 1189329369070854226347943

theorem tailTrace_6948632 : CollatzResearch.WordTrace tailWord_6948632 prefixEnd_6948632 1189329369070854226347943 := by
  unfold tailWord_6948632
  simp only [CollatzResearch.WordTrace]
  refine ⟨126718714881150235355080075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168958286508200313806773433 126718714881150235355080075)
  ·
    refine ⟨190078072321725353032620113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126718714881150235355080075 190078072321725353032620113)
    ·
      refine ⟨142558554241294014774465085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190078072321725353032620113 142558554241294014774465085)
      ·
        refine ⟨53459457840485255540424407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 142558554241294014774465085 53459457840485255540424407)
        ·
          refine ⟨80189186760727883310636611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53459457840485255540424407 80189186760727883310636611)
          ·
            refine ⟨120283780141091824965954917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 80189186760727883310636611 120283780141091824965954917)
            ·
              refine ⟨22553208776454717181116547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120283780141091824965954917 22553208776454717181116547)
              ·
                refine ⟨33829813164682075771674821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22553208776454717181116547 33829813164682075771674821)
                ·
                  refine ⟨6343089968377889207189029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33829813164682075771674821 6343089968377889207189029)
                  ·
                    refine ⟨1189329369070854226347943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6343089968377889207189029 1189329369070854226347943)
                    ·
                      rfl

theorem cell23_6948632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_6948632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948632 prefixEnd_6948632 := by exact prefixLift 6948632
  have htrace : WordTrace (prefixWord ++ tailWord_6948632) baseStart_6948632 baseEnd_6948632 := by
    simpa [prefixWord, tailWord_6948632, baseEnd_6948632] using wordTrace_append hprefix tailTrace_6948632
  have hstable : (prefixWord ++ tailWord_6948632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948632).length < 2 ^ (prefixWord ++ tailWord_6948632).sum := by decide
  have hdescent : baseEnd_6948632 < baseStart_6948632 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948635 : List Nat := [1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4]
def baseStart_6948635 : Nat := 118140960795 + 6948635 * 2 ^ 59
def prefixEnd_6948635 : Nat := 4983230072969 + 3 ^ 40 * 6948635 * 2
def baseEnd_6948635 : Nat := 3567989647654526167306315

theorem tailTrace_6948635 : CollatzResearch.WordTrace tailWord_6948635 prefixEnd_6948635 3567989647654526167306315 := by
  unfold tailWord_6948635
  simp only [CollatzResearch.WordTrace]
  refine ⟨253437539181289602222519359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168958359454193068148346239 253437539181289602222519359)
  ·
    refine ⟨380156308771934403333779039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253437539181289602222519359 380156308771934403333779039)
    ·
      refine ⟨570234463157901605000668559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380156308771934403333779039 570234463157901605000668559)
      ·
        refine ⟨855351694736852407501002839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570234463157901605000668559 855351694736852407501002839)
        ·
          refine ⟨1283027542105278611251504259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855351694736852407501002839 1283027542105278611251504259)
          ·
            refine ⟨1924541313157917916877256389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283027542105278611251504259 1924541313157917916877256389)
            ·
              refine ⟨360851496217109609414485573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1924541313157917916877256389 360851496217109609414485573)
              ·
                refine ⟨67659655540708051765216045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 360851496217109609414485573 67659655540708051765216045)
                ·
                  refine ⟨25372370827765519411956017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 67659655540708051765216045 25372370827765519411956017)
                  ·
                    refine ⟨19029278120824139558967013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25372370827765519411956017 19029278120824139558967013)
                    ·
                      refine ⟨3567989647654526167306315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19029278120824139558967013 3567989647654526167306315)
                      ·
                        rfl

theorem cell23_6948635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_6948635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948635 prefixEnd_6948635 := by exact prefixLift 6948635
  have htrace : WordTrace (prefixWord ++ tailWord_6948635) baseStart_6948635 baseEnd_6948635 := by
    simpa [prefixWord, tailWord_6948635, baseEnd_6948635] using wordTrace_append hprefix tailTrace_6948635
  have hstable : (prefixWord ++ tailWord_6948635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948635).length < 2 ^ (prefixWord ++ tailWord_6948635).sum := by decide
  have hdescent : baseEnd_6948635 < baseStart_6948635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948642 : List Nat := [3, 3, 1, 1, 2, 1, 1, 4, 1, 1, 5]
def baseStart_6948642 : Nat := 118140960795 + 6948642 * 2 ^ 59
def prefixEnd_6948642 : Nat := 4983230072969 + 3 ^ 40 * 6948642 * 2
def baseEnd_6948642 : Nat := 3567993242019107639918783

theorem tailTrace_6948642 : CollatzResearch.WordTrace tailWord_6948642 prefixEnd_6948642 3567993242019107639918783 := by
  unfold tailWord_6948642
  simp only [CollatzResearch.WordTrace]
  refine ⟨63359448623066060604506045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168958529661509494945349453 63359448623066060604506045)
  ·
    refine ⟨23759793233649772726689767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63359448623066060604506045 23759793233649772726689767)
    ·
      refine ⟨35639689850474659090034651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23759793233649772726689767 35639689850474659090034651)
      ·
        refine ⟨53459534775711988635051977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35639689850474659090034651 53459534775711988635051977)
        ·
          refine ⟨40094651081783991476288983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53459534775711988635051977 40094651081783991476288983)
          ·
            refine ⟨60141976622675987214433475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40094651081783991476288983 60141976622675987214433475)
            ·
              refine ⟨90212964934013980821650213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60141976622675987214433475 90212964934013980821650213)
              ·
                refine ⟨16914930925127621404059415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90212964934013980821650213 16914930925127621404059415)
                ·
                  refine ⟨25372396387691432106089123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16914930925127621404059415 25372396387691432106089123)
                  ·
                    refine ⟨38058594581537148159133685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25372396387691432106089123 38058594581537148159133685)
                    ·
                      refine ⟨3567993242019107639918783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38058594581537148159133685 3567993242019107639918783)
                      ·
                        rfl

theorem cell23_6948642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_6948642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948642 prefixEnd_6948642 := by exact prefixLift 6948642
  have htrace : WordTrace (prefixWord ++ tailWord_6948642) baseStart_6948642 baseEnd_6948642 := by
    simpa [prefixWord, tailWord_6948642, baseEnd_6948642] using wordTrace_append hprefix tailTrace_6948642
  have hstable : (prefixWord ++ tailWord_6948642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948642).length < 2 ^ (prefixWord ++ tailWord_6948642).sum := by decide
  have hdescent : baseEnd_6948642 < baseStart_6948642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948645 : List Nat := [1, 3, 1, 2, 3, 2, 1, 10]
def baseStart_6948645 : Nat := 118140960795 + 6948645 * 2 ^ 59
def prefixEnd_6948645 : Nat := 4983230072969 + 3 ^ 40 * 6948645 * 2
def baseEnd_6948645 : Nat := 132147954905965597340047

theorem tailTrace_6948645 : CollatzResearch.WordTrace tailWord_6948645 prefixEnd_6948645 132147954905965597340047 := by
  unfold tailWord_6948645
  simp only [CollatzResearch.WordTrace]
  refine ⟨253437903911253373930383389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168958602607502249286922259 253437903911253373930383389)
  ·
    refine ⟨95039213966720015223893771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253437903911253373930383389 95039213966720015223893771)
    ·
      refine ⟨142558820950080022835840657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95039213966720015223893771 142558820950080022835840657)
      ·
        refine ⟨106919115712560017126880493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142558820950080022835840657 106919115712560017126880493)
        ·
          refine ⟨40094668392210006422580185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106919115712560017126880493 40094668392210006422580185)
          ·
            refine ⟨30071001294157504816935139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40094668392210006422580185 30071001294157504816935139)
            ·
              refine ⟨45106501941236257225402709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30071001294157504816935139 45106501941236257225402709)
              ·
                refine ⟨132147954905965597340047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45106501941236257225402709 132147954905965597340047)
                ·
                  rfl

theorem cell23_6948645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 10].length) (baseStart_6948645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948645 prefixEnd_6948645 := by exact prefixLift 6948645
  have htrace : WordTrace (prefixWord ++ tailWord_6948645) baseStart_6948645 baseEnd_6948645 := by
    simpa [prefixWord, tailWord_6948645, baseEnd_6948645] using wordTrace_append hprefix tailTrace_6948645
  have hstable : (prefixWord ++ tailWord_6948645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948645).length < 2 ^ (prefixWord ++ tailWord_6948645).sum := by decide
  have hdescent : baseEnd_6948645 < baseStart_6948645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948659 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 3]
def baseStart_6948659 : Nat := 118140960795 + 6948659 * 2 ^ 59
def prefixEnd_6948659 : Nat := 4983230072969 + 3 ^ 40 * 6948659 * 2
def baseEnd_6948659 : Nat := 3568001971190234073406205

theorem tailTrace_6948659 : CollatzResearch.WordTrace tailWord_6948659 prefixEnd_6948659 3568001971190234073406205 := by
  unfold tailWord_6948659
  simp only [CollatzResearch.WordTrace]
  refine ⟨253438414533202654321393031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168958943022135102880928687 253438414533202654321393031)
  ·
    refine ⟨380157621799803981482089547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253438414533202654321393031 380157621799803981482089547)
    ·
      refine ⟨570236432699705972223134321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380157621799803981482089547 570236432699705972223134321)
      ·
        refine ⟨427677324524779479167350741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570236432699705972223134321 427677324524779479167350741)
        ·
          refine ⟨10023687293549519042984783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 427677324524779479167350741 10023687293549519042984783)
          ·
            refine ⟨15035530940324278564477175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10023687293549519042984783 15035530940324278564477175)
            ·
              refine ⟨22553296410486417846715763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15035530940324278564477175 22553296410486417846715763)
              ·
                refine ⟨33829944615729626770073645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22553296410486417846715763 33829944615729626770073645)
                ·
                  refine ⟨12686229230898610038777617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33829944615729626770073645 12686229230898610038777617)
                  ·
                    refine ⟨9514671923173957529083213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12686229230898610038777617 9514671923173957529083213)
                    ·
                      refine ⟨3568001971190234073406205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9514671923173957529083213 3568001971190234073406205)
                      ·
                        rfl

theorem cell23_6948659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_6948659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948659 prefixEnd_6948659 := by exact prefixLift 6948659
  have htrace : WordTrace (prefixWord ++ tailWord_6948659) baseStart_6948659 baseEnd_6948659 := by
    simpa [prefixWord, tailWord_6948659, baseEnd_6948659] using wordTrace_append hprefix tailTrace_6948659
  have hstable : (prefixWord ++ tailWord_6948659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948659).length < 2 ^ (prefixWord ++ tailWord_6948659).sum := by decide
  have hdescent : baseEnd_6948659 < baseStart_6948659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948669 : List Nat := [1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6948669 : Nat := 118140960795 + 6948669 * 2 ^ 59
def prefixEnd_6948669 : Nat := 4983230072969 + 3 ^ 40 * 6948669 * 2
def baseEnd_6948669 : Nat := 3568007105996779034281159

theorem tailTrace_6948669 : CollatzResearch.WordTrace tailWord_6948669 prefixEnd_6948669 3568007105996779034281159 := by
  unfold tailWord_6948669
  simp only [CollatzResearch.WordTrace]
  refine ⟨253438779263166426029257061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168959186175444284019504707 253438779263166426029257061)
  ·
    refine ⟨47519771111843704880485699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253438779263166426029257061 47519771111843704880485699)
    ·
      refine ⟨71279656667765557320728549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47519771111843704880485699 71279656667765557320728549)
      ·
        refine ⟨13364935625206041997636603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 71279656667765557320728549 13364935625206041997636603)
        ·
          refine ⟨20047403437809062996454905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13364935625206041997636603 20047403437809062996454905)
          ·
            refine ⟨15035552578356797247341179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20047403437809062996454905 15035552578356797247341179)
            ·
              refine ⟨22553328867535195871011769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15035552578356797247341179 22553328867535195871011769)
              ·
                refine ⟨16914996650651396903258827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22553328867535195871011769 16914996650651396903258827)
                ·
                  refine ⟨25372494975977095354888241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16914996650651396903258827 25372494975977095354888241)
                  ·
                    refine ⟨19029371231982821516166181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25372494975977095354888241 19029371231982821516166181)
                    ·
                      refine ⟨3568007105996779034281159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19029371231982821516166181 3568007105996779034281159)
                      ·
                        rfl

theorem cell23_6948669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6948669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948669 prefixEnd_6948669 := by exact prefixLift 6948669
  have htrace : WordTrace (prefixWord ++ tailWord_6948669) baseStart_6948669 baseEnd_6948669 := by
    simpa [prefixWord, tailWord_6948669, baseEnd_6948669] using wordTrace_append hprefix tailTrace_6948669
  have hstable : (prefixWord ++ tailWord_6948669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948669).length < 2 ^ (prefixWord ++ tailWord_6948669).sum := by decide
  have hdescent : baseEnd_6948669 < baseStart_6948669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948690 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_6948690 : Nat := 118140960795 + 6948690 * 2 ^ 59
def prefixEnd_6948690 : Nat := 4983230072969 + 3 ^ 40 * 6948690 * 2
def baseEnd_6948690 : Nat := 3568017889090523452118563

theorem tailTrace_6948690 : CollatzResearch.WordTrace tailWord_6948690 prefixEnd_6948690 3568017889090523452118563 := by
  unfold tailWord_6948690
  simp only [CollatzResearch.WordTrace]
  refine ⟨63359886299022586653942881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168959696797393564410514349 63359886299022586653942881)
  ·
    refine ⟨47519914724266939990457161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63359886299022586653942881 47519914724266939990457161)
    ·
      refine ⟨35639936043200204992842871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47519914724266939990457161 35639936043200204992842871)
      ·
        refine ⟨53459904064800307489264307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35639936043200204992842871 53459904064800307489264307)
        ·
          refine ⟨80189856097200461233896461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53459904064800307489264307 80189856097200461233896461)
          ·
            refine ⟨30071196036450172962711173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80189856097200461233896461 30071196036450172962711173)
            ·
              refine ⟨5638349256834407430508345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30071196036450172962711173 5638349256834407430508345)
              ·
                refine ⟨4228761942625805572881259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638349256834407430508345 4228761942625805572881259)
                ·
                  refine ⟨6343142913938708359321889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228761942625805572881259 6343142913938708359321889)
                  ·
                    refine ⟨4757357185454031269491417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6343142913938708359321889 4757357185454031269491417)
                    ·
                      refine ⟨3568017889090523452118563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757357185454031269491417 3568017889090523452118563)
                      ·
                        rfl

theorem cell23_6948690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_6948690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948690 prefixEnd_6948690 := by exact prefixLift 6948690
  have htrace : WordTrace (prefixWord ++ tailWord_6948690) baseStart_6948690 baseEnd_6948690 := by
    simpa [prefixWord, tailWord_6948690, baseEnd_6948690] using wordTrace_append hprefix tailTrace_6948690
  have hstable : (prefixWord ++ tailWord_6948690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948690).length < 2 ^ (prefixWord ++ tailWord_6948690).sum := by decide
  have hdescent : baseEnd_6948690 < baseStart_6948690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948692 : List Nat := [2, 4, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_6948692 : Nat := 118140960795 + 6948692 * 2 ^ 59
def prefixEnd_6948692 : Nat := 4983230072969 + 3 ^ 40 * 6948692 * 2
def baseEnd_6948692 : Nat := 1189339638683944148097851

theorem tailTrace_6948692 : CollatzResearch.WordTrace tailWord_6948692 prefixEnd_6948692 1189339638683944148097851 := by
  unfold tailWord_6948692
  simp only [CollatzResearch.WordTrace]
  refine ⟨126719809071041550478672165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168959745428055400638229553 126719809071041550478672165)
  ·
    refine ⟨23759964200820290714751031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126719809071041550478672165 23759964200820290714751031)
    ·
      refine ⟨35639946301230436072126547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23759964200820290714751031 35639946301230436072126547)
      ·
        refine ⟨53459919451845654108189821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35639946301230436072126547 53459919451845654108189821)
        ·
          refine ⟨20047469794442120290571183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53459919451845654108189821 20047469794442120290571183)
          ·
            refine ⟨30071204691663180435856775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20047469794442120290571183 30071204691663180435856775)
            ·
              refine ⟨45106807037494770653785163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30071204691663180435856775 45106807037494770653785163)
              ·
                refine ⟨67660210556242155980677745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45106807037494770653785163 67660210556242155980677745)
                ·
                  refine ⟨50745157917181616985508309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67660210556242155980677745 50745157917181616985508309)
                  ·
                    refine ⟨1189339638683944148097851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 50745157917181616985508309 1189339638683944148097851)
                    ·
                      rfl

theorem cell23_6948692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_6948692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948692 prefixEnd_6948692 := by exact prefixLift 6948692
  have htrace : WordTrace (prefixWord ++ tailWord_6948692) baseStart_6948692 baseEnd_6948692 := by
    simpa [prefixWord, tailWord_6948692, baseEnd_6948692] using wordTrace_append hprefix tailTrace_6948692
  have hstable : (prefixWord ++ tailWord_6948692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948692).length < 2 ^ (prefixWord ++ tailWord_6948692).sum := by decide
  have hdescent : baseEnd_6948692 < baseStart_6948692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948706 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 1, 3, 3]
def baseStart_6948706 : Nat := 118140960795 + 6948706 * 2 ^ 59
def prefixEnd_6948706 : Nat := 4983230072969 + 3 ^ 40 * 6948706 * 2
def baseEnd_6948706 : Nat := 3568026104780995389518489

theorem tailTrace_6948706 : CollatzResearch.WordTrace tailWord_6948706 prefixEnd_6948706 3568026104780995389518489 := by
  unfold tailWord_6948706
  simp only [CollatzResearch.WordTrace]
  refine ⟨63360032191008095337088493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168960085842688254232235981 63360032191008095337088493)
  ·
    refine ⟨23760012071628035751408185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 63360032191008095337088493 23760012071628035751408185)
    ·
      refine ⟨17820009053721026813556139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23760012071628035751408185 17820009053721026813556139)
      ·
        refine ⟨26730013580581540220334209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17820009053721026813556139 26730013580581540220334209)
        ·
          refine ⟨20047510185436155165250657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26730013580581540220334209 20047510185436155165250657)
          ·
            refine ⟨15035632639077116373937993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20047510185436155165250657 15035632639077116373937993)
            ·
              refine ⟨11276724479307837280453495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15035632639077116373937993 11276724479307837280453495)
              ·
                refine ⟨16915086718961755920680243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11276724479307837280453495 16915086718961755920680243)
                ·
                  refine ⟨25372630078442633881020365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16915086718961755920680243 25372630078442633881020365)
                  ·
                    refine ⟨9514736279415987705382637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25372630078442633881020365 9514736279415987705382637)
                    ·
                      refine ⟨3568026104780995389518489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9514736279415987705382637 3568026104780995389518489)
                      ·
                        rfl

theorem cell23_6948706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_6948706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948706 prefixEnd_6948706 := by exact prefixLift 6948706
  have htrace : WordTrace (prefixWord ++ tailWord_6948706) baseStart_6948706 baseEnd_6948706 := by
    simpa [prefixWord, tailWord_6948706, baseEnd_6948706] using wordTrace_append hprefix tailTrace_6948706
  have hstable : (prefixWord ++ tailWord_6948706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948706).length < 2 ^ (prefixWord ++ tailWord_6948706).sum := by decide
  have hdescent : baseEnd_6948706 < baseStart_6948706 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948712 : List Nat := [2, 1, 4, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_6948712 : Nat := 118140960795 + 6948712 * 2 ^ 59
def prefixEnd_6948712 : Nat := 4983230072969 + 3 ^ 40 * 6948712 * 2
def baseEnd_6948712 : Nat := 3568029185664922366043461

theorem tailTrace_6948712 : CollatzResearch.WordTrace tailWord_6948712 prefixEnd_6948712 3568029185664922366043461 := by
  unfold tailWord_6948712
  simp only [CollatzResearch.WordTrace]
  refine ⟨126720173801005322186536195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168960231734673762915381593 126720173801005322186536195)
  ·
    refine ⟨190080260701507983279804293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126720173801005322186536195 190080260701507983279804293)
    ·
      refine ⟨35640048881532746864963305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190080260701507983279804293 35640048881532746864963305)
      ·
        refine ⟨26730036661149560148722479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35640048881532746864963305 26730036661149560148722479)
        ·
          refine ⟨40095054991724340223083719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26730036661149560148722479 40095054991724340223083719)
          ·
            refine ⟨60142582487586510334625579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40095054991724340223083719 60142582487586510334625579)
            ·
              refine ⟨90213873731379765501938369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60142582487586510334625579 90213873731379765501938369)
              ·
                refine ⟨67660405298534824126453777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90213873731379765501938369 67660405298534824126453777)
                ·
                  refine ⟨50745303973901118094840333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67660405298534824126453777 50745303973901118094840333)
                  ·
                    refine ⟨19029488990212919285565125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 50745303973901118094840333 19029488990212919285565125)
                    ·
                      refine ⟨3568029185664922366043461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19029488990212919285565125 3568029185664922366043461)
                      ·
                        rfl

theorem cell23_6948712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_6948712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948712 prefixEnd_6948712 := by exact prefixLift 6948712
  have htrace : WordTrace (prefixWord ++ tailWord_6948712) baseStart_6948712 baseEnd_6948712 := by
    simpa [prefixWord, tailWord_6948712, baseEnd_6948712] using wordTrace_append hprefix tailTrace_6948712
  have hstable : (prefixWord ++ tailWord_6948712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948712).length < 2 ^ (prefixWord ++ tailWord_6948712).sum := by decide
  have hdescent : baseEnd_6948712 < baseStart_6948712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948729 : List Nat := [1, 2, 1, 3, 2, 2, 1, 4, 1, 4, 2]
def baseStart_6948729 : Nat := 118140960795 + 6948729 * 2 ^ 59
def prefixEnd_6948729 : Nat := 4983230072969 + 3 ^ 40 * 6948729 * 2
def baseEnd_6948729 : Nat := 3568037914836048799530883

theorem tailTrace_6948729 : CollatzResearch.WordTrace tailWord_6948729 prefixEnd_6948729 3568037914836048799530883 := by
  unfold tailWord_6948729
  simp only [CollatzResearch.WordTrace]
  refine ⟨253440967642949056276441241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168960645095299370850960827 253440967642949056276441241)
  ·
    refine ⟨190080725732211792207330931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253440967642949056276441241 190080725732211792207330931)
    ·
      refine ⟨285121088598317688310996397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190080725732211792207330931 285121088598317688310996397)
      ·
        refine ⟨106920408224369133116623649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285121088598317688310996397 106920408224369133116623649)
        ·
          refine ⟨80190306168276849837467737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106920408224369133116623649 80190306168276849837467737)
          ·
            refine ⟨60142729626207637378100803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80190306168276849837467737 60142729626207637378100803)
            ·
              refine ⟨90214094439311456067151205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60142729626207637378100803 90214094439311456067151205)
              ·
                refine ⟨16915142707370898012590851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90214094439311456067151205 16915142707370898012590851)
                ·
                  refine ⟨25372714061056347018886277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16915142707370898012590851 25372714061056347018886277)
                  ·
                    refine ⟨4757383886448065066041177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25372714061056347018886277 4757383886448065066041177)
                    ·
                      refine ⟨3568037914836048799530883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757383886448065066041177 3568037914836048799530883)
                      ·
                        rfl

theorem cell23_6948729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 4, 1, 4, 2].length) (baseStart_6948729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948729 prefixEnd_6948729 := by exact prefixLift 6948729
  have htrace : WordTrace (prefixWord ++ tailWord_6948729) baseStart_6948729 baseEnd_6948729 := by
    simpa [prefixWord, tailWord_6948729, baseEnd_6948729] using wordTrace_append hprefix tailTrace_6948729
  have hstable : (prefixWord ++ tailWord_6948729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948729).length < 2 ^ (prefixWord ++ tailWord_6948729).sum := by decide
  have hdescent : baseEnd_6948729 < baseStart_6948729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948735 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 11]
def baseStart_6948735 : Nat := 118140960795 + 6948735 * 2 ^ 59
def prefixEnd_6948735 : Nat := 4983230072969 + 3 ^ 40 * 6948735 * 2
def baseEnd_6948735 : Nat := 396448999524441752895095

theorem tailTrace_6948735 : CollatzResearch.WordTrace tailWord_6948735 prefixEnd_6948735 396448999524441752895095 := by
  unfold tailWord_6948735
  simp only [CollatzResearch.WordTrace]
  refine ⟨253441186480927319301159659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168960790987284879534106439 253441186480927319301159659)
  ·
    refine ⟨380161779721390978951739489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253441186480927319301159659 380161779721390978951739489)
    ·
      refine ⟨285121334791043234213804617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380161779721390978951739489 285121334791043234213804617)
      ·
        refine ⟨213841001093282425660353463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285121334791043234213804617 213841001093282425660353463)
        ·
          refine ⟨320761501639923638490530195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213841001093282425660353463 320761501639923638490530195)
          ·
            refine ⟨481142252459885457735795293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320761501639923638490530195 481142252459885457735795293)
            ·
              refine ⟨180428344672457046650923235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481142252459885457735795293 180428344672457046650923235)
              ·
                refine ⟨270642517008685569976384853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180428344672457046650923235 270642517008685569976384853)
                ·
                  refine ⟨396448999524441752895095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 270642517008685569976384853 396448999524441752895095)
                  ·
                    rfl

theorem cell23_6948735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 11].length) (baseStart_6948735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948735 prefixEnd_6948735 := by exact prefixLift 6948735
  have htrace : WordTrace (prefixWord ++ tailWord_6948735) baseStart_6948735 baseEnd_6948735 := by
    simpa [prefixWord, tailWord_6948735, baseEnd_6948735] using wordTrace_append hprefix tailTrace_6948735
  have hstable : (prefixWord ++ tailWord_6948735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948735).length < 2 ^ (prefixWord ++ tailWord_6948735).sum := by decide
  have hdescent : baseEnd_6948735 < baseStart_6948735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948792 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_6948792 : Nat := 118140960795 + 6948792 * 2 ^ 59
def prefixEnd_6948792 : Nat := 4983230072969 + 3 ^ 40 * 6948792 * 2
def baseEnd_6948792 : Nat := 3568070264117282053043093

theorem tailTrace_6948792 : CollatzResearch.WordTrace tailWord_6948792 prefixEnd_6948792 3568070264117282053043093 := by
  unfold tailWord_6948792
  simp only [CollatzResearch.WordTrace]
  refine ⟨126721632720860409017992315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168962176961147212023989753 126721632720860409017992315)
  ·
    refine ⟨190082449081290613526988473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126721632720860409017992315 190082449081290613526988473)
    ·
      refine ⟨142561836810967960145241355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190082449081290613526988473 142561836810967960145241355)
      ·
        refine ⟨213842755216451940217862033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142561836810967960145241355 213842755216451940217862033)
        ·
          refine ⟨160382066412338955163396525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213842755216451940217862033 160382066412338955163396525)
          ·
            refine ⟨60143274904627108186273697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160382066412338955163396525 60143274904627108186273697)
            ·
              refine ⟨45107456178470331139705273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60143274904627108186273697 45107456178470331139705273)
              ·
                refine ⟨33830592133852748354778955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45107456178470331139705273 33830592133852748354778955)
                ·
                  refine ⟨50745888200779122532168433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33830592133852748354778955 50745888200779122532168433)
                  ·
                    refine ⟨38059416150584341899126325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50745888200779122532168433 38059416150584341899126325)
                    ·
                      refine ⟨3568070264117282053043093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38059416150584341899126325 3568070264117282053043093)
                      ·
                        rfl

theorem cell23_6948792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_6948792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948792 prefixEnd_6948792 := by exact prefixLift 6948792
  have htrace : WordTrace (prefixWord ++ tailWord_6948792) baseStart_6948792 baseEnd_6948792 := by
    simpa [prefixWord, tailWord_6948792, baseEnd_6948792] using wordTrace_append hprefix tailTrace_6948792
  have hstable : (prefixWord ++ tailWord_6948792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948792).length < 2 ^ (prefixWord ++ tailWord_6948792).sum := by decide
  have hdescent : baseEnd_6948792 < baseStart_6948792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948832 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4]
def baseStart_6948832 : Nat := 118140960795 + 6948832 * 2 ^ 59
def prefixEnd_6948832 : Nat := 4983230072969 + 3 ^ 40 * 6948832 * 2
def baseEnd_6948832 : Nat := 3568090803343461896542909

theorem tailTrace_6948832 : CollatzResearch.WordTrace tailWord_6948832 prefixEnd_6948832 3568090803343461896542909 := by
  unfold tailWord_6948832
  simp only [CollatzResearch.WordTrace]
  refine ⟨126722362180787952433720375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168963149574383936578293833 126722362180787952433720375)
  ·
    refine ⟨190083543271181928650580563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126722362180787952433720375 190083543271181928650580563)
    ·
      refine ⟨285125314906772892975870845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190083543271181928650580563 285125314906772892975870845)
      ·
        refine ⟨106921993090039834865951567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285125314906772892975870845 106921993090039834865951567)
        ·
          refine ⟨160382989635059752298927351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106921993090039834865951567 160382989635059752298927351)
          ·
            refine ⟨240574484452589628448391027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160382989635059752298927351 240574484452589628448391027)
            ·
              refine ⟨360861726678884442672586541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 240574484452589628448391027 360861726678884442672586541)
              ·
                refine ⟨135323147504581666002219953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 360861726678884442672586541 135323147504581666002219953)
                ·
                  refine ⟨101492360628436249501664965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135323147504581666002219953 101492360628436249501664965)
                  ·
                    refine ⟨19029817617831796781562181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 101492360628436249501664965 19029817617831796781562181)
                    ·
                      refine ⟨3568090803343461896542909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19029817617831796781562181 3568090803343461896542909)
                      ·
                        rfl

theorem cell23_6948832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_6948832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948832 prefixEnd_6948832 := by exact prefixLift 6948832
  have htrace : WordTrace (prefixWord ++ tailWord_6948832) baseStart_6948832 baseEnd_6948832 := by
    simpa [prefixWord, tailWord_6948832, baseEnd_6948832] using wordTrace_append hprefix tailTrace_6948832
  have hstable : (prefixWord ++ tailWord_6948832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948832).length < 2 ^ (prefixWord ++ tailWord_6948832).sum := by decide
  have hdescent : baseEnd_6948832 < baseStart_6948832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948889 : List Nat := [1, 2, 1, 2, 1, 1, 3, 6, 1, 5]
def baseStart_6948889 : Nat := 118140960795 + 6948889 * 2 ^ 59
def prefixEnd_6948889 : Nat := 4983230072969 + 3 ^ 40 * 6948889 * 2
def baseEnd_6948889 : Nat := 1189373357246922724510049

theorem tailTrace_6948889 : CollatzResearch.WordTrace tailWord_6948889 prefixEnd_6948889 1189373357246922724510049 := by
  unfold tailWord_6948889
  simp only [CollatzResearch.WordTrace]
  refine ⟨253446803322369403602265721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168964535548246269068177147 253446803322369403602265721)
  ·
    refine ⟨190085102491777052701699291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253446803322369403602265721 190085102491777052701699291)
    ·
      refine ⟨285127653737665579052548937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190085102491777052701699291 285127653737665579052548937)
      ·
        refine ⟨213845740303249184289411703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285127653737665579052548937 213845740303249184289411703)
        ·
          refine ⟨320768610454873776434117555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213845740303249184289411703 320768610454873776434117555)
          ·
            refine ⟨481152915682310664651176333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320768610454873776434117555 481152915682310664651176333)
            ·
              refine ⟨180432343380866499244191125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 481152915682310664651176333 180432343380866499244191125)
              ·
                refine ⟨8457766095978117152071459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 180432343380866499244191125 8457766095978117152071459)
                ·
                  refine ⟨12686649143967175728107189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8457766095978117152071459 12686649143967175728107189)
                  ·
                    refine ⟨1189373357246922724510049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12686649143967175728107189 1189373357246922724510049)
                    ·
                      rfl

theorem cell23_6948889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 1, 5].length) (baseStart_6948889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948889 prefixEnd_6948889 := by exact prefixLift 6948889
  have htrace : WordTrace (prefixWord ++ tailWord_6948889) baseStart_6948889 baseEnd_6948889 := by
    simpa [prefixWord, tailWord_6948889, baseEnd_6948889] using wordTrace_append hprefix tailTrace_6948889
  have hstable : (prefixWord ++ tailWord_6948889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948889).length < 2 ^ (prefixWord ++ tailWord_6948889).sum := by decide
  have hdescent : baseEnd_6948889 < baseStart_6948889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948949 : List Nat := [1, 3, 2, 2, 1, 4, 1, 9]
def baseStart_6948949 : Nat := 118140960795 + 6948949 * 2 ^ 59
def prefixEnd_6948949 : Nat := 4983230072969 + 3 ^ 40 * 6948949 * 2
def baseEnd_6948949 : Nat := 132153736317779182917773

theorem tailTrace_6948949 : CollatzResearch.WordTrace tailWord_6948949 prefixEnd_6948949 132153736317779182917773 := by
  unfold tailWord_6948949
  simp only [CollatzResearch.WordTrace]
  refine ⟨253448991702152033849449901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168965994468101355899633267 253448991702152033849449901)
  ·
    refine ⟨95043371888307012693543713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253448991702152033849449901 95043371888307012693543713)
    ·
      refine ⟨71282528916230259520157785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95043371888307012693543713 71282528916230259520157785)
      ·
        refine ⟨53461896687172694640118339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71282528916230259520157785 53461896687172694640118339)
        ·
          refine ⟨80192845030759041960177509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53461896687172694640118339 80192845030759041960177509)
          ·
            refine ⟨15036158443267320367533283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80192845030759041960177509 15036158443267320367533283)
            ·
              refine ⟨22554237664900980551299925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15036158443267320367533283 22554237664900980551299925)
              ·
                refine ⟨132153736317779182917773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22554237664900980551299925 132153736317779182917773)
                ·
                  rfl

theorem cell23_6948949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 9].length) (baseStart_6948949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948949 prefixEnd_6948949 := by exact prefixLift 6948949
  have htrace : WordTrace (prefixWord ++ tailWord_6948949) baseStart_6948949 baseEnd_6948949 := by
    simpa [prefixWord, tailWord_6948949, baseEnd_6948949] using wordTrace_append hprefix tailTrace_6948949
  have hstable : (prefixWord ++ tailWord_6948949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948949).length < 2 ^ (prefixWord ++ tailWord_6948949).sum := by decide
  have hdescent : baseEnd_6948949 < baseStart_6948949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6948977 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 1, 2, 2]
def baseStart_6948977 : Nat := 118140960795 + 6948977 * 2 ^ 59
def prefixEnd_6948977 : Nat := 4983230072969 + 3 ^ 40 * 6948977 * 2
def baseEnd_6948977 : Nat := 3568165258038363829229743

theorem tailTrace_6948977 : CollatzResearch.WordTrace tailWord_6948977 prefixEnd_6948977 3568165258038363829229743 := by
  unfold tailWord_6948977
  simp only [CollatzResearch.WordTrace]
  refine ⟨253450012946050594631469185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168966675297367063087646123 253450012946050594631469185)
  ·
    refine ⟨190087509709537945973601889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253450012946050594631469185 190087509709537945973601889)
    ·
      refine ⟨142565632282153459480201417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190087509709537945973601889 142565632282153459480201417)
      ·
        refine ⟨106924224211615094610151063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142565632282153459480201417 106924224211615094610151063)
        ·
          refine ⟨160386336317422641915226595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106924224211615094610151063 160386336317422641915226595)
          ·
            refine ⟨240579504476133962872839893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 160386336317422641915226595 240579504476133962872839893)
            ·
              refine ⟨5638582136159389754832185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 240579504476133962872839893 5638582136159389754832185)
              ·
                refine ⟨4228936602119542316124139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5638582136159389754832185 4228936602119542316124139)
                ·
                  refine ⟨6343404903179313474186209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4228936602119542316124139 6343404903179313474186209)
                  ·
                    refine ⟨4757553677384485105639657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6343404903179313474186209 4757553677384485105639657)
                    ·
                      refine ⟨3568165258038363829229743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757553677384485105639657 3568165258038363829229743)
                      ·
                        rfl

theorem cell23_6948977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_6948977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6948977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6948977 prefixEnd_6948977 := by exact prefixLift 6948977
  have htrace : WordTrace (prefixWord ++ tailWord_6948977) baseStart_6948977 baseEnd_6948977 := by
    simpa [prefixWord, tailWord_6948977, baseEnd_6948977] using wordTrace_append hprefix tailTrace_6948977
  have hstable : (prefixWord ++ tailWord_6948977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6948977).length < 2 ^ (prefixWord ++ tailWord_6948977).sum := by decide
  have hdescent : baseEnd_6948977 < baseStart_6948977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6948977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5]
def baseStart_6949019 : Nat := 118140960795 + 6949019 * 2 ^ 59
def prefixEnd_6949019 : Nat := 4983230072969 + 3 ^ 40 * 6949019 * 2
def baseEnd_6949019 : Nat := 3568186824225852664904549

theorem tailTrace_6949019 : CollatzResearch.WordTrace tailWord_6949019 prefixEnd_6949019 3568186824225852664904549 := by
  unfold tailWord_6949019
  simp only [CollatzResearch.WordTrace]
  refine ⟨253451544811898435804498111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168967696541265623869665407 253451544811898435804498111)
  ·
    refine ⟨380177317217847653706747167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253451544811898435804498111 380177317217847653706747167)
    ·
      refine ⟨570265975826771480560120751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380177317217847653706747167 570265975826771480560120751)
      ·
        refine ⟨855398963740157220840181127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570265975826771480560120751 855398963740157220840181127)
        ·
          refine ⟨1283098445610235831260271691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855398963740157220840181127 1283098445610235831260271691)
          ·
            refine ⟨1924647668415353746890407537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283098445610235831260271691 1924647668415353746890407537)
            ·
              refine ⟨1443485751311515310167805653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1924647668415353746890407537 1443485751311515310167805653)
              ·
                refine ⟨33831697296363640082057945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1443485751311515310167805653 33831697296363640082057945)
                ·
                  refine ⟨25373772972272730061543459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33831697296363640082057945 25373772972272730061543459)
                  ·
                    refine ⟨38060659458409095092315189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25373772972272730061543459 38060659458409095092315189)
                    ·
                      refine ⟨3568186824225852664904549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38060659458409095092315189 3568186824225852664904549)
                      ·
                        rfl

theorem cell23_6949019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_6949019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949019 prefixEnd_6949019 := by exact prefixLift 6949019
  have htrace : WordTrace (prefixWord ++ tailWord_6949019) baseStart_6949019 baseEnd_6949019 := by
    simpa [prefixWord, tailWord_6949019, baseEnd_6949019] using wordTrace_append hprefix tailTrace_6949019
  have hstable : (prefixWord ++ tailWord_6949019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949019).length < 2 ^ (prefixWord ++ tailWord_6949019).sum := by decide
  have hdescent : baseEnd_6949019 < baseStart_6949019 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949039 : List Nat := [1, 1, 2, 1, 2, 3, 1, 5, 7]
def baseStart_6949039 : Nat := 118140960795 + 6949039 * 2 ^ 59
def prefixEnd_6949039 : Nat := 4983230072969 + 3 ^ 40 * 6949039 * 2
def baseEnd_6949039 : Nat := 396466343759882509628273

theorem tailTrace_6949039 : CollatzResearch.WordTrace tailWord_6949039 prefixEnd_6949039 396466343759882509628273 := by
  unfold tailWord_6949039
  simp only [CollatzResearch.WordTrace]
  refine ⟨253452274271825979220226171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168968182847883986146817447 253452274271825979220226171)
  ·
    refine ⟨380178411407738968830339257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253452274271825979220226171 380178411407738968830339257)
    ·
      refine ⟨285133808555804226622754443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380178411407738968830339257 285133808555804226622754443)
      ·
        refine ⟨427700712833706339934131665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285133808555804226622754443 427700712833706339934131665)
        ·
          refine ⟨320775534625279754950598749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427700712833706339934131665 320775534625279754950598749)
          ·
            refine ⟨120290825484479908106474531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320775534625279754950598749 120290825484479908106474531)
            ·
              refine ⟨180436238226719862159711797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120290825484479908106474531 180436238226719862159711797)
              ·
                refine ⟨16915897333754987077472981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 180436238226719862159711797 16915897333754987077472981)
                ·
                  refine ⟨396466343759882509628273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16915897333754987077472981 396466343759882509628273)
                  ·
                    rfl

theorem cell23_6949039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 7].length) (baseStart_6949039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949039 prefixEnd_6949039 := by exact prefixLift 6949039
  have htrace : WordTrace (prefixWord ++ tailWord_6949039) baseStart_6949039 baseEnd_6949039 := by
    simpa [prefixWord, tailWord_6949039, baseEnd_6949039] using wordTrace_append hprefix tailTrace_6949039
  have hstable : (prefixWord ++ tailWord_6949039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949039).length < 2 ^ (prefixWord ++ tailWord_6949039).sum := by decide
  have hdescent : baseEnd_6949039 < baseStart_6949039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949044 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6949044 : Nat := 118140960795 + 6949044 * 2 ^ 59
def prefixEnd_6949044 : Nat := 4983230072969 + 3 ^ 40 * 6949044 * 2
def baseEnd_6949044 : Nat := 3568199661242215067091935

theorem tailTrace_6949044 : CollatzResearch.WordTrace tailWord_6949044 prefixEnd_6949044 3568199661242215067091935 := by
  unfold tailWord_6949044
  simp only [CollatzResearch.WordTrace]
  refine ⟨126726228318403932537079093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168968304424538576716105457 126726228318403932537079093)
  ·
    refine ⟨11880583904850368675351165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 126726228318403932537079093 11880583904850368675351165)
    ·
      refine ⟨4455218964318888253256687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11880583904850368675351165 4455218964318888253256687)
      ·
        refine ⟨6682828446478332379885031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4455218964318888253256687 6682828446478332379885031)
        ·
          refine ⟨10024242669717498569827547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682828446478332379885031 10024242669717498569827547)
          ·
            refine ⟨15036364004576247854741321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024242669717498569827547 15036364004576247854741321)
            ·
              refine ⟨11277273003432185891055991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15036364004576247854741321 11277273003432185891055991)
              ·
                refine ⟨16915909505148278836583987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11277273003432185891055991 16915909505148278836583987)
                ·
                  refine ⟨25373864257722418254875981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16915909505148278836583987 25373864257722418254875981)
                  ·
                    refine ⟨9515199096645906845578493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25373864257722418254875981 9515199096645906845578493)
                    ·
                      refine ⟨3568199661242215067091935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515199096645906845578493 3568199661242215067091935)
                      ·
                        rfl

theorem cell23_6949044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6949044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949044 prefixEnd_6949044 := by exact prefixLift 6949044
  have htrace : WordTrace (prefixWord ++ tailWord_6949044) baseStart_6949044 baseEnd_6949044 := by
    simpa [prefixWord, tailWord_6949044, baseEnd_6949044] using wordTrace_append hprefix tailTrace_6949044
  have hstable : (prefixWord ++ tailWord_6949044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949044).length < 2 ^ (prefixWord ++ tailWord_6949044).sum := by decide
  have hdescent : baseEnd_6949044 < baseStart_6949044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949050 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2]
def baseStart_6949050 : Nat := 118140960795 + 6949050 * 2 ^ 59
def prefixEnd_6949050 : Nat := 4983230072969 + 3 ^ 40 * 6949050 * 2
def baseEnd_6949050 : Nat := 3568202742126142043616907

theorem tailTrace_6949050 : CollatzResearch.WordTrace tailWord_6949050 prefixEnd_6949050 3568202742126142043616907 := by
  unfold tailWord_6949050
  simp only [CollatzResearch.WordTrace]
  refine ⟨63363168868696532024719151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168968450316524085399251069 63363168868696532024719151)
  ·
    refine ⟨95044753303044798037078727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63363168868696532024719151 95044753303044798037078727)
    ·
      refine ⟨142567129954567197055618091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 95044753303044798037078727 142567129954567197055618091)
      ·
        refine ⟨213850694931850795583427137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142567129954567197055618091 213850694931850795583427137)
        ·
          refine ⟨160388021198888096687570353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213850694931850795583427137 160388021198888096687570353)
          ·
            refine ⟨120291015899166072515677765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160388021198888096687570353 120291015899166072515677765)
            ·
              refine ⟨22554565481093638596689581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 120291015899166072515677765 22554565481093638596689581)
              ·
                refine ⟨8457962055410114473758593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22554565481093638596689581 8457962055410114473758593)
                ·
                  refine ⟨6343471541557585855318945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8457962055410114473758593 6343471541557585855318945)
                  ·
                    refine ⟨4757603656168189391489209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6343471541557585855318945 4757603656168189391489209)
                    ·
                      refine ⟨3568202742126142043616907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757603656168189391489209 3568202742126142043616907)
                      ·
                        rfl

theorem cell23_6949050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2].length) (baseStart_6949050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949050 prefixEnd_6949050 := by exact prefixLift 6949050
  have htrace : WordTrace (prefixWord ++ tailWord_6949050) baseStart_6949050 baseEnd_6949050 := by
    simpa [prefixWord, tailWord_6949050, baseEnd_6949050] using wordTrace_append hprefix tailTrace_6949050
  have hstable : (prefixWord ++ tailWord_6949050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949050).length < 2 ^ (prefixWord ++ tailWord_6949050).sum := by decide
  have hdescent : baseEnd_6949050 < baseStart_6949050 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949056 : List Nat := [2, 1, 1, 2, 5, 2, 1, 2, 7]
def baseStart_6949056 : Nat := 118140960795 + 6949056 * 2 ^ 59
def prefixEnd_6949056 : Nat := 4983230072969 + 3 ^ 40 * 6949056 * 2
def baseEnd_6949056 : Nat := 396467313667785446682431

theorem tailTrace_6949056 : CollatzResearch.WordTrace tailWord_6949056 prefixEnd_6949056 396467313667785446682431 := by
  unfold tailWord_6949056
  simp only [CollatzResearch.WordTrace]
  refine ⟨126726447156382195561797511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168968596208509594082396681 126726447156382195561797511)
  ·
    refine ⟨190089670734573293342696267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126726447156382195561797511 190089670734573293342696267)
    ·
      refine ⟨285134506101859940014044401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190089670734573293342696267 285134506101859940014044401)
      ·
        refine ⟨213850879576394955010533301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285134506101859940014044401 213850879576394955010533301)
        ·
          refine ⟨20048519960287027032237497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 213850879576394955010533301 20048519960287027032237497)
          ·
            refine ⟨15036389970215270274178123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20048519960287027032237497 15036389970215270274178123)
            ·
              refine ⟨22554584955322905411267185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15036389970215270274178123 22554584955322905411267185)
              ·
                refine ⟨16915938716492179058450389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22554584955322905411267185 16915938716492179058450389)
                ·
                  refine ⟨396467313667785446682431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16915938716492179058450389 396467313667785446682431)
                  ·
                    rfl

theorem cell23_6949056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 2, 7].length) (baseStart_6949056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949056 prefixEnd_6949056 := by exact prefixLift 6949056
  have htrace : WordTrace (prefixWord ++ tailWord_6949056) baseStart_6949056 baseEnd_6949056 := by
    simpa [prefixWord, tailWord_6949056, baseEnd_6949056] using wordTrace_append hprefix tailTrace_6949056
  have hstable : (prefixWord ++ tailWord_6949056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949056).length < 2 ^ (prefixWord ++ tailWord_6949056).sum := by decide
  have hdescent : baseEnd_6949056 < baseStart_6949056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949066 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_6949066 : Nat := 118140960795 + 6949066 * 2 ^ 59
def prefixEnd_6949066 : Nat := 4983230072969 + 3 ^ 40 * 6949066 * 2
def baseEnd_6949066 : Nat := 3568210957816613981016833

theorem tailTrace_6949066 : CollatzResearch.WordTrace tailWord_6949066 prefixEnd_6949066 3568210957816613981016833 := by
  unfold tailWord_6949066
  simp only [CollatzResearch.WordTrace]
  refine ⟨63363314760682040707864763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168968839361818775220972701 63363314760682040707864763)
  ·
    refine ⟨95044972141023061061797145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63363314760682040707864763 95044972141023061061797145)
    ·
      refine ⟨71283729105767295796347859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95044972141023061061797145 71283729105767295796347859)
      ·
        refine ⟨106925593658650943694521789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71283729105767295796347859 106925593658650943694521789)
        ·
          refine ⟨40097097621994103885445671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106925593658650943694521789 40097097621994103885445671)
          ·
            refine ⟨60145646432991155828168507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40097097621994103885445671 60145646432991155828168507)
            ·
              refine ⟨90218469649486733742252761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60145646432991155828168507 90218469649486733742252761)
              ·
                refine ⟨67663852237115050306689571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 90218469649486733742252761 67663852237115050306689571)
                ·
                  refine ⟨101495778355672575460034357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 67663852237115050306689571 101495778355672575460034357)
                  ·
                    refine ⟨9515229220844303949378221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101495778355672575460034357 9515229220844303949378221)
                    ·
                      refine ⟨3568210957816613981016833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515229220844303949378221 3568210957816613981016833)
                      ·
                        rfl

theorem cell23_6949066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_6949066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949066 prefixEnd_6949066 := by exact prefixLift 6949066
  have htrace : WordTrace (prefixWord ++ tailWord_6949066) baseStart_6949066 baseEnd_6949066 := by
    simpa [prefixWord, tailWord_6949066, baseEnd_6949066] using wordTrace_append hprefix tailTrace_6949066
  have hstable : (prefixWord ++ tailWord_6949066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949066).length < 2 ^ (prefixWord ++ tailWord_6949066).sum := by decide
  have hdescent : baseEnd_6949066 < baseStart_6949066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949084 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_6949084 : Nat := 118140960795 + 6949084 * 2 ^ 59
def prefixEnd_6949084 : Nat := 4983230072969 + 3 ^ 40 * 6949084 * 2
def baseEnd_6949084 : Nat := 3568220200468394910591751

theorem tailTrace_6949084 : CollatzResearch.WordTrace tailWord_6949084 prefixEnd_6949084 3568220200468394910591751 := by
  unfold tailWord_6949084
  simp only [CollatzResearch.WordTrace]
  refine ⟨126726957778331475952807153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168969277037775301270409537 126726957778331475952807153)
  ·
    refine ⟨95045218333748606964605365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126726957778331475952807153 95045218333748606964605365)
    ·
      refine ⟨8910489218788931902931753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 95045218333748606964605365 8910489218788931902931753)
      ·
        refine ⟨6682866914091698927198815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8910489218788931902931753 6682866914091698927198815)
        ·
          refine ⟨10024300371137548390798223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6682866914091698927198815 10024300371137548390798223)
          ·
            refine ⟨15036450556706322586197335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10024300371137548390798223 15036450556706322586197335)
            ·
              refine ⟨22554675835059483879296003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15036450556706322586197335 22554675835059483879296003)
              ·
                refine ⟨33832013752589225818944005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22554675835059483879296003 33832013752589225818944005)
                ·
                  refine ⟨6343502578610479841052001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33832013752589225818944005 6343502578610479841052001)
                  ·
                    refine ⟨4757626933957859880789001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6343502578610479841052001 4757626933957859880789001)
                    ·
                      refine ⟨3568220200468394910591751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757626933957859880789001 3568220200468394910591751)
                      ·
                        rfl

theorem cell23_6949084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_6949084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949084 prefixEnd_6949084 := by exact prefixLift 6949084
  have htrace : WordTrace (prefixWord ++ tailWord_6949084) baseStart_6949084 baseEnd_6949084 := by
    simpa [prefixWord, tailWord_6949084, baseEnd_6949084] using wordTrace_append hprefix tailTrace_6949084
  have hstable : (prefixWord ++ tailWord_6949084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949084).length < 2 ^ (prefixWord ++ tailWord_6949084).sum := by decide
  have hdescent : baseEnd_6949084 < baseStart_6949084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949143 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_6949143 : Nat := 118140960795 + 6949143 * 2 ^ 59
def prefixEnd_6949143 : Nat := 4983230072969 + 3 ^ 40 * 6949143 * 2
def baseEnd_6949143 : Nat := 3568250495827010179753979

theorem tailTrace_6949143 : CollatzResearch.WordTrace tailWord_6949143 prefixEnd_6949143 3568250495827010179753979 := by
  unfold tailWord_6949143
  simp only [CollatzResearch.WordTrace]
  refine ⟨253456067463449204982012083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168970711642299469988008055 253456067463449204982012083)
  ·
    refine ⟨380184101195173807473018125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253456067463449204982012083 380184101195173807473018125)
    ·
      refine ⟨142569037948190177802381797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380184101195173807473018125 142569037948190177802381797)
      ·
        refine ⟨26731694615285658337946587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 142569037948190177802381797 26731694615285658337946587)
        ·
          refine ⟨40097541922928487506919881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26731694615285658337946587 40097541922928487506919881)
          ·
            refine ⟨30073156442196365630189911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40097541922928487506919881 30073156442196365630189911)
            ·
              refine ⟨45109734663294548445284867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30073156442196365630189911 45109734663294548445284867)
              ·
                refine ⟨67664601994941822667927301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45109734663294548445284867 67664601994941822667927301)
                ·
                  refine ⟨12687112874051591750236369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67664601994941822667927301 12687112874051591750236369)
                  ·
                    refine ⟨9515334655538693812677277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12687112874051591750236369 9515334655538693812677277)
                    ·
                      refine ⟨3568250495827010179753979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515334655538693812677277 3568250495827010179753979)
                      ·
                        rfl

theorem cell23_6949143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_6949143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949143 prefixEnd_6949143 := by exact prefixLift 6949143
  have htrace : WordTrace (prefixWord ++ tailWord_6949143) baseStart_6949143 baseEnd_6949143 := by
    simpa [prefixWord, tailWord_6949143, baseEnd_6949143] using wordTrace_append hprefix tailTrace_6949143
  have hstable : (prefixWord ++ tailWord_6949143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949143).length < 2 ^ (prefixWord ++ tailWord_6949143).sum := by decide
  have hdescent : baseEnd_6949143 < baseStart_6949143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949200 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 2, 3, 2]
def baseStart_6949200 : Nat := 118140960795 + 6949200 * 2 ^ 59
def prefixEnd_6949200 : Nat := 4983230072969 + 3 ^ 40 * 6949200 * 2
def baseEnd_6949200 : Nat := 3568279764224316456741217

theorem tailTrace_6949200 : CollatzResearch.WordTrace tailWord_6949200 prefixEnd_6949200 3568279764224316456741217 := by
  unfold tailWord_6949200
  simp only [CollatzResearch.WordTrace]
  refine ⟨126729073212121351858418527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168972097616161802477891369 126729073212121351858418527)
  ·
    refine ⟨190093609818182027787627791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126729073212121351858418527 190093609818182027787627791)
    ·
      refine ⟨285140414727273041681441687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190093609818182027787627791 285140414727273041681441687)
      ·
        refine ⟨427710622090909562522162531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285140414727273041681441687 427710622090909562522162531)
        ·
          refine ⟨641565933136364343783243797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427710622090909562522162531 641565933136364343783243797)
          ·
            refine ⟨30073403115767078614839553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 641565933136364343783243797 30073403115767078614839553)
            ·
              refine ⟨22555052336825308961129665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30073403115767078614839553 22555052336825308961129665)
              ·
                refine ⟨16916289252618981720847249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22555052336825308961129665 16916289252618981720847249)
                ·
                  refine ⟨12687216939464236290635437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16916289252618981720847249 12687216939464236290635437)
                  ·
                    refine ⟨4757706352299088608988289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12687216939464236290635437 4757706352299088608988289)
                    ·
                      refine ⟨3568279764224316456741217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757706352299088608988289 3568279764224316456741217)
                      ·
                        rfl

theorem cell23_6949200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 2, 3, 2].length) (baseStart_6949200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949200 prefixEnd_6949200 := by exact prefixLift 6949200
  have htrace : WordTrace (prefixWord ++ tailWord_6949200) baseStart_6949200 baseEnd_6949200 := by
    simpa [prefixWord, tailWord_6949200, baseEnd_6949200] using wordTrace_append hprefix tailTrace_6949200
  have hstable : (prefixWord ++ tailWord_6949200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949200).length < 2 ^ (prefixWord ++ tailWord_6949200).sum := by decide
  have hdescent : baseEnd_6949200 < baseStart_6949200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949207 : List Nat := [1, 1, 3, 2, 3, 1, 3, 4, 1, 1, 3]
def baseStart_6949207 : Nat := 118140960795 + 6949207 * 2 ^ 59
def prefixEnd_6949207 : Nat := 4983230072969 + 3 ^ 40 * 6949207 * 2
def baseEnd_6949207 : Nat := 3568283358588897929353685

theorem tailTrace_6949207 : CollatzResearch.WordTrace tailWord_6949207 prefixEnd_6949207 3568283358588897929353685 := by
  unfold tailWord_6949207
  simp only [CollatzResearch.WordTrace]
  refine ⟨253458401735217343912341875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168972267823478229274894583 253458401735217343912341875)
  ·
    refine ⟨380187602602826015868512813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253458401735217343912341875 380187602602826015868512813)
    ·
      refine ⟨142570350976059755950692305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380187602602826015868512813 142570350976059755950692305)
      ·
        refine ⟨106927763232044816963019229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142570350976059755950692305 106927763232044816963019229)
        ·
          refine ⟨40097911212016806361132211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 106927763232044816963019229 40097911212016806361132211)
          ·
            refine ⟨60146866818025209541698317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40097911212016806361132211 60146866818025209541698317)
            ·
              refine ⟨22555075056759453578136869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 60146866818025209541698317 22555075056759453578136869)
              ·
                refine ⟨4229076573142397545900663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22555075056759453578136869 4229076573142397545900663)
                ·
                  refine ⟨6343614859713596318850995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229076573142397545900663 6343614859713596318850995)
                  ·
                    refine ⟨9515422289570394478276493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6343614859713596318850995 9515422289570394478276493)
                    ·
                      refine ⟨3568283358588897929353685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515422289570394478276493 3568283358588897929353685)
                      ·
                        rfl

theorem cell23_6949207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 4, 1, 1, 3].length) (baseStart_6949207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949207 prefixEnd_6949207 := by exact prefixLift 6949207
  have htrace : WordTrace (prefixWord ++ tailWord_6949207) baseStart_6949207 baseEnd_6949207 := by
    simpa [prefixWord, tailWord_6949207, baseEnd_6949207] using wordTrace_append hprefix tailTrace_6949207
  have hstable : (prefixWord ++ tailWord_6949207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949207).length < 2 ^ (prefixWord ++ tailWord_6949207).sum := by decide
  have hdescent : baseEnd_6949207 < baseStart_6949207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949223 : List Nat := [1, 1, 5, 1, 3, 1, 1, 3, 1, 6]
def baseStart_6949223 : Nat := 118140960795 + 6949223 * 2 ^ 59
def prefixEnd_6949223 : Nat := 4983230072969 + 3 ^ 40 * 6949223 * 2
def baseEnd_6949223 : Nat := 1189430524759789955584537

theorem tailTrace_6949223 : CollatzResearch.WordTrace tailWord_6949223 prefixEnd_6949223 1189430524759789955584537 := by
  unfold tailWord_6949223
  simp only [CollatzResearch.WordTrace]
  refine ⟨253458985303159378644924323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168972656868772919096616215 253458985303159378644924323)
  ·
    refine ⟨380188477954739067967386485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253458985303159378644924323 380188477954739067967386485)
    ·
      refine ⟨35642669808256787621942483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 380188477954739067967386485 35642669808256787621942483)
      ·
        refine ⟨53464004712385181432913725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35642669808256787621942483 53464004712385181432913725)
        ·
          refine ⟨20049001767144443037342647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53464004712385181432913725 20049001767144443037342647)
          ·
            refine ⟨30073502650716664556013971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20049001767144443037342647 30073502650716664556013971)
            ·
              refine ⟨45110253976074996834020957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30073502650716664556013971 45110253976074996834020957)
              ·
                refine ⟨16916345241028123812757859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45110253976074996834020957 16916345241028123812757859)
                ·
                  refine ⟨25374517861542185719136789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16916345241028123812757859 25374517861542185719136789)
                  ·
                    refine ⟨1189430524759789955584537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 25374517861542185719136789 1189430524759789955584537)
                    ·
                      rfl

theorem cell23_6949223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_6949223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949223 prefixEnd_6949223 := by exact prefixLift 6949223
  have htrace : WordTrace (prefixWord ++ tailWord_6949223) baseStart_6949223 baseEnd_6949223 := by
    simpa [prefixWord, tailWord_6949223, baseEnd_6949223] using wordTrace_append hprefix tailTrace_6949223
  have hstable : (prefixWord ++ tailWord_6949223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949223).length < 2 ^ (prefixWord ++ tailWord_6949223).sum := by decide
  have hdescent : baseEnd_6949223 < baseStart_6949223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949243 : List Nat := [1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4]
def baseStart_6949243 : Nat := 118140960795 + 6949243 * 2 ^ 59
def prefixEnd_6949243 : Nat := 4983230072969 + 3 ^ 40 * 6949243 * 2
def baseEnd_6949243 : Nat := 3568301843892459788503519

theorem tailTrace_6949243 : CollatzResearch.WordTrace tailWord_6949243 prefixEnd_6949243 3568301843892459788503519 := by
  unfold tailWord_6949243
  simp only [CollatzResearch.WordTrace]
  refine ⟨253459714763086922060652383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168973143175391281373768255 253459714763086922060652383)
  ·
    refine ⟨380189572144630383090978575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253459714763086922060652383 380189572144630383090978575)
    ·
      refine ⟨570284358216945574636467863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380189572144630383090978575 570284358216945574636467863)
      ·
        refine ⟨855426537325418361954701795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570284358216945574636467863 855426537325418361954701795)
        ·
          refine ⟨1283139805988127542932052693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855426537325418361954701795 1283139805988127542932052693)
          ·
            refine ⟨30073589202846739287469985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1283139805988127542932052693 30073589202846739287469985)
            ·
              refine ⟨22555191902135054465602489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30073589202846739287469985 22555191902135054465602489)
              ·
                refine ⟨16916393926601290849201867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22555191902135054465602489 16916393926601290849201867)
                ·
                  refine ⟨25374590889901936273802801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16916393926601290849201867 25374590889901936273802801)
                  ·
                    refine ⟨19030943167426452205352101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25374590889901936273802801 19030943167426452205352101)
                    ·
                      refine ⟨3568301843892459788503519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19030943167426452205352101 3568301843892459788503519)
                      ·
                        rfl

theorem cell23_6949243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].length) (baseStart_6949243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949243 prefixEnd_6949243 := by exact prefixLift 6949243
  have htrace : WordTrace (prefixWord ++ tailWord_6949243) baseStart_6949243 baseEnd_6949243 := by
    simpa [prefixWord, tailWord_6949243, baseEnd_6949243] using wordTrace_append hprefix tailTrace_6949243
  have hstable : (prefixWord ++ tailWord_6949243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949243).length < 2 ^ (prefixWord ++ tailWord_6949243).sum := by decide
  have hdescent : baseEnd_6949243 < baseStart_6949243 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949257 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 2, 4]
def baseStart_6949257 : Nat := 118140960795 + 6949257 * 2 ^ 59
def prefixEnd_6949257 : Nat := 4983230072969 + 3 ^ 40 * 6949257 * 2
def baseEnd_6949257 : Nat := 1189436344207207577909485

theorem tailTrace_6949257 : CollatzResearch.WordTrace tailWord_6949257 prefixEnd_6949257 1189436344207207577909485 := by
  unfold tailWord_6949257
  simp only [CollatzResearch.WordTrace]
  refine ⟨253460225385036202451662025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168973483590024134967774683 253460225385036202451662025)
  ·
    refine ⟨190095169038777151838746519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253460225385036202451662025 190095169038777151838746519)
    ·
      refine ⟨285142753558165727758119779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190095169038777151838746519 285142753558165727758119779)
      ·
        refine ⟨427714130337248591637179669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285142753558165727758119779 427714130337248591637179669)
        ·
          refine ⟨20049099859558527732992797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 427714130337248591637179669 20049099859558527732992797)
          ·
            refine ⟨7518412447334447899872299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20049099859558527732992797 7518412447334447899872299)
            ·
              refine ⟨11277618671001671849808449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518412447334447899872299 11277618671001671849808449)
              ·
                refine ⟨8458214003251253887356337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11277618671001671849808449 8458214003251253887356337)
                ·
                  refine ⟨6343660502438440415517253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8458214003251253887356337 6343660502438440415517253)
                  ·
                    refine ⟨1189436344207207577909485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6343660502438440415517253 1189436344207207577909485)
                    ·
                      rfl

theorem cell23_6949257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 2, 4].length) (baseStart_6949257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949257 prefixEnd_6949257 := by exact prefixLift 6949257
  have htrace : WordTrace (prefixWord ++ tailWord_6949257) baseStart_6949257 baseEnd_6949257 := by
    simpa [prefixWord, tailWord_6949257, baseEnd_6949257] using wordTrace_append hprefix tailTrace_6949257
  have hstable : (prefixWord ++ tailWord_6949257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949257).length < 2 ^ (prefixWord ++ tailWord_6949257).sum := by decide
  have hdescent : baseEnd_6949257 < baseStart_6949257 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949277 : List Nat := [1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_6949277 : Nat := 118140960795 + 6949277 * 2 ^ 59
def prefixEnd_6949277 : Nat := 4983230072969 + 3 ^ 40 * 6949277 * 2
def baseEnd_6949277 : Nat := 3568319302234712655478363

theorem tailTrace_6949277 : CollatzResearch.WordTrace tailWord_6949277 prefixEnd_6949277 3568319302234712655478363 := by
  unfold tailWord_6949277
  simp only [CollatzResearch.WordTrace]
  refine ⟨253460954844963745867390085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168973969896642497244926723 253460954844963745867390085)
  ·
    refine ⟨47523929033430702350135641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253460954844963745867390085 47523929033430702350135641)
    ·
      refine ⟨35642946775073026762601731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47523929033430702350135641 35642946775073026762601731)
      ·
        refine ⟨53464420162609540143902597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35642946775073026762601731 53464420162609540143902597)
        ·
          refine ⟨10024578780489288776981737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 53464420162609540143902597 10024578780489288776981737)
          ·
            refine ⟨7518434085366966582736303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10024578780489288776981737 7518434085366966582736303)
            ·
              refine ⟨11277651128050449874104455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518434085366966582736303 11277651128050449874104455)
              ·
                refine ⟨16916476692075674811156683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11277651128050449874104455 16916476692075674811156683)
                ·
                  refine ⟨25374715038113512216735025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16916476692075674811156683 25374715038113512216735025)
                  ·
                    refine ⟨19031036278585134162551269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 25374715038113512216735025 19031036278585134162551269)
                    ·
                      refine ⟨3568319302234712655478363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19031036278585134162551269 3568319302234712655478363)
                      ·
                        rfl

theorem cell23_6949277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_6949277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949277 prefixEnd_6949277 := by exact prefixLift 6949277
  have htrace : WordTrace (prefixWord ++ tailWord_6949277) baseStart_6949277 baseEnd_6949277 := by
    simpa [prefixWord, tailWord_6949277, baseEnd_6949277] using wordTrace_append hprefix tailTrace_6949277
  have hstable : (prefixWord ++ tailWord_6949277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949277).length < 2 ^ (prefixWord ++ tailWord_6949277).sum := by decide
  have hdescent : baseEnd_6949277 < baseStart_6949277 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949280 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3]
def baseStart_6949280 : Nat := 118140960795 + 6949280 * 2 ^ 59
def prefixEnd_6949280 : Nat := 4983230072969 + 3 ^ 40 * 6949280 * 2
def baseEnd_6949280 : Nat := 3568320842676676143740849

theorem tailTrace_6949280 : CollatzResearch.WordTrace tailWord_6949280 prefixEnd_6949280 3568320842676676143740849 := by
  unfold tailWord_6949280
  simp only [CollatzResearch.WordTrace]
  refine ⟨126730532131976438689874647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168974042842635251586499529 126730532131976438689874647)
  ·
    refine ⟨190095798197964658034811971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126730532131976438689874647 190095798197964658034811971)
    ·
      refine ⟨285143697296946987052217957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190095798197964658034811971 285143697296946987052217957)
      ·
        refine ⟨53464443243177560072290867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 285143697296946987052217957 53464443243177560072290867)
        ·
          refine ⟨80196664864766340108436301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53464443243177560072290867 80196664864766340108436301)
          ·
            refine ⟨30073749324287377540663613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80196664864766340108436301 30073749324287377540663613)
            ·
              refine ⟨11277655996607766577748855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30073749324287377540663613 11277655996607766577748855)
              ·
                refine ⟨16916483994911649866623283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11277655996607766577748855 16916483994911649866623283)
                ·
                  refine ⟨25374725992367474799934925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16916483994911649866623283 25374725992367474799934925)
                  ·
                    refine ⟨9515522247137803049975597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25374725992367474799934925 9515522247137803049975597)
                    ·
                      refine ⟨3568320842676676143740849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515522247137803049975597 3568320842676676143740849)
                      ·
                        rfl

theorem cell23_6949280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_6949280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949280 prefixEnd_6949280 := by exact prefixLift 6949280
  have htrace : WordTrace (prefixWord ++ tailWord_6949280) baseStart_6949280 baseEnd_6949280 := by
    simpa [prefixWord, tailWord_6949280, baseEnd_6949280] using wordTrace_append hprefix tailTrace_6949280
  have hstable : (prefixWord ++ tailWord_6949280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949280).length < 2 ^ (prefixWord ++ tailWord_6949280).sum := by decide
  have hdescent : baseEnd_6949280 < baseStart_6949280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949323 : List Nat := [1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 3]
def baseStart_6949323 : Nat := 118140960795 + 6949323 * 2 ^ 59
def prefixEnd_6949323 : Nat := 4983230072969 + 3 ^ 40 * 6949323 * 2
def baseEnd_6949323 : Nat := 3568342922344819475503151

theorem tailTrace_6949323 : CollatzResearch.WordTrace tailWord_6949323 prefixEnd_6949323 3568342922344819475503151 := by
  unfold tailWord_6949323
  simp only [CollatzResearch.WordTrace]
  refine ⟨253462632602797095723564623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168975088401864730482376415 253462632602797095723564623)
  ·
    refine ⟨380193948904195643585346935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253462632602797095723564623 380193948904195643585346935)
    ·
      refine ⟨570290923356293465378020403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380193948904195643585346935 570290923356293465378020403)
      ·
        refine ⟨855436385034440198067030605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570290923356293465378020403 855436385034440198067030605)
        ·
          refine ⟨320788644387915074275136477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 855436385034440198067030605 320788644387915074275136477)
          ·
            refine ⟨120295741645468152853176179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 320788644387915074275136477 120295741645468152853176179)
            ·
              refine ⟨180443612468202229279764269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 120295741645468152853176179 180443612468202229279764269)
              ·
                refine ⟨67666354675575835979911601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 180443612468202229279764269 67666354675575835979911601)
                ·
                  refine ⟨50749766006681876984933701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 67666354675575835979911601 50749766006681876984933701)
                  ·
                    refine ⟨9515581126252851934675069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 50749766006681876984933701 9515581126252851934675069)
                    ·
                      refine ⟨3568342922344819475503151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515581126252851934675069 3568342922344819475503151)
                      ·
                        rfl

theorem cell23_6949323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 3].length) (baseStart_6949323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949323 prefixEnd_6949323 := by exact prefixLift 6949323
  have htrace : WordTrace (prefixWord ++ tailWord_6949323) baseStart_6949323 baseEnd_6949323 := by
    simpa [prefixWord, tailWord_6949323, baseEnd_6949323] using wordTrace_append hprefix tailTrace_6949323
  have hstable : (prefixWord ++ tailWord_6949323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949323).length < 2 ^ (prefixWord ++ tailWord_6949323).sum := by decide
  have hdescent : baseEnd_6949323 < baseStart_6949323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949353 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 3]
def baseStart_6949353 : Nat := 118140960795 + 6949353 * 2 ^ 59
def prefixEnd_6949353 : Nat := 4983230072969 + 3 ^ 40 * 6949353 * 2
def baseEnd_6949353 : Nat := 3568358326764454358128013

theorem tailTrace_6949353 : CollatzResearch.WordTrace tailWord_6949353 prefixEnd_6949353 3568358326764454358128013 := by
  unfold tailWord_6949353
  simp only [CollatzResearch.WordTrace]
  refine ⟨253463726792688410847156713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168975817861792273898104475 253463726792688410847156713)
  ·
    refine ⟨190097795094516308135367535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253463726792688410847156713 190097795094516308135367535)
    ·
      refine ⟨285146692641774462203051303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190097795094516308135367535 285146692641774462203051303)
      ·
        refine ⟨427720038962661693304576955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285146692641774462203051303 427720038962661693304576955)
        ·
          refine ⟨641580058443992539956865433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427720038962661693304576955 641580058443992539956865433)
          ·
            refine ⟨481185043832994404967649075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 641580058443992539956865433 481185043832994404967649075)
            ·
              refine ⟨721777565749491607451473613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481185043832994404967649075 721777565749491607451473613)
              ·
                refine ⟨270666587156059352794302605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721777565749491607451473613 270666587156059352794302605)
                ·
                  refine ⟨101499970183522257297863477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 270666587156059352794302605 101499970183522257297863477)
                  ·
                    refine ⟨9515622204705211621674701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 101499970183522257297863477 9515622204705211621674701)
                    ·
                      refine ⟨3568358326764454358128013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515622204705211621674701 3568358326764454358128013)
                      ·
                        rfl

theorem cell23_6949353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 5, 3].length) (baseStart_6949353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949353 prefixEnd_6949353 := by exact prefixLift 6949353
  have htrace : WordTrace (prefixWord ++ tailWord_6949353) baseStart_6949353 baseEnd_6949353 := by
    simpa [prefixWord, tailWord_6949353, baseEnd_6949353] using wordTrace_append hprefix tailTrace_6949353
  have hstable : (prefixWord ++ tailWord_6949353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949353).length < 2 ^ (prefixWord ++ tailWord_6949353).sum := by decide
  have hdescent : baseEnd_6949353 < baseStart_6949353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949360 : List Nat := [2, 1, 1, 1, 3, 3, 2, 5, 5]
def baseStart_6949360 : Nat := 118140960795 + 6949360 * 2 ^ 59
def prefixEnd_6949360 : Nat := 4983230072969 + 3 ^ 40 * 6949360 * 2
def baseEnd_6949360 : Nat := 396484657903226203415609

theorem tailTrace_6949360 : CollatzResearch.WordTrace tailWord_6949360 prefixEnd_6949360 396484657903226203415609 := by
  unfold tailWord_6949360
  simp only [CollatzResearch.WordTrace]
  refine ⟨126731991051831525521330767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168975988069108700695107689 126731991051831525521330767)
  ·
    refine ⟨190097986577747288281996151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126731991051831525521330767 190097986577747288281996151)
    ·
      refine ⟨285146979866620932422994227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190097986577747288281996151 285146979866620932422994227)
      ·
        refine ⟨427720469799931398634491341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285146979866620932422994227 427720469799931398634491341)
        ·
          refine ⟨160395176174974274487934253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427720469799931398634491341 160395176174974274487934253)
          ·
            refine ⟨60148191065615352932975345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 160395176174974274487934253 60148191065615352932975345)
            ·
              refine ⟨45111143299211514699731509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60148191065615352932975345 45111143299211514699731509)
              ·
                refine ⟨4229169684301079503099829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45111143299211514699731509 4229169684301079503099829)
                ·
                  refine ⟨396484657903226203415609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4229169684301079503099829 396484657903226203415609)
                  ·
                    rfl

theorem cell23_6949360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 5].length) (baseStart_6949360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949360 prefixEnd_6949360 := by exact prefixLift 6949360
  have htrace : WordTrace (prefixWord ++ tailWord_6949360) baseStart_6949360 baseEnd_6949360 := by
    simpa [prefixWord, tailWord_6949360, baseEnd_6949360] using wordTrace_append hprefix tailTrace_6949360
  have hstable : (prefixWord ++ tailWord_6949360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949360).length < 2 ^ (prefixWord ++ tailWord_6949360).sum := by decide
  have hdescent : baseEnd_6949360 < baseStart_6949360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949377 : List Nat := [1, 2, 4, 1, 3, 2, 1, 4, 5]
def baseStart_6949377 : Nat := 118140960795 + 6949377 * 2 ^ 59
def prefixEnd_6949377 : Nat := 4983230072969 + 3 ^ 40 * 6949377 * 2
def baseEnd_6949377 : Nat := 396485627811129140469767

theorem tailTrace_6949377 : CollatzResearch.WordTrace tailWord_6949377 prefixEnd_6949377 396485627811129140469767 := by
  unfold tailWord_6949377
  simp only [CollatzResearch.WordTrace]
  refine ⟨253464602144601462946030385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168976401429734308630686923 253464602144601462946030385)
  ·
    refine ⟨190098451608451097209522789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253464602144601462946030385 190098451608451097209522789)
    ·
      refine ⟨35643459676584580726785523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190098451608451097209522789 35643459676584580726785523)
      ·
        refine ⟨53465189514876871090178285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35643459676584580726785523 53465189514876871090178285)
        ·
          refine ⟨20049446068078826658816857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53465189514876871090178285 20049446068078826658816857)
          ·
            refine ⟨15037084551059119994112643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20049446068078826658816857 15037084551059119994112643)
            ·
              refine ⟨22555626826588679991168965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15037084551059119994112643 22555626826588679991168965)
              ·
                refine ⟨4229180029985377498344181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22555626826588679991168965 4229180029985377498344181)
                ·
                  refine ⟨396485627811129140469767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4229180029985377498344181 396485627811129140469767)
                  ·
                    rfl

theorem cell23_6949377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 4, 5].length) (baseStart_6949377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949377 prefixEnd_6949377 := by exact prefixLift 6949377
  have htrace : WordTrace (prefixWord ++ tailWord_6949377) baseStart_6949377 baseEnd_6949377 := by
    simpa [prefixWord, tailWord_6949377, baseEnd_6949377] using wordTrace_append hprefix tailTrace_6949377
  have hstable : (prefixWord ++ tailWord_6949377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949377).length < 2 ^ (prefixWord ++ tailWord_6949377).sum := by decide
  have hdescent : baseEnd_6949377 < baseStart_6949377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949423 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_6949423 : Nat := 118140960795 + 6949423 * 2 ^ 59
def prefixEnd_6949423 : Nat := 4983230072969 + 3 ^ 40 * 6949423 * 2
def baseEnd_6949423 : Nat := 3568394270410269084252691

theorem tailTrace_6949423 : CollatzResearch.WordTrace tailWord_6949423 prefixEnd_6949423 3568394270410269084252691 := by
  unfold tailWord_6949423
  simp only [CollatzResearch.WordTrace]
  refine ⟨253466279902434812802204923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168977519934956541868136615 253466279902434812802204923)
  ·
    refine ⟨380199419853652219203307385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253466279902434812802204923 380199419853652219203307385)
    ·
      refine ⟨285149564890239164402480539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380199419853652219203307385 285149564890239164402480539)
      ·
        refine ⟨427724347335358746603720809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285149564890239164402480539 427724347335358746603720809)
        ·
          refine ⟨320793260501519059952790607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 427724347335358746603720809 320793260501519059952790607)
          ·
            refine ⟨481189890752278589929185911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320793260501519059952790607 481189890752278589929185911)
            ·
              refine ⟨721784836128417884893778867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481189890752278589929185911 721784836128417884893778867)
              ·
                refine ⟨1082677254192626827340668301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 721784836128417884893778867 1082677254192626827340668301)
                ·
                  refine ⟨406003970322235060252750613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1082677254192626827340668301 406003970322235060252750613)
                  ·
                    refine ⟨19031436108854768449347685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 406003970322235060252750613 19031436108854768449347685)
                    ·
                      refine ⟨3568394270410269084252691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19031436108854768449347685 3568394270410269084252691)
                      ·
                        rfl

theorem cell23_6949423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_6949423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949423 prefixEnd_6949423 := by exact prefixLift 6949423
  have htrace : WordTrace (prefixWord ++ tailWord_6949423) baseStart_6949423 baseEnd_6949423 := by
    simpa [prefixWord, tailWord_6949423, baseEnd_6949423] using wordTrace_append hprefix tailTrace_6949423
  have hstable : (prefixWord ++ tailWord_6949423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949423).length < 2 ^ (prefixWord ++ tailWord_6949423).sum := by decide
  have hdescent : baseEnd_6949423 < baseStart_6949423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949437 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 3, 4]
def baseStart_6949437 : Nat := 118140960795 + 6949437 * 2 ^ 59
def prefixEnd_6949437 : Nat := 4983230072969 + 3 ^ 40 * 6949437 * 2
def baseEnd_6949437 : Nat := 1189467153046477343159209

theorem tailTrace_6949437 : CollatzResearch.WordTrace tailWord_6949437 prefixEnd_6949437 1189467153046477343159209 := by
  unfold tailWord_6949437
  simp only [CollatzResearch.WordTrace]
  refine ⟨253466790524384093193214565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168977860349589395462143043 253466790524384093193214565)
  ·
    refine ⟨47525023223322017473727731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253466790524384093193214565 47525023223322017473727731)
    ·
      refine ⟨71287534834983026210591597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47525023223322017473727731 71287534834983026210591597)
      ·
        refine ⟨26732825563118634828971849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71287534834983026210591597 26732825563118634828971849)
        ·
          refine ⟨20049619172338976121728887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26732825563118634828971849 20049619172338976121728887)
          ·
            refine ⟨30074428758508464182593331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20049619172338976121728887 30074428758508464182593331)
            ·
              refine ⟨45111643137762696273889997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30074428758508464182593331 45111643137762696273889997)
              ·
                refine ⟨16916866176661011102708749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45111643137762696273889997 16916866176661011102708749)
                ·
                  refine ⟨6343824816247879163515781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16916866176661011102708749 6343824816247879163515781)
                  ·
                    refine ⟨1189467153046477343159209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6343824816247879163515781 1189467153046477343159209)
                    ·
                      rfl

theorem cell23_6949437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_6949437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949437 prefixEnd_6949437 := by exact prefixLift 6949437
  have htrace : WordTrace (prefixWord ++ tailWord_6949437) baseStart_6949437 baseEnd_6949437 := by
    simpa [prefixWord, tailWord_6949437, baseEnd_6949437] using wordTrace_append hprefix tailTrace_6949437
  have hstable : (prefixWord ++ tailWord_6949437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949437).length < 2 ^ (prefixWord ++ tailWord_6949437).sum := by decide
  have hdescent : baseEnd_6949437 < baseStart_6949437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949487 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 2]
def baseStart_6949487 : Nat := 118140960795 + 6949487 * 2 ^ 59
def prefixEnd_6949487 : Nat := 4983230072969 + 3 ^ 40 * 6949487 * 2
def baseEnd_6949487 : Nat := 3568427133172156833852397

theorem tailTrace_6949487 : CollatzResearch.WordTrace tailWord_6949487 prefixEnd_6949487 3568427133172156833852397 := by
  unfold tailWord_6949487
  simp only [CollatzResearch.WordTrace]
  refine ⟨253468614174202951732534715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168979076116135301155023143 253468614174202951732534715)
  ·
    refine ⟨380202921261304427598802073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253468614174202951732534715 380202921261304427598802073)
    ·
      refine ⟨285152190945978320699101555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380202921261304427598802073 285152190945978320699101555)
      ·
        refine ⟨427728286418967481048652333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285152190945978320699101555 427728286418967481048652333)
        ·
          refine ⟨160398107407112805393244625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 427728286418967481048652333 160398107407112805393244625)
          ·
            refine ⟨120298580555334604044933469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 160398107407112805393244625 120298580555334604044933469)
            ·
              refine ⟨45111967708250476516850051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 120298580555334604044933469 45111967708250476516850051)
              ·
                refine ⟨67667951562375714775275077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 45111967708250476516850051 67667951562375714775275077)
                ·
                  refine ⟨12687740917945446520364077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 67667951562375714775275077 12687740917945446520364077)
                  ·
                    refine ⟨4757902844229542445136529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12687740917945446520364077 4757902844229542445136529)
                    ·
                      refine ⟨3568427133172156833852397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4757902844229542445136529 3568427133172156833852397)
                      ·
                        rfl

theorem cell23_6949487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 4, 3, 2].length) (baseStart_6949487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949487 prefixEnd_6949487 := by exact prefixLift 6949487
  have htrace : WordTrace (prefixWord ++ tailWord_6949487) baseStart_6949487 baseEnd_6949487 := by
    simpa [prefixWord, tailWord_6949487, baseEnd_6949487] using wordTrace_append hprefix tailTrace_6949487
  have hstable : (prefixWord ++ tailWord_6949487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949487).length < 2 ^ (prefixWord ++ tailWord_6949487).sum := by decide
  have hdescent : baseEnd_6949487 < baseStart_6949487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949501 : List Nat := [1, 4, 1, 1, 6, 1, 2, 1, 6]
def baseStart_6949501 : Nat := 118140960795 + 6949501 * 2 ^ 59
def prefixEnd_6949501 : Nat := 4983230072969 + 3 ^ 40 * 6949501 * 2
def baseEnd_6949501 : Nat := 396492702433479975453037

theorem tailTrace_6949501 : CollatzResearch.WordTrace tailWord_6949501 prefixEnd_6949501 396492702433479975453037 := by
  unfold tailWord_6949501
  simp only [CollatzResearch.WordTrace]
  refine ⟨253469124796152232123544357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168979416530768154749029571 253469124796152232123544357)
  ·
    refine ⟨47525460899278543523164567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253469124796152232123544357 47525460899278543523164567)
    ·
      refine ⟨71288191348917815284746851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47525460899278543523164567 71288191348917815284746851)
      ·
        refine ⟨106932287023376722927120277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71288191348917815284746851 106932287023376722927120277)
        ·
          refine ⟨5012450954220783887208763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106932287023376722927120277 5012450954220783887208763)
          ·
            refine ⟨7518676431331175830813145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012450954220783887208763 7518676431331175830813145)
            ·
              refine ⟨5639007323498381873109859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7518676431331175830813145 5639007323498381873109859)
              ·
                refine ⟨8458510985247572809664789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639007323498381873109859 8458510985247572809664789)
                ·
                  refine ⟨396492702433479975453037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8458510985247572809664789 396492702433479975453037)
                  ·
                    rfl

theorem cell23_6949501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 6].length) (baseStart_6949501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949501 prefixEnd_6949501 := by exact prefixLift 6949501
  have htrace : WordTrace (prefixWord ++ tailWord_6949501) baseStart_6949501 baseEnd_6949501 := by
    simpa [prefixWord, tailWord_6949501, baseEnd_6949501] using wordTrace_append hprefix tailTrace_6949501
  have hstable : (prefixWord ++ tailWord_6949501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949501).length < 2 ^ (prefixWord ++ tailWord_6949501).sum := by decide
  have hdescent : baseEnd_6949501 < baseStart_6949501 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949557 : List Nat := [1, 3, 3, 3, 1, 1, 3, 8]
def baseStart_6949557 : Nat := 118140960795 + 6949557 * 2 ^ 59
def prefixEnd_6949557 : Nat := 4983230072969 + 3 ^ 40 * 6949557 * 2
def baseEnd_6949557 : Nat := 132165299141406354073225

theorem tailTrace_6949557 : CollatzResearch.WordTrace tailWord_6949557 prefixEnd_6949557 132165299141406354073225 := by
  unfold tailWord_6949557
  simp only [CollatzResearch.WordTrace]
  refine ⟨253471167283949353687582925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168980778189299569125055283 253471167283949353687582925)
  ·
    refine ⟨95051687731481007632843597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253471167283949353687582925 95051687731481007632843597)
    ·
      refine ⟨35644382899305377862316349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95051687731481007632843597 35644382899305377862316349)
      ·
        refine ⟨13366643587239516698368631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35644382899305377862316349 13366643587239516698368631)
        ·
          refine ⟨20049965380859275047552947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13366643587239516698368631 20049965380859275047552947)
          ·
            refine ⟨30074948071288912571329421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20049965380859275047552947 30074948071288912571329421)
            ·
              refine ⟨11278105526733342214248533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30074948071288912571329421 11278105526733342214248533)
              ·
                refine ⟨132165299141406354073225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11278105526733342214248533 132165299141406354073225)
                ·
                  rfl

theorem cell23_6949557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 8].length) (baseStart_6949557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949557 prefixEnd_6949557 := by exact prefixLift 6949557
  have htrace : WordTrace (prefixWord ++ tailWord_6949557) baseStart_6949557 baseEnd_6949557 := by
    simpa [prefixWord, tailWord_6949557, baseEnd_6949557] using wordTrace_append hprefix tailTrace_6949557
  have hstable : (prefixWord ++ tailWord_6949557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949557).length < 2 ^ (prefixWord ++ tailWord_6949557).sum := by decide
  have hdescent : baseEnd_6949557 < baseStart_6949557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949567 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_6949567 : Nat := 118140960795 + 6949567 * 2 ^ 59
def prefixEnd_6949567 : Nat := 4983230072969 + 3 ^ 40 * 6949567 * 2
def baseEnd_6949567 : Nat := 3568468211624516520852029

theorem tailTrace_6949567 : CollatzResearch.WordTrace tailWord_6949567 prefixEnd_6949567 3568468211624516520852029 := by
  unfold tailWord_6949567
  simp only [CollatzResearch.WordTrace]
  refine ⟨253471532013913125395446955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168981021342608750263631303 253471532013913125395446955)
  ·
    refine ⟨380207298020869688093170433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253471532013913125395446955 380207298020869688093170433)
    ·
      refine ⟨285155473515652266069877825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380207298020869688093170433 285155473515652266069877825)
      ·
        refine ⟨213866605136739199552408369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285155473515652266069877825 213866605136739199552408369)
        ·
          refine ⟨160399953852554399664306277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 213866605136739199552408369 160399953852554399664306277)
          ·
            refine ⟨30074991347353949937057427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160399953852554399664306277 30074991347353949937057427)
            ·
              refine ⟨45112487021030924905586141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30074991347353949937057427 45112487021030924905586141)
              ·
                refine ⟨16917182632886596839594803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45112487021030924905586141 16917182632886596839594803)
                ·
                  refine ⟨25375773949329895259392205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16917182632886596839594803 25375773949329895259392205)
                  ·
                    refine ⟨9515915230998710722272077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25375773949329895259392205 9515915230998710722272077)
                    ·
                      refine ⟨3568468211624516520852029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515915230998710722272077 3568468211624516520852029)
                      ·
                        rfl

theorem cell23_6949567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_6949567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949567 prefixEnd_6949567 := by exact prefixLift 6949567
  have htrace : WordTrace (prefixWord ++ tailWord_6949567) baseStart_6949567 baseEnd_6949567 := by
    simpa [prefixWord, tailWord_6949567, baseEnd_6949567] using wordTrace_append hprefix tailTrace_6949567
  have hstable : (prefixWord ++ tailWord_6949567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949567).length < 2 ^ (prefixWord ++ tailWord_6949567).sum := by decide
  have hdescent : baseEnd_6949567 < baseStart_6949567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949601 : List Nat := [1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 3]
def baseStart_6949601 : Nat := 118140960795 + 6949601 * 2 ^ 59
def prefixEnd_6949601 : Nat := 4983230072969 + 3 ^ 40 * 6949601 * 2
def baseEnd_6949601 : Nat := 3568485669966769387826873

theorem tailTrace_6949601 : CollatzResearch.WordTrace tailWord_6949601 prefixEnd_6949601 3568485669966769387826873 := by
  unfold tailWord_6949601
  simp only [CollatzResearch.WordTrace]
  refine ⟨253472772095789949202184657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168981848063859966134789771 253472772095789949202184657)
  ·
    refine ⟨190104579071842461901638493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253472772095789949202184657 190104579071842461901638493)
    ·
      refine ⟨71289217151940923213114435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190104579071842461901638493 71289217151940923213114435)
      ·
        refine ⟨106933825727911384819671653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71289217151940923213114435 106933825727911384819671653)
        ·
          refine ⟨20050092323983384653688435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 106933825727911384819671653 20050092323983384653688435)
          ·
            refine ⟨30075138485975076980532653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20050092323983384653688435 30075138485975076980532653)
            ·
              refine ⟨11278176932240653867699745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30075138485975076980532653 11278176932240653867699745)
              ·
                refine ⟨8458632699180490400774809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11278176932240653867699745 8458632699180490400774809)
                ·
                  refine ⟨6343974524385367800581107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8458632699180490400774809 6343974524385367800581107)
                  ·
                    refine ⟨9515961786578051700871661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6343974524385367800581107 9515961786578051700871661)
                    ·
                      refine ⟨3568485669966769387826873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515961786578051700871661 3568485669966769387826873)
                      ·
                        rfl

theorem cell23_6949601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_6949601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949601 prefixEnd_6949601 := by exact prefixLift 6949601
  have htrace : WordTrace (prefixWord ++ tailWord_6949601) baseStart_6949601 baseEnd_6949601 := by
    simpa [prefixWord, tailWord_6949601, baseEnd_6949601] using wordTrace_append hprefix tailTrace_6949601
  have hstable : (prefixWord ++ tailWord_6949601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949601).length < 2 ^ (prefixWord ++ tailWord_6949601).sum := by decide
  have hdescent : baseEnd_6949601 < baseStart_6949601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949618 : List Nat := [3, 2, 1, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_6949618 : Nat := 118140960795 + 6949618 * 2 ^ 59
def prefixEnd_6949618 : Nat := 4983230072969 + 3 ^ 40 * 6949618 * 2
def baseEnd_6949618 : Nat := 3568494399137895821314295

theorem tailTrace_6949618 : CollatzResearch.WordTrace tailWord_6949618 prefixEnd_6949618 3568494399137895821314295 := by
  unfold tailWord_6949618
  simp only [CollatzResearch.WordTrace]
  refine ⟨63368348034182090276388377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168982261424485574070369005 63368348034182090276388377)
  ·
    refine ⟨47526261025636567707291283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63368348034182090276388377 47526261025636567707291283)
    ·
      refine ⟨71289391538454851560936925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47526261025636567707291283 71289391538454851560936925)
      ·
        refine ⟨26733521826920569335351347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 71289391538454851560936925 26733521826920569335351347)
        ·
          refine ⟨40100282740380854003027021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26733521826920569335351347 40100282740380854003027021)
          ·
            refine ⟨15037606027642820251135133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40100282740380854003027021 15037606027642820251135133)
            ·
              refine ⟨5639102260366057594175675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15037606027642820251135133 5639102260366057594175675)
              ·
                refine ⟨8458653390549086391263513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639102260366057594175675 8458653390549086391263513)
                ·
                  refine ⟨6343990042911814793447635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8458653390549086391263513 6343990042911814793447635)
                  ·
                    refine ⟨9515985064367722190171453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6343990042911814793447635 9515985064367722190171453)
                    ·
                      refine ⟨3568494399137895821314295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9515985064367722190171453 3568494399137895821314295)
                      ·
                        rfl

theorem cell23_6949618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_6949618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949618 prefixEnd_6949618 := by exact prefixLift 6949618
  have htrace : WordTrace (prefixWord ++ tailWord_6949618) baseStart_6949618 baseEnd_6949618 := by
    simpa [prefixWord, tailWord_6949618, baseEnd_6949618] using wordTrace_append hprefix tailTrace_6949618
  have hstable : (prefixWord ++ tailWord_6949618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949618).length < 2 ^ (prefixWord ++ tailWord_6949618).sum := by decide
  have hdescent : baseEnd_6949618 < baseStart_6949618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949657 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 3]
def baseStart_6949657 : Nat := 118140960795 + 6949657 * 2 ^ 59
def prefixEnd_6949657 : Nat := 4983230072969 + 3 ^ 40 * 6949657 * 2
def baseEnd_6949657 : Nat := 3568514424883421168726615

theorem tailTrace_6949657 : CollatzResearch.WordTrace tailWord_6949657 prefixEnd_6949657 3568514424883421168726615 := by
  unfold tailWord_6949657
  simp only [CollatzResearch.WordTrace]
  refine ⟨253474814583587070766223225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168983209722391380510815483 253474814583587070766223225)
  ·
    refine ⟨190106110937690303074667419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253474814583587070766223225 190106110937690303074667419)
    ·
      refine ⟨285159166406535454612001129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190106110937690303074667419 285159166406535454612001129)
      ·
        refine ⟨213869374804901590959000847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285159166406535454612001129 213869374804901590959000847)
        ·
          refine ⟨320804062207352386438501271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 213869374804901590959000847 320804062207352386438501271)
          ·
            refine ⟨481206093311028579657751907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 320804062207352386438501271 481206093311028579657751907)
            ·
              refine ⟨721809139966542869486627861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 481206093311028579657751907 721809139966542869486627861)
              ·
                refine ⟨33834803435931697007185681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 721809139966542869486627861 33834803435931697007185681)
                ·
                  refine ⟨25376102576948772755389261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33834803435931697007185681 25376102576948772755389261)
                  ·
                    refine ⟨9516038466355789783270973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25376102576948772755389261 9516038466355789783270973)
                    ·
                      refine ⟨3568514424883421168726615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9516038466355789783270973 3568514424883421168726615)
                      ·
                        rfl

theorem cell23_6949657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 2, 3, 3].length) (baseStart_6949657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949657 prefixEnd_6949657 := by exact prefixLift 6949657
  have htrace : WordTrace (prefixWord ++ tailWord_6949657) baseStart_6949657 baseEnd_6949657 := by
    simpa [prefixWord, tailWord_6949657, baseEnd_6949657] using wordTrace_append hprefix tailTrace_6949657
  have hstable : (prefixWord ++ tailWord_6949657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949657).length < 2 ^ (prefixWord ++ tailWord_6949657).sum := by decide
  have hdescent : baseEnd_6949657 < baseStart_6949657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949664 : List Nat := [2, 1, 1, 5, 1, 4, 1, 1, 7]
def baseStart_6949664 : Nat := 118140960795 + 6949664 * 2 ^ 59
def prefixEnd_6949664 : Nat := 4983230072969 + 3 ^ 40 * 6949664 * 2
def baseEnd_6949664 : Nat := 396502002138666960148787

theorem tailTrace_6949664 : CollatzResearch.WordTrace tailWord_6949664 prefixEnd_6949664 396502002138666960148787 := by
  unfold tailWord_6949664
  simp only [CollatzResearch.WordTrace]
  refine ⟨126737534947280855480864023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168983379929707807307818697 126737534947280855480864023)
  ·
    refine ⟨190106302420921283221296035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126737534947280855480864023 190106302420921283221296035)
    ·
      refine ⟨285159453631381924831944053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190106302420921283221296035 285159453631381924831944053)
      ·
        refine ⟨26733698777942055452994755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285159453631381924831944053 26733698777942055452994755)
        ·
          refine ⟨40100548166913083179492133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26733698777942055452994755 40100548166913083179492133)
          ·
            refine ⟨7518852781296203096154775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40100548166913083179492133 7518852781296203096154775)
            ·
              refine ⟨11278279171944304644232163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7518852781296203096154775 11278279171944304644232163)
              ·
                refine ⟨16917418757916456966348245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11278279171944304644232163 16917418757916456966348245)
                ·
                  refine ⟨396502002138666960148787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16917418757916456966348245 396502002138666960148787)
                  ·
                    rfl

theorem cell23_6949664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 1, 7].length) (baseStart_6949664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949664 prefixEnd_6949664 := by exact prefixLift 6949664
  have htrace : WordTrace (prefixWord ++ tailWord_6949664) baseStart_6949664 baseEnd_6949664 := by
    simpa [prefixWord, tailWord_6949664, baseEnd_6949664] using wordTrace_append hprefix tailTrace_6949664
  have hstable : (prefixWord ++ tailWord_6949664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949664).length < 2 ^ (prefixWord ++ tailWord_6949664).sum := by decide
  have hdescent : baseEnd_6949664 < baseStart_6949664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949714 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_6949714 : Nat := 118140960795 + 6949714 * 2 ^ 59
def prefixEnd_6949714 : Nat := 4983230072969 + 3 ^ 40 * 6949714 * 2
def baseEnd_6949714 : Nat := 3568543693280727445713853

theorem tailTrace_6949714 : CollatzResearch.WordTrace tailWord_6949714 prefixEnd_6949714 3568543693280727445713853 := by
  unfold tailWord_6949714
  simp only [CollatzResearch.WordTrace]
  refine ⟨63369223386095142375262049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168984595696253713000698797 63369223386095142375262049)
  ·
    refine ⟨47526917539571356781446537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 63369223386095142375262049 47526917539571356781446537)
    ·
      refine ⟨35645188154678517586084903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47526917539571356781446537 35645188154678517586084903)
      ·
        refine ⟨53467782232017776379127355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35645188154678517586084903 53467782232017776379127355)
        ·
          refine ⟨80201673348026664568691033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53467782232017776379127355 80201673348026664568691033)
          ·
            refine ⟨60151255011019998426518275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80201673348026664568691033 60151255011019998426518275)
            ·
              refine ⟨90226882516529997639777413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60151255011019998426518275 90226882516529997639777413)
              ·
                refine ⟨16917540471849374557458265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 90226882516529997639777413 16917540471849374557458265)
                ·
                  refine ⟨12688155353887030918093699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16917540471849374557458265 12688155353887030918093699)
                  ·
                    refine ⟨19032233030830546377140549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12688155353887030918093699 19032233030830546377140549)
                    ·
                      refine ⟨3568543693280727445713853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19032233030830546377140549 3568543693280727445713853)
                      ·
                        rfl

theorem cell23_6949714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_6949714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949714 prefixEnd_6949714 := by exact prefixLift 6949714
  have htrace : WordTrace (prefixWord ++ tailWord_6949714) baseStart_6949714 baseEnd_6949714 := by
    simpa [prefixWord, tailWord_6949714, baseEnd_6949714] using wordTrace_append hprefix tailTrace_6949714
  have hstable : (prefixWord ++ tailWord_6949714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949714).length < 2 ^ (prefixWord ++ tailWord_6949714).sum := by decide
  have hdescent : baseEnd_6949714 < baseStart_6949714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949717 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_6949717 : Nat := 118140960795 + 6949717 * 2 ^ 59
def prefixEnd_6949717 : Nat := 4983230072969 + 3 ^ 40 * 6949717 * 2
def baseEnd_6949717 : Nat := 3568545233722690933976339

theorem tailTrace_6949717 : CollatzResearch.WordTrace tailWord_6949717 prefixEnd_6949717 3568545233722690933976339 := by
  unfold tailWord_6949717
  simp only [CollatzResearch.WordTrace]
  refine ⟨253477002963369701013407405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168984668642246467342271603 253477002963369701013407405)
  ·
    refine ⟨95053876111263637880027777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253477002963369701013407405 95053876111263637880027777)
    ·
      refine ⟨71290407083447728410020833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95053876111263637880027777 71290407083447728410020833)
      ·
        refine ⟨53467805312585796307515625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71290407083447728410020833 53467805312585796307515625)
        ·
          refine ⟨40100853984439347230636719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53467805312585796307515625 40100853984439347230636719)
          ·
            refine ⟨60151280976659020845955079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40100853984439347230636719 60151280976659020845955079)
            ·
              refine ⟨90226921464988531268932619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60151280976659020845955079 90226921464988531268932619)
              ·
                refine ⟨135340382197482796903398929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90226921464988531268932619 135340382197482796903398929)
                ·
                  refine ⟨101505286648112097677549197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 135340382197482796903398929 101505286648112097677549197)
                  ·
                    refine ⟨38064482493042036629080949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 101505286648112097677549197 38064482493042036629080949)
                    ·
                      refine ⟨3568545233722690933976339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38064482493042036629080949 3568545233722690933976339)
                      ·
                        rfl

theorem cell23_6949717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_6949717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949717 prefixEnd_6949717 := by exact prefixLift 6949717
  have htrace : WordTrace (prefixWord ++ tailWord_6949717) baseStart_6949717 baseEnd_6949717 := by
    simpa [prefixWord, tailWord_6949717, baseEnd_6949717] using wordTrace_append hprefix tailTrace_6949717
  have hstable : (prefixWord ++ tailWord_6949717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949717).length < 2 ^ (prefixWord ++ tailWord_6949717).sum := by decide
  have hdescent : baseEnd_6949717 < baseStart_6949717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949731 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 2, 4, 2]
def baseStart_6949731 : Nat := 118140960795 + 6949731 * 2 ^ 59
def prefixEnd_6949731 : Nat := 4983230072969 + 3 ^ 40 * 6949731 * 2
def baseEnd_6949731 : Nat := 3568552422451853879201275

theorem tailTrace_6949731 : CollatzResearch.WordTrace tailWord_6949731 prefixEnd_6949731 3568552422451853879201275 := by
  unfold tailWord_6949731
  simp only [CollatzResearch.WordTrace]
  refine ⟨253477513585318981404417047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168985009056879320936278031 253477513585318981404417047)
  ·
    refine ⟨380216270377978472106625571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253477513585318981404417047 380216270377978472106625571)
    ·
      refine ⟨570324405566967708159938357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380216270377978472106625571 570324405566967708159938357)
      ·
        refine ⟨53467913021903222639994221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 570324405566967708159938357 53467913021903222639994221)
        ·
          refine ⟨20050467383213708489997833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53467913021903222639994221 20050467383213708489997833)
          ·
            refine ⟨15037850537410281367498375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20050467383213708489997833 15037850537410281367498375)
            ·
              refine ⟨22556775806115422051247563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15037850537410281367498375 22556775806115422051247563)
              ·
                refine ⟨33835163709173133076871345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22556775806115422051247563 33835163709173133076871345)
                ·
                  refine ⟨25376372781879849807653509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33835163709173133076871345 25376372781879849807653509)
                  ·
                    refine ⟨4758069896602471838935033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 25376372781879849807653509 4758069896602471838935033)
                    ·
                      refine ⟨3568552422451853879201275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758069896602471838935033 3568552422451853879201275)
                      ·
                        rfl

theorem cell23_6949731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_6949731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949731 prefixEnd_6949731 := by exact prefixLift 6949731
  have htrace : WordTrace (prefixWord ++ tailWord_6949731) baseStart_6949731 baseEnd_6949731 := by
    simpa [prefixWord, tailWord_6949731, baseEnd_6949731] using wordTrace_append hprefix tailTrace_6949731
  have hstable : (prefixWord ++ tailWord_6949731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949731).length < 2 ^ (prefixWord ++ tailWord_6949731).sum := by decide
  have hdescent : baseEnd_6949731 < baseStart_6949731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949781 : List Nat := [1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 3]
def baseStart_6949781 : Nat := 118140960795 + 6949781 * 2 ^ 59
def prefixEnd_6949781 : Nat := 4983230072969 + 3 ^ 40 * 6949781 * 2
def baseEnd_6949781 : Nat := 3568578096484578683576045

theorem tailTrace_6949781 : CollatzResearch.WordTrace tailWord_6949781 prefixEnd_6949781 3568578096484578683576045 := by
  unfold tailWord_6949781
  simp only [CollatzResearch.WordTrace]
  refine ⟨253479337235137839943737197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168986224823425226629158131 253479337235137839943737197)
  ·
    refine ⟨95054751463176689978901449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 253479337235137839943737197 95054751463176689978901449)
    ·
      refine ⟨71291063597382517484176087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95054751463176689978901449 71291063597382517484176087)
      ·
        refine ⟨106936595396073776226264131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71291063597382517484176087 106936595396073776226264131)
        ·
          refine ⟨160404893094110664339396197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 106936595396073776226264131 160404893094110664339396197)
          ·
            refine ⟨30075917455145749563636787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 160404893094110664339396197 30075917455145749563636787)
            ·
              refine ⟨45113876182718624345455181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30075917455145749563636787 45113876182718624345455181)
              ·
                refine ⟨16917703568519484129545693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45113876182718624345455181 16917703568519484129545693)
                ·
                  refine ⟨6344138838194806548579635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16917703568519484129545693 6344138838194806548579635)
                  ·
                    refine ⟨9516208257292209822869453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6344138838194806548579635 9516208257292209822869453)
                    ·
                      refine ⟨3568578096484578683576045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9516208257292209822869453 3568578096484578683576045)
                      ·
                        rfl

theorem cell23_6949781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3, 3, 1, 3].length) (baseStart_6949781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949781 prefixEnd_6949781 := by exact prefixLift 6949781
  have htrace : WordTrace (prefixWord ++ tailWord_6949781) baseStart_6949781 baseEnd_6949781 := by
    simpa [prefixWord, tailWord_6949781, baseEnd_6949781] using wordTrace_append hprefix tailTrace_6949781
  have hstable : (prefixWord ++ tailWord_6949781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949781).length < 2 ^ (prefixWord ++ tailWord_6949781).sum := by decide
  have hdescent : baseEnd_6949781 < baseStart_6949781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949788 : List Nat := [2, 2, 3, 3, 2, 1, 3, 1, 6]
def baseStart_6949788 : Nat := 118140960795 + 6949788 * 2 ^ 59
def prefixEnd_6949788 : Nat := 4983230072969 + 3 ^ 40 * 6949788 * 2
def baseEnd_6949788 : Nat := 396509076761017795132057

theorem tailTrace_6949788 : CollatzResearch.WordTrace tailWord_6949788 prefixEnd_6949788 396509076761017795132057 := by
  unfold tailWord_6949788
  simp only [CollatzResearch.WordTrace]
  refine ⟨126739796273056240069621009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168986395030741653426161345 126739796273056240069621009)
  ·
    refine ⟨95054847204792180052215757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 126739796273056240069621009 95054847204792180052215757)
    ·
      refine ⟨35645567701797067519580909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 95054847204792180052215757 35645567701797067519580909)
      ·
        refine ⟨13367087888173900319842841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35645567701797067519580909 13367087888173900319842841)
        ·
          refine ⟨10025315916130425239882131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13367087888173900319842841 10025315916130425239882131)
          ·
            refine ⟨15037973874195637859823197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10025315916130425239882131 15037973874195637859823197)
            ·
              refine ⟨5639240202823364197433699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15037973874195637859823197 5639240202823364197433699)
              ·
                refine ⟨8458860304235046296150549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639240202823364197433699 8458860304235046296150549)
                ·
                  refine ⟨396509076761017795132057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8458860304235046296150549 396509076761017795132057)
                  ·
                    rfl

theorem cell23_6949788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3, 1, 6].length) (baseStart_6949788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949788 prefixEnd_6949788 := by exact prefixLift 6949788
  have htrace : WordTrace (prefixWord ++ tailWord_6949788) baseStart_6949788 baseEnd_6949788 := by
    simpa [prefixWord, tailWord_6949788, baseEnd_6949788] using wordTrace_append hprefix tailTrace_6949788
  have hstable : (prefixWord ++ tailWord_6949788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949788).length < 2 ^ (prefixWord ++ tailWord_6949788).sum := by decide
  have hdescent : baseEnd_6949788 < baseStart_6949788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949791 : List Nat := [1, 1, 2, 5, 2, 1, 1, 2, 1, 5, 2]
def baseStart_6949791 : Nat := 118140960795 + 6949791 * 2 ^ 59
def prefixEnd_6949791 : Nat := 4983230072969 + 3 ^ 40 * 6949791 * 2
def baseEnd_6949791 : Nat := 3568583231291123644450999

theorem tailTrace_6949791 : CollatzResearch.WordTrace tailWord_6949791 prefixEnd_6949791 3568583231291123644450999 := by
  unfold tailWord_6949791
  simp only [CollatzResearch.WordTrace]
  refine ⟨253479701965101611651601227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168986467976734407767734151 253479701965101611651601227)
  ·
    refine ⟨380219552947652417477401841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253479701965101611651601227 380219552947652417477401841)
    ·
      refine ⟨285164664710739313108051381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380219552947652417477401841 285164664710739313108051381)
      ·
        refine ⟨26734187316631810603879817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285164664710739313108051381 26734187316631810603879817)
        ·
          refine ⟨20050640487473857952909863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26734187316631810603879817 20050640487473857952909863)
          ·
            refine ⟨30075960731210786929364795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20050640487473857952909863 30075960731210786929364795)
            ·
              refine ⟨45113941096816180394047193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30075960731210786929364795 45113941096816180394047193)
              ·
                refine ⟨33835455822612135295535395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45113941096816180394047193 33835455822612135295535395)
                ·
                  refine ⟨50753183733918202943303093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33835455822612135295535395 50753183733918202943303093)
                  ·
                    refine ⟨4758110975054831525934665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50753183733918202943303093 4758110975054831525934665)
                    ·
                      refine ⟨3568583231291123644450999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758110975054831525934665 3568583231291123644450999)
                      ·
                        rfl

theorem cell23_6949791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 2, 1, 5, 2].length) (baseStart_6949791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949791 prefixEnd_6949791 := by exact prefixLift 6949791
  have htrace : WordTrace (prefixWord ++ tailWord_6949791) baseStart_6949791 baseEnd_6949791 := by
    simpa [prefixWord, tailWord_6949791, baseEnd_6949791] using wordTrace_append hprefix tailTrace_6949791
  have hstable : (prefixWord ++ tailWord_6949791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949791).length < 2 ^ (prefixWord ++ tailWord_6949791).sum := by decide
  have hdescent : baseEnd_6949791 < baseStart_6949791 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949824 : List Nat := [2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5]
def baseStart_6949824 : Nat := 118140960795 + 6949824 * 2 ^ 59
def prefixEnd_6949824 : Nat := 4983230072969 + 3 ^ 40 * 6949824 * 2
def baseEnd_6949824 : Nat := 3568600176152722015338347

theorem tailTrace_6949824 : CollatzResearch.WordTrace tailWord_6949824 prefixEnd_6949824 3568600176152722015338347 := by
  unfold tailWord_6949824
  simp only [CollatzResearch.WordTrace]
  refine ⟨126740452786991029143776263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168987270382654705525035017 126740452786991029143776263)
  ·
    refine ⟨190110679180486543715664395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126740452786991029143776263 190110679180486543715664395)
    ·
      refine ⟨285166018770729815573496593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190110679180486543715664395 285166018770729815573496593)
      ·
        refine ⟨213874514078047361680122445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 285166018770729815573496593 213874514078047361680122445)
        ·
          refine ⟨80202942779267760630045917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 213874514078047361680122445 80202942779267760630045917)
          ·
            refine ⟨30076103542225410236267219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80202942779267760630045917 30076103542225410236267219)
            ·
              refine ⟨45114155313338115354400829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30076103542225410236267219 45114155313338115354400829)
              ·
                refine ⟨16917808242501793257900311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 45114155313338115354400829 16917808242501793257900311)
                ·
                  refine ⟨25376712363752689886850467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16917808242501793257900311 25376712363752689886850467)
                  ·
                    refine ⟨38065068545629034830275701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 25376712363752689886850467 38065068545629034830275701)
                    ·
                      refine ⟨3568600176152722015338347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38065068545629034830275701 3568600176152722015338347)
                      ·
                        rfl

theorem cell23_6949824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_6949824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949824 prefixEnd_6949824 := by exact prefixLift 6949824
  have htrace : WordTrace (prefixWord ++ tailWord_6949824) baseStart_6949824 baseEnd_6949824 := by
    simpa [prefixWord, tailWord_6949824, baseEnd_6949824] using wordTrace_append hprefix tailTrace_6949824
  have hstable : (prefixWord ++ tailWord_6949824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949824).length < 2 ^ (prefixWord ++ tailWord_6949824).sum := by decide
  have hdescent : baseEnd_6949824 < baseStart_6949824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949832 : List Nat := [2, 1, 3, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_6949832 : Nat := 118140960795 + 6949832 * 2 ^ 59
def prefixEnd_6949832 : Nat := 4983230072969 + 3 ^ 40 * 6949832 * 2
def baseEnd_6949832 : Nat := 3568604283997957984038311

theorem tailTrace_6949832 : CollatzResearch.WordTrace tailWord_6949832 prefixEnd_6949832 3568604283997957984038311 := by
  unfold tailWord_6949832
  simp only [CollatzResearch.WordTrace]
  refine ⟨126740598678976537826921875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168987464905302050435895833 126740598678976537826921875)
  ·
    refine ⟨190110898018464806740382813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126740598678976537826921875 190110898018464806740382813)
    ·
      refine ⟨71291586756924302527643555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 190110898018464806740382813 71291586756924302527643555)
      ·
        refine ⟨106937380135386453791465333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 71291586756924302527643555 106937380135386453791465333)
        ·
          refine ⟨10025379387692480042949875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 106937380135386453791465333 10025379387692480042949875)
          ·
            refine ⟨15038069081538720064424813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10025379387692480042949875 15038069081538720064424813)
            ·
              refine ⟨5639275905577020024159305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15038069081538720064424813 5639275905577020024159305)
              ·
                refine ⟨4229456929182765018119479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5639275905577020024159305 4229456929182765018119479)
                ·
                  refine ⟨6344185393774147527179219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229456929182765018119479 6344185393774147527179219)
                  ·
                    refine ⟨9516278090661221290768829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6344185393774147527179219 9516278090661221290768829)
                    ·
                      refine ⟨3568604283997957984038311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9516278090661221290768829 3568604283997957984038311)
                      ·
                        rfl

theorem cell23_6949832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_6949832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949832 prefixEnd_6949832 := by exact prefixLift 6949832
  have htrace : WordTrace (prefixWord ++ tailWord_6949832) baseStart_6949832 baseEnd_6949832 := by
    simpa [prefixWord, tailWord_6949832, baseEnd_6949832] using wordTrace_append hprefix tailTrace_6949832
  have hstable : (prefixWord ++ tailWord_6949832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949832).length < 2 ^ (prefixWord ++ tailWord_6949832).sum := by decide
  have hdescent : baseEnd_6949832 < baseStart_6949832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949844 : List Nat := [2, 4, 1, 2, 1, 2, 1, 10]
def baseStart_6949844 : Nat := 118140960795 + 6949844 * 2 ^ 59
def prefixEnd_6949844 : Nat := 4983230072969 + 3 ^ 40 * 6949844 * 2
def baseEnd_6949844 : Nat := 132170757250585627299565

theorem tailTrace_6949844 : CollatzResearch.WordTrace tailWord_6949844 prefixEnd_6949844 132170757250585627299565 := by
  unfold tailWord_6949844
  simp only [CollatzResearch.WordTrace]
  refine ⟨126740817516954800851640293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168987756689273067802187057 126740817516954800851640293)
  ·
    refine ⟨23763903284429025159682555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 126740817516954800851640293 23763903284429025159682555)
    ·
      refine ⟨35645854926643537739523833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23763903284429025159682555 35645854926643537739523833)
      ·
        refine ⟨26734391194982653304642875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35645854926643537739523833 26734391194982653304642875)
        ·
          refine ⟨40101586792473979956964313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26734391194982653304642875 40101586792473979956964313)
          ·
            refine ⟨30076190094355484967723235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 40101586792473979956964313 30076190094355484967723235)
            ·
              refine ⟨45114285141533227451584853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30076190094355484967723235 45114285141533227451584853)
              ·
                refine ⟨132170757250585627299565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 45114285141533227451584853 132170757250585627299565)
                ·
                  rfl

theorem cell23_6949844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 10].length) (baseStart_6949844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949844 prefixEnd_6949844 := by exact prefixLift 6949844
  have htrace : WordTrace (prefixWord ++ tailWord_6949844) baseStart_6949844 baseEnd_6949844 := by
    simpa [prefixWord, tailWord_6949844, baseEnd_6949844] using wordTrace_append hprefix tailTrace_6949844
  have hstable : (prefixWord ++ tailWord_6949844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949844).length < 2 ^ (prefixWord ++ tailWord_6949844).sum := by decide
  have hdescent : baseEnd_6949844 < baseStart_6949844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949848 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 2, 4]
def baseStart_6949848 : Nat := 118140960795 + 6949848 * 2 ^ 59
def prefixEnd_6949848 : Nat := 4983230072969 + 3 ^ 40 * 6949848 * 2
def baseEnd_6949848 : Nat := 1189537499896143307146079

theorem tailTrace_6949848 : CollatzResearch.WordTrace tailWord_6949848 prefixEnd_6949848 1189537499896143307146079 := by
  unfold tailWord_6949848
  simp only [CollatzResearch.WordTrace]
  refine ⟨126740890462947555193213099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168987853950596740257617465 126740890462947555193213099)
  ·
    refine ⟨190111335694421332789819649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 126740890462947555193213099 190111335694421332789819649)
    ·
      refine ⟨142583501770815999592364737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 190111335694421332789819649 142583501770815999592364737)
      ·
        refine ⟨106937626328111999694273553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 142583501770815999592364737 106937626328111999694273553)
        ·
          refine ⟨80203219746083999770705165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 106937626328111999694273553 80203219746083999770705165)
          ·
            refine ⟨30076207404781499914014437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80203219746083999770705165 30076207404781499914014437)
            ·
              refine ⟨5639288888396531233877707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30076207404781499914014437 5639288888396531233877707)
              ·
                refine ⟨8458933332594796850816561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5639288888396531233877707 8458933332594796850816561)
                ·
                  refine ⟨6344199999446097638112421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8458933332594796850816561 6344199999446097638112421)
                  ·
                    refine ⟨1189537499896143307146079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6344199999446097638112421 1189537499896143307146079)
                    ·
                      rfl

theorem cell23_6949848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_6949848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949848 prefixEnd_6949848 := by exact prefixLift 6949848
  have htrace : WordTrace (prefixWord ++ tailWord_6949848) baseStart_6949848 baseEnd_6949848 := by
    simpa [prefixWord, tailWord_6949848, baseEnd_6949848] using wordTrace_append hprefix tailTrace_6949848
  have hstable : (prefixWord ++ tailWord_6949848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949848).length < 2 ^ (prefixWord ++ tailWord_6949848).sum := by decide
  have hdescent : baseEnd_6949848 < baseStart_6949848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949855 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 1, 1, 4]
def baseStart_6949855 : Nat := 118140960795 + 6949855 * 2 ^ 59
def prefixEnd_6949855 : Nat := 4983230072969 + 3 ^ 40 * 6949855 * 2
def baseEnd_6949855 : Nat := 3568616094053011394050705

theorem tailTrace_6949855 : CollatzResearch.WordTrace tailWord_6949855 prefixEnd_6949855 3568616094053011394050705 := by
  unfold tailWord_6949855
  simp only [CollatzResearch.WordTrace]
  refine ⟨253482036236869750581931019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168988024157913167054620679 253482036236869750581931019)
  ·
    refine ⟨380223054355304625872896529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253482036236869750581931019 380223054355304625872896529)
    ·
      refine ⟨285167290766478469404672397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380223054355304625872896529 285167290766478469404672397)
      ·
        refine ⟨106937734037429426026752149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 285167290766478469404672397 106937734037429426026752149)
        ·
          refine ⟨5012706283004504345004007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 106937734037429426026752149 5012706283004504345004007)
          ·
            refine ⟨7519059424506756517506011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012706283004504345004007 7519059424506756517506011)
            ·
              refine ⟨11278589136760134776259017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7519059424506756517506011 11278589136760134776259017)
              ·
                refine ⟨8458941852570101082194263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11278589136760134776259017 8458941852570101082194263)
                ·
                  refine ⟨12688412778855151623291395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8458941852570101082194263 12688412778855151623291395)
                  ·
                    refine ⟨19032619168282727434937093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12688412778855151623291395 19032619168282727434937093)
                    ·
                      refine ⟨3568616094053011394050705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19032619168282727434937093 3568616094053011394050705)
                      ·
                        rfl

theorem cell23_6949855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 1, 4].length) (baseStart_6949855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949855 prefixEnd_6949855 := by exact prefixLift 6949855
  have htrace : WordTrace (prefixWord ++ tailWord_6949855) baseStart_6949855 baseEnd_6949855 := by
    simpa [prefixWord, tailWord_6949855, baseEnd_6949855] using wordTrace_append hprefix tailTrace_6949855
  have hstable : (prefixWord ++ tailWord_6949855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949855).length < 2 ^ (prefixWord ++ tailWord_6949855).sum := by decide
  have hdescent : baseEnd_6949855 < baseStart_6949855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949871 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_6949871 : Nat := 118140960795 + 6949871 * 2 ^ 59
def prefixEnd_6949871 : Nat := 4983230072969 + 3 ^ 40 * 6949871 * 2
def baseEnd_6949871 : Nat := 3568624309743483331450631

theorem tailTrace_6949871 : CollatzResearch.WordTrace tailWord_6949871 prefixEnd_6949871 3568624309743483331450631 := by
  unfold tailWord_6949871
  simp only [CollatzResearch.WordTrace]
  refine ⟨253482619804811785314513467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168988413203207856876342311 253482619804811785314513467)
  ·
    refine ⟨380223929707217677971770201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253482619804811785314513467 380223929707217677971770201)
    ·
      refine ⟨285167947280413258478827651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 380223929707217677971770201 285167947280413258478827651)
      ·
        refine ⟨427751920920619887718241477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 285167947280413258478827651 427751920920619887718241477)
        ·
          refine ⟨80203485172616228947170277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 427751920920619887718241477 80203485172616228947170277)
          ·
            refine ⟨15038153469865542927594427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 80203485172616228947170277 15038153469865542927594427)
            ·
              refine ⟨22557230204798314391391641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15038153469865542927594427 22557230204798314391391641)
              ·
                refine ⟨16917922653598735793543731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22557230204798314391391641 16917922653598735793543731)
                ·
                  refine ⟨25376883980398103690315597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16917922653598735793543731 25376883980398103690315597)
                  ·
                    refine ⟨9516331492649288883868349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 25376883980398103690315597 9516331492649288883868349)
                    ·
                      refine ⟨3568624309743483331450631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9516331492649288883868349 3568624309743483331450631)
                      ·
                        rfl

theorem cell23_6949871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_6949871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949871 prefixEnd_6949871 := by exact prefixLift 6949871
  have htrace : WordTrace (prefixWord ++ tailWord_6949871) baseStart_6949871 baseEnd_6949871 := by
    simpa [prefixWord, tailWord_6949871, baseEnd_6949871] using wordTrace_append hprefix tailTrace_6949871
  have hstable : (prefixWord ++ tailWord_6949871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949871).length < 2 ^ (prefixWord ++ tailWord_6949871).sum := by decide
  have hdescent : baseEnd_6949871 < baseStart_6949871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949889 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 1, 2, 2]
def baseStart_6949889 : Nat := 118140960795 + 6949889 * 2 ^ 59
def prefixEnd_6949889 : Nat := 4983230072969 + 3 ^ 40 * 6949889 * 2
def baseEnd_6949889 : Nat := 3568633552395264261025549

theorem tailTrace_6949889 : CollatzResearch.WordTrace tailWord_6949889 prefixEnd_6949889 3568633552395264261025549 := by
  unfold tailWord_6949889
  simp only [CollatzResearch.WordTrace]
  refine ⟨253483276318746574388668721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168988850879164382925779147 253483276318746574388668721)
  ·
    refine ⟨190112457239059930791501541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253483276318746574388668721 190112457239059930791501541)
    ·
      refine ⟨35646085732323737023406539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190112457239059930791501541 35646085732323737023406539)
      ·
        refine ⟨53469128598485605535109809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35646085732323737023406539 53469128598485605535109809)
        ·
          refine ⟨40101846448864204151332357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 53469128598485605535109809 40101846448864204151332357)
          ·
            refine ⟨7519096209162038278374817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 40101846448864204151332357 7519096209162038278374817)
            ·
              refine ⟨5639322156871528708781113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7519096209162038278374817 5639322156871528708781113)
              ·
                refine ⟨4229491617653646531585835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5639322156871528708781113 4229491617653646531585835)
                ·
                  refine ⟨6344237426480469797378753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229491617653646531585835 6344237426480469797378753)
                  ·
                    refine ⟨4758178069860352348034065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6344237426480469797378753 4758178069860352348034065)
                    ·
                      refine ⟨3568633552395264261025549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758178069860352348034065 3568633552395264261025549)
                      ·
                        rfl

theorem cell23_6949889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 1, 2, 2].length) (baseStart_6949889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949889 prefixEnd_6949889 := by exact prefixLift 6949889
  have htrace : WordTrace (prefixWord ++ tailWord_6949889) baseStart_6949889 baseEnd_6949889 := by
    simpa [prefixWord, tailWord_6949889, baseEnd_6949889] using wordTrace_append hprefix tailTrace_6949889
  have hstable : (prefixWord ++ tailWord_6949889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949889).length < 2 ^ (prefixWord ++ tailWord_6949889).sum := by decide
  have hdescent : baseEnd_6949889 < baseStart_6949889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949898 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2]
def baseStart_6949898 : Nat := 118140960795 + 6949898 * 2 ^ 59
def prefixEnd_6949898 : Nat := 4983230072969 + 3 ^ 40 * 6949898 * 2
def baseEnd_6949898 : Nat := 3568638173721154725813007

theorem tailTrace_6949898 : CollatzResearch.WordTrace tailWord_6949898 prefixEnd_6949898 3568638173721154725813007 := by
  unfold tailWord_6949898
  simp only [CollatzResearch.WordTrace]
  refine ⟨63370901143928492231436587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 168989069717142645950497565 63370901143928492231436587)
  ·
    refine ⟨95056351715892738347154881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 63370901143928492231436587 95056351715892738347154881)
    ·
      refine ⟨71292263786919553760366161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 95056351715892738347154881 71292263786919553760366161)
      ·
        refine ⟨53469197840189665320274621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 71292263786919553760366161 53469197840189665320274621)
        ·
          refine ⟨20050949190071124495102983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 53469197840189665320274621 20050949190071124495102983)
          ·
            refine ⟨30076423785106686742654475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20050949190071124495102983 30076423785106686742654475)
            ·
              refine ⟨45114635677660030113981713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30076423785106686742654475 45114635677660030113981713)
              ·
                refine ⟨33835976758245022585486285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 45114635677660030113981713 33835976758245022585486285)
                ·
                  refine ⟨12688491284341883469557357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33835976758245022585486285 12688491284341883469557357)
                  ·
                    refine ⟨4758184231628206301084009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12688491284341883469557357 4758184231628206301084009)
                    ·
                      refine ⟨3568638173721154725813007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758184231628206301084009 3568638173721154725813007)
                      ·
                        rfl

theorem cell23_6949898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 3, 3, 2].length) (baseStart_6949898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949898 prefixEnd_6949898 := by exact prefixLift 6949898
  have htrace : WordTrace (prefixWord ++ tailWord_6949898) baseStart_6949898 baseEnd_6949898 := by
    simpa [prefixWord, tailWord_6949898, baseEnd_6949898] using wordTrace_append hprefix tailTrace_6949898
  have hstable : (prefixWord ++ tailWord_6949898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949898).length < 2 ^ (prefixWord ++ tailWord_6949898).sum := by decide
  have hdescent : baseEnd_6949898 < baseStart_6949898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949945 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 4, 2, 2]
def baseStart_6949945 : Nat := 118140960795 + 6949945 * 2 ^ 59
def prefixEnd_6949945 : Nat := 4983230072969 + 3 ^ 40 * 6949945 * 2
def baseEnd_6949945 : Nat := 3568662307311916041925291

theorem tailTrace_6949945 : CollatzResearch.WordTrace tailWord_6949945 prefixEnd_6949945 3568662307311916041925291 := by
  unfold tailWord_6949945
  simp only [CollatzResearch.WordTrace]
  refine ⟨253485318806543695952707289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168990212537695797301804859 253485318806543695952707289)
  ·
    refine ⟨190113989104907771964530467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253485318806543695952707289 190113989104907771964530467)
    ·
      refine ⟨285170983657361657946795701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 190113989104907771964530467 285170983657361657946795701)
      ·
        refine ⟨26734779717877655432512097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 285170983657361657946795701 26734779717877655432512097)
        ·
          refine ⟨20051084788408241574384073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26734779717877655432512097 20051084788408241574384073)
          ·
            refine ⟨15038313591306181180788055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20051084788408241574384073 15038313591306181180788055)
            ·
              refine ⟨22557470386959271771182083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15038313591306181180788055 22557470386959271771182083)
              ·
                refine ⟨33836205580438907656773125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22557470386959271771182083 33836205580438907656773125)
                ·
                  refine ⟨6344288546332295185644961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33836205580438907656773125 6344288546332295185644961)
                  ·
                    refine ⟨4758216409749221389233721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6344288546332295185644961 4758216409749221389233721)
                    ·
                      refine ⟨3568662307311916041925291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758216409749221389233721 3568662307311916041925291)
                      ·
                        rfl

theorem cell23_6949945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 4, 2, 2].length) (baseStart_6949945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949945 prefixEnd_6949945 := by exact prefixLift 6949945
  have htrace : WordTrace (prefixWord ++ tailWord_6949945) baseStart_6949945 baseEnd_6949945 := by
    simpa [prefixWord, tailWord_6949945, baseEnd_6949945] using wordTrace_append hprefix tailTrace_6949945
  have hstable : (prefixWord ++ tailWord_6949945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949945).length < 2 ^ (prefixWord ++ tailWord_6949945).sum := by decide
  have hdescent : baseEnd_6949945 < baseStart_6949945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949971 : List Nat := [1, 1, 1, 2, 1, 1, 2, 3, 4, 5, 2]
def baseStart_6949971 : Nat := 118140960795 + 6949971 * 2 ^ 59
def prefixEnd_6949971 : Nat := 4983230072969 + 3 ^ 40 * 6949971 * 2
def baseEnd_6949971 : Nat := 3568675657808932940200171

theorem tailTrace_6949971 : CollatzResearch.WordTrace tailWord_6949971 prefixEnd_6949971 3568675657808932940200171 := by
  unfold tailWord_6949971
  simp only [CollatzResearch.WordTrace]
  refine ⟨253486267104449502393153767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168990844736299668262102511 253486267104449502393153767)
  ·
    refine ⟨380229400656674253589730651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253486267104449502393153767 380229400656674253589730651)
    ·
      refine ⟨570344100985011380384595977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380229400656674253589730651 570344100985011380384595977)
      ·
        refine ⟨427758075738758535288446983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 570344100985011380384595977 427758075738758535288446983)
        ·
          refine ⟨641637113608137802932670475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 427758075738758535288446983 641637113608137802932670475)
          ·
            refine ⟨962455670412206704399005713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 641637113608137802932670475 962455670412206704399005713)
            ·
              refine ⟨721841752809155028299254285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 962455670412206704399005713 721841752809155028299254285)
              ·
                refine ⟨270690657303433135612220357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 721841752809155028299254285 270690657303433135612220357)
                ·
                  refine ⟨50754498244393712927291317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270690657303433135612220357 50754498244393712927291317)
                  ·
                    refine ⟨4758234210411910586933561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 50754498244393712927291317 4758234210411910586933561)
                    ·
                      refine ⟨3568675657808932940200171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4758234210411910586933561 3568675657808932940200171)
                      ·
                        rfl

theorem cell23_6949971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4, 5, 2].length) (baseStart_6949971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949971 prefixEnd_6949971 := by exact prefixLift 6949971
  have htrace : WordTrace (prefixWord ++ tailWord_6949971) baseStart_6949971 baseEnd_6949971 := by
    simpa [prefixWord, tailWord_6949971, baseEnd_6949971] using wordTrace_append hprefix tailTrace_6949971
  have hstable : (prefixWord ++ tailWord_6949971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949971).length < 2 ^ (prefixWord ++ tailWord_6949971).sum := by decide
  have hdescent : baseEnd_6949971 < baseStart_6949971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6949998 : List Nat := [4, 1, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_6949998 : Nat := 118140960795 + 6949998 * 2 ^ 59
def prefixEnd_6949998 : Nat := 4983230072969 + 3 ^ 40 * 6949998 * 2
def baseEnd_6949998 : Nat := 1189563173928868111520849

theorem tailTrace_6949998 : CollatzResearch.WordTrace tailWord_6949998 prefixEnd_6949998 1189563173928868111520849 := by
  unfold tailWord_6949998
  simp only [CollatzResearch.WordTrace]
  refine ⟨31685906484418960750548331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168991501250234457336257765 31685906484418960750548331)
  ·
    refine ⟨47528859726628441125822497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31685906484418960750548331 47528859726628441125822497)
    ·
      refine ⟨35646644794971330844366873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47528859726628441125822497 35646644794971330844366873)
      ·
        refine ⟨26734983596228498133275155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35646644794971330844366873 26734983596228498133275155)
        ·
          refine ⟨40102475394342747199912733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26734983596228498133275155 40102475394342747199912733)
          ·
            refine ⟨15038428272878530199967275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40102475394342747199912733 15038428272878530199967275)
            ·
              refine ⟨22557642409317795299950913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15038428272878530199967275 22557642409317795299950913)
              ·
                refine ⟨16918231806988346474963185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22557642409317795299950913 16918231806988346474963185)
                ·
                  refine ⟨12688673855241259856222389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16918231806988346474963185 12688673855241259856222389)
                  ·
                    refine ⟨1189563173928868111520849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12688673855241259856222389 1189563173928868111520849)
                    ·
                      rfl

theorem cell23_6949998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_6949998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6949998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6949998 prefixEnd_6949998 := by exact prefixLift 6949998
  have htrace : WordTrace (prefixWord ++ tailWord_6949998) baseStart_6949998 baseEnd_6949998 := by
    simpa [prefixWord, tailWord_6949998, baseEnd_6949998] using wordTrace_append hprefix tailTrace_6949998
  have hstable : (prefixWord ++ tailWord_6949998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6949998).length < 2 ^ (prefixWord ++ tailWord_6949998).sum := by decide
  have hdescent : baseEnd_6949998 < baseStart_6949998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6949998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950045 : List Nat := [1, 4, 2, 1, 1, 2, 2, 5, 1, 4]
def baseStart_6950045 : Nat := 118140960795 + 6950045 * 2 ^ 59
def prefixEnd_6950045 : Nat := 4983230072969 + 3 ^ 40 * 6950045 * 2
def baseEnd_6950045 : Nat := 1189571218459121883558277

theorem tailTrace_6950045 : CollatzResearch.WordTrace tailWord_6950045 prefixEnd_6950045 1189571218459121883558277 := by
  unfold tailWord_6950045
  simp only [CollatzResearch.WordTrace]
  refine ⟨253488966106181413031347589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168992644070787608687565059 253488966106181413031347589)
  ·
    refine ⟨47529181144909014943377673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 253488966106181413031347589 47529181144909014943377673)
    ·
      refine ⟨35646885858681761207533255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47529181144909014943377673 35646885858681761207533255)
      ·
        refine ⟨53470328788022641811299883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35646885858681761207533255 53470328788022641811299883)
        ·
          refine ⟨80205493182033962716949825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53470328788022641811299883 80205493182033962716949825)
          ·
            refine ⟨60154119886525472037712369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 80205493182033962716949825 60154119886525472037712369)
            ·
              refine ⟨45115589914894104028284277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 60154119886525472037712369 45115589914894104028284277)
              ·
                refine ⟨4229586554521322252651651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 45115589914894104028284277 4229586554521322252651651)
                ·
                  refine ⟨6344379831781983378977477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4229586554521322252651651 6344379831781983378977477)
                  ·
                    refine ⟨1189571218459121883558277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6344379831781983378977477 1189571218459121883558277)
                    ·
                      rfl

theorem cell23_6950045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_6950045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950045 prefixEnd_6950045 := by exact prefixLift 6950045
  have htrace : WordTrace (prefixWord ++ tailWord_6950045) baseStart_6950045 baseEnd_6950045 := by
    simpa [prefixWord, tailWord_6950045, baseEnd_6950045] using wordTrace_append hprefix tailTrace_6950045
  have hstable : (prefixWord ++ tailWord_6950045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950045).length < 2 ^ (prefixWord ++ tailWord_6950045).sum := by decide
  have hdescent : baseEnd_6950045 < baseStart_6950045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950055 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_6950055 : Nat := 118140960795 + 6950055 * 2 ^ 59
def prefixEnd_6950055 : Nat := 4983230072969 + 3 ^ 40 * 6950055 * 2
def baseEnd_6950055 : Nat := 3568718790183910611549785

theorem tailTrace_6950055 : CollatzResearch.WordTrace tailWord_6950055 prefixEnd_6950055 3568718790183910611549785 := by
  unfold tailWord_6950055
  simp only [CollatzResearch.WordTrace]
  refine ⟨253489330836145184739211619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168992887224096789826141079 253489330836145184739211619)
  ·
    refine ⟨380233996254217777108817429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253489330836145184739211619 380233996254217777108817429)
    ·
      refine ⟨17823468574416458301975817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 380233996254217777108817429 17823468574416458301975817)
      ·
        refine ⟨13367601430812343726481863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17823468574416458301975817 13367601430812343726481863)
        ·
          refine ⟨20051402146218515589722795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13367601430812343726481863 20051402146218515589722795)
          ·
            refine ⟨30077103219327773384584193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20051402146218515589722795 30077103219327773384584193)
            ·
              refine ⟨22557827414495830038438145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30077103219327773384584193 22557827414495830038438145)
              ·
                refine ⟨16918370560871872528828609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22557827414495830038438145 16918370560871872528828609)
                ·
                  refine ⟨12688777920653904396621457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16918370560871872528828609 12688777920653904396621457)
                  ·
                    refine ⟨9516583440490428297466093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12688777920653904396621457 9516583440490428297466093)
                    ·
                      refine ⟨3568718790183910611549785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9516583440490428297466093 3568718790183910611549785)
                      ·
                        rfl

theorem cell23_6950055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_6950055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950055 prefixEnd_6950055 := by exact prefixLift 6950055
  have htrace : WordTrace (prefixWord ++ tailWord_6950055) baseStart_6950055 baseEnd_6950055 := by
    simpa [prefixWord, tailWord_6950055, baseEnd_6950055] using wordTrace_append hprefix tailTrace_6950055
  have hstable : (prefixWord ++ tailWord_6950055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950055).length < 2 ^ (prefixWord ++ tailWord_6950055).sum := by decide
  have hdescent : baseEnd_6950055 < baseStart_6950055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950071 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 5, 5]
def baseStart_6950071 : Nat := 118140960795 + 6950071 * 2 ^ 59
def prefixEnd_6950071 : Nat := 4983230072969 + 3 ^ 40 * 6950071 * 2
def baseEnd_6950071 : Nat := 1189575668624794182983237

theorem tailTrace_6950071 : CollatzResearch.WordTrace tailWord_6950071 prefixEnd_6950071 1189575668624794182983237 := by
  unfold tailWord_6950071
  simp only [CollatzResearch.WordTrace]
  refine ⟨253489914404087219471794067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168993276269391479647862711 253489914404087219471794067)
  ·
    refine ⟨380234871606130829207691101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253489914404087219471794067 380234871606130829207691101)
    ·
      refine ⟨142588076852299060952884163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 380234871606130829207691101 142588076852299060952884163)
      ·
        refine ⟨213882115278448591429326245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 142588076852299060952884163 213882115278448591429326245)
        ·
          refine ⟨40102896614709110892998671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 213882115278448591429326245 40102896614709110892998671)
          ·
            refine ⟨60154344922063666339498007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 40102896614709110892998671 60154344922063666339498007)
            ·
              refine ⟨90231517383095499509247011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 60154344922063666339498007 90231517383095499509247011)
              ·
                refine ⟨135347276074643249263870517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 90231517383095499509247011 135347276074643249263870517)
                ·
                  refine ⟨12688807131997804618487861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 135347276074643249263870517 12688807131997804618487861)
                  ·
                    refine ⟨1189575668624794182983237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12688807131997804618487861 1189575668624794182983237)
                    ·
                      rfl

theorem cell23_6950071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_6950071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950071 prefixEnd_6950071 := by exact prefixLift 6950071
  have htrace : WordTrace (prefixWord ++ tailWord_6950071) baseStart_6950071 baseEnd_6950071 := by
    simpa [prefixWord, tailWord_6950071, baseEnd_6950071] using wordTrace_append hprefix tailTrace_6950071
  have hstable : (prefixWord ++ tailWord_6950071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950071).length < 2 ^ (prefixWord ++ tailWord_6950071).sum := by decide
  have hdescent : baseEnd_6950071 < baseStart_6950071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950086 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6950086 : Nat := 118140960795 + 6950086 * 2 ^ 59
def prefixEnd_6950086 : Nat := 4983230072969 + 3 ^ 40 * 6950086 * 2
def baseEnd_6950086 : Nat := 3568734708084199990262143

theorem tailTrace_6950086 : CollatzResearch.WordTrace tailWord_6950086 prefixEnd_6950086 3568734708084199990262143 := by
  unfold tailWord_6950086
  simp only [CollatzResearch.WordTrace]
  refine ⟨7921576921844777407299691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 168993640999355251355726741 7921576921844777407299691)
  ·
    refine ⟨11882365382767166110949537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7921576921844777407299691 11882365382767166110949537)
    ·
      refine ⟨8911774037075374583212153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11882365382767166110949537 8911774037075374583212153)
      ·
        refine ⟨6683830527806530937409115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8911774037075374583212153 6683830527806530937409115)
        ·
          refine ⟨10025745791709796406113673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6683830527806530937409115 10025745791709796406113673)
          ·
            refine ⟨7519309343782347304585255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10025745791709796406113673 7519309343782347304585255)
            ·
              refine ⟨11278964015673520956877883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7519309343782347304585255 11278964015673520956877883)
              ·
                refine ⟨16918446023510281435316825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11278964015673520956877883 16918446023510281435316825)
                ·
                  refine ⟨12688834517632711076487619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16918446023510281435316825 12688834517632711076487619)
                  ·
                    refine ⟨19033251776449066614731429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12688834517632711076487619 19033251776449066614731429)
                    ·
                      refine ⟨3568734708084199990262143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19033251776449066614731429 3568734708084199990262143)
                      ·
                        rfl

theorem cell23_6950086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6950086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950086 prefixEnd_6950086 := by exact prefixLift 6950086
  have htrace : WordTrace (prefixWord ++ tailWord_6950086) baseStart_6950086 baseEnd_6950086 := by
    simpa [prefixWord, tailWord_6950086, baseEnd_6950086] using wordTrace_append hprefix tailTrace_6950086
  have hstable : (prefixWord ++ tailWord_6950086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950086).length < 2 ^ (prefixWord ++ tailWord_6950086).sum := by decide
  have hdescent : baseEnd_6950086 < baseStart_6950086 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950142 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6950142 : Nat := 118140960795 + 6950142 * 2 ^ 59
def prefixEnd_6950142 : Nat := 4983230072969 + 3 ^ 40 * 6950142 * 2
def baseEnd_6950142 : Nat := 3568763463000851771161885

theorem tailTrace_6950142 : CollatzResearch.WordTrace tailWord_6950142 prefixEnd_6950142 3568763463000851771161885 := by
  unfold tailWord_6950142
  simp only [CollatzResearch.WordTrace]
  refine ⟨31686562998353749824703585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 168995002657886665731752453 31686562998353749824703585)
  ·
    refine ⟨23764922248765312368527689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31686562998353749824703585 23764922248765312368527689)
    ·
      refine ⟨17823691686573984276395767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23764922248765312368527689 17823691686573984276395767)
      ·
        refine ⟨26735537529860976414593651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17823691686573984276395767 26735537529860976414593651)
        ·
          refine ⟨40103306294791464621890477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26735537529860976414593651 40103306294791464621890477)
          ·
            refine ⟨15038739860546799233208929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40103306294791464621890477 15038739860546799233208929)
            ·
              refine ⟨11279054895410099424906697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15038739860546799233208929 11279054895410099424906697)
              ·
                refine ⟨8459291171557574568680023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11279054895410099424906697 8459291171557574568680023)
                ·
                  refine ⟨12688936757336361853020035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459291171557574568680023 12688936757336361853020035)
                  ·
                    refine ⟨19033405136004542779530053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12688936757336361853020035 19033405136004542779530053)
                    ·
                      refine ⟨3568763463000851771161885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19033405136004542779530053 3568763463000851771161885)
                      ·
                        rfl

theorem cell23_6950142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6950142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950142 prefixEnd_6950142 := by exact prefixLift 6950142
  have htrace : WordTrace (prefixWord ++ tailWord_6950142) baseStart_6950142 baseEnd_6950142 := by
    simpa [prefixWord, tailWord_6950142, baseEnd_6950142] using wordTrace_append hprefix tailTrace_6950142
  have hstable : (prefixWord ++ tailWord_6950142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950142).length < 2 ^ (prefixWord ++ tailWord_6950142).sum := by decide
  have hdescent : baseEnd_6950142 < baseStart_6950142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950145 : List Nat := [1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 3]
def baseStart_6950145 : Nat := 118140960795 + 6950145 * 2 ^ 59
def prefixEnd_6950145 : Nat := 4983230072969 + 3 ^ 40 * 6950145 * 2
def baseEnd_6950145 : Nat := 3568765003442815259424371

theorem tailTrace_6950145 : CollatzResearch.WordTrace tailWord_6950145 prefixEnd_6950145 3568765003442815259424371 := by
  unfold tailWord_6950145
  simp only [CollatzResearch.WordTrace]
  refine ⟨253492613405819130109987889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168995075603879420073325259 253492613405819130109987889)
  ·
    refine ⟨190119460054364347582490917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 253492613405819130109987889 190119460054364347582490917)
    ·
      refine ⟨35647398760193315171717047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 190119460054364347582490917 35647398760193315171717047)
      ·
        refine ⟨53471098140289972757575571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35647398760193315171717047 53471098140289972757575571)
        ·
          refine ⟨80206647210434959136363357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 53471098140289972757575571 80206647210434959136363357)
          ·
            refine ⟨30077492703913109676136259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 80206647210434959136363357 30077492703913109676136259)
            ·
              refine ⟨45116239055869664514204389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30077492703913109676136259 45116239055869664514204389)
              ·
                refine ⟨8459294822975562096413323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 45116239055869664514204389 8459294822975562096413323)
                ·
                  refine ⟨12688942234463343144619985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8459294822975562096413323 12688942234463343144619985)
                  ·
                    refine ⟨9516706675847507358464989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12688942234463343144619985 9516706675847507358464989)
                    ·
                      refine ⟨3568765003442815259424371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9516706675847507358464989 3568765003442815259424371)
                      ·
                        rfl

theorem cell23_6950145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 2, 3].length) (baseStart_6950145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950145 prefixEnd_6950145 := by exact prefixLift 6950145
  have htrace : WordTrace (prefixWord ++ tailWord_6950145) baseStart_6950145 baseEnd_6950145 := by
    simpa [prefixWord, tailWord_6950145, baseEnd_6950145] using wordTrace_append hprefix tailTrace_6950145
  have hstable : (prefixWord ++ tailWord_6950145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950145).length < 2 ^ (prefixWord ++ tailWord_6950145).sum := by decide
  have hdescent : baseEnd_6950145 < baseStart_6950145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950148 : List Nat := [2, 3, 2, 2, 2, 2, 1, 9]
def baseStart_6950148 : Nat := 118140960795 + 6950148 * 2 ^ 59
def prefixEnd_6950148 : Nat := 4983230072969 + 3 ^ 40 * 6950148 * 2
def baseEnd_6950148 : Nat := 132176538662399212877291

theorem tailTrace_6950148 : CollatzResearch.WordTrace tailWord_6950148 prefixEnd_6950148 132176538662399212877291 := by
  unfold tailWord_6950148
  simp only [CollatzResearch.WordTrace]
  refine ⟨126746361412404130811173549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 168995148549872174414898065 126746361412404130811173549)
  ·
    refine ⟨47529885529651549054190081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 126746361412404130811173549 47529885529651549054190081)
    ·
      refine ⟨35647414147238661790642561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47529885529651549054190081 35647414147238661790642561)
      ·
        refine ⟨26735560610428996342981921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35647414147238661790642561 26735560610428996342981921)
        ·
          refine ⟨20051670457821747257236441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26735560610428996342981921 20051670457821747257236441)
          ·
            refine ⟨15038752843366310442927331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20051670457821747257236441 15038752843366310442927331)
            ·
              refine ⟨22558129265049465664390997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15038752843366310442927331 22558129265049465664390997)
              ·
                refine ⟨132176538662399212877291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22558129265049465664390997 132176538662399212877291)
                ·
                  rfl

theorem cell23_6950148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 9].length) (baseStart_6950148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950148 prefixEnd_6950148 := by exact prefixLift 6950148
  have htrace : WordTrace (prefixWord ++ tailWord_6950148) baseStart_6950148 baseEnd_6950148 := by
    simpa [prefixWord, tailWord_6950148, baseEnd_6950148] using wordTrace_append hprefix tailTrace_6950148
  have hstable : (prefixWord ++ tailWord_6950148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950148).length < 2 ^ (prefixWord ++ tailWord_6950148).sum := by decide
  have hdescent : baseEnd_6950148 < baseStart_6950148 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6950171 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_6950171 : Nat := 118140960795 + 6950171 * 2 ^ 59
def prefixEnd_6950171 : Nat := 4983230072969 + 3 ^ 40 * 6950171 * 2
def baseEnd_6950171 : Nat := 3568778353939832157699251

theorem tailTrace_6950171 : CollatzResearch.WordTrace tailWord_6950171 prefixEnd_6950171 3568778353939832157699251 := by
  unfold tailWord_6950171
  simp only [CollatzResearch.WordTrace]
  refine ⟨253493561703724936550434367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 168995707802483291033622911 253493561703724936550434367)
  ·
    refine ⟨380240342555587404825651551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 253493561703724936550434367 380240342555587404825651551)
    ·
      refine ⟨570360513833381107238477327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 380240342555587404825651551 570360513833381107238477327)
      ·
        refine ⟨855540770750071660857715991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 570360513833381107238477327 855540770750071660857715991)
        ·
          refine ⟨1283311156125107491286573987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 855540770750071660857715991 1283311156125107491286573987)
          ·
            refine ⟨1924966734187661236929860981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1283311156125107491286573987 1924966734187661236929860981)
            ·
              refine ⟨180465631330093240962174467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1924966734187661236929860981 180465631330093240962174467)
              ·
                refine ⟨270698446995139861443261701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 180465631330093240962174467 270698446995139861443261701)
                ·
                  refine ⟨50755958811588724020611569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 270698446995139861443261701 50755958811588724020611569)
                  ·
                    refine ⟨38066969108691543015458677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 50755958811588724020611569 38066969108691543015458677)
                    ·
                      refine ⟨3568778353939832157699251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 38066969108691543015458677 3568778353939832157699251)
                      ·
                        rfl

theorem cell23_6950171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_6950171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6950171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6950171 prefixEnd_6950171 := by exact prefixLift 6950171
  have htrace : WordTrace (prefixWord ++ tailWord_6950171) baseStart_6950171 baseEnd_6950171 := by
    simpa [prefixWord, tailWord_6950171, baseEnd_6950171] using wordTrace_append hprefix tailTrace_6950171
  have hstable : (prefixWord ++ tailWord_6950171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6950171).length < 2 ^ (prefixWord ++ tailWord_6950171).sum := by decide
  have hdescent : baseEnd_6950171 < baseStart_6950171 := by decide
  rcases family_descends (prefixWord ++ tailWord_6950171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
